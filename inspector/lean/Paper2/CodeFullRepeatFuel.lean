import Paper2.CodeFullRepeatPublic
import Mathlib.Tactic

namespace Paper2.CodeFullRepeatFuel

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

open Turing
open EthInapproximability.CurrentPaper
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.GeneratorStateSize Paper2.GeneratorSize

noncomputable section

theorem normalize_weight_le (s : State) :
    weight (GeneratorCode.normalize s) ≤ weight s := by
  induction s using GeneratorCode.normalize.induct with
  | case1 s h => rw [GeneratorCode.normalize]; split <;> simp_all
  | case2 s t h ih =>
      rw [GeneratorCode.normalize]
      split
      · simp_all
      · rename_i t' ht
        have he : t' = t := Option.some.inj (ht.symm.trans h)
        subst t'
        exact ih.trans (Nat.le_of_lt (admin_weight_lt s t h))

theorem ticket_advance_weight_lt (D : Nat) (hD : 0 < D)
    (cs : List Code) (out : List Bool) (q : Fin D) :
    weight (GeneratorCode.advance ⟨.ticket D::cs,out⟩ q.val) <
      weight ⟨.ticket D::cs,out⟩ := by
  cases D with
  | zero => omega
  | succ d => simp [GeneratorCode.advance,weight,nodes]

theorem bit_advance_weight_lt (cs : List Code)
    (out : List Bool) (q : Fin 2) :
    weight (GeneratorCode.advance ⟨.bit::cs,out⟩ q.val) <
      weight ⟨.bit::cs,out⟩ := by
  simp [GeneratorCode.advance,weight,nodes]

theorem branch_advance_weight_lt (D a b : Nat) (hD : 0 < D)
    (f g h : Code) (cs : List Code) (out : List Bool) (q : Fin D) :
    weight (GeneratorCode.advance
      ⟨.branch3 D a b f g h::cs,out⟩ q.val) <
      weight ⟨.branch3 D a b f g h::cs,out⟩ := by
  cases D with
  | zero => omega
  | succ d =>
      have hf := nodes_pos f
      have hg := nodes_pos g
      have hh := nodes_pos h
      simp [GeneratorCode.advance,weight,nodes]
      split_ifs <;> omega

theorem accepted_weight_lt {root : Code} {B R : Nat}
    {s s' : State} {tape tape' : List Bool}
    (h : CodeFullRepeatPath.Accepted root B R s tape s' tape') :
    weight s' < weight s := by
  cases h with
  | ticket hp ht D hD cs out hstate N hB tape q hq =>
      exact (ticket_advance_weight_lt D hD cs out.reverse q).trans_le
        (by rw [← hstate]; exact normalize_weight_le _)
  | bit hp ht cs out hstate N hB tape q hq =>
      exact (bit_advance_weight_lt cs out.reverse q).trans_le
        (by rw [← hstate]; exact normalize_weight_le _)
  | branch hp ht D a b hD f g h cs out hstate N hB tape q hq =>
      exact (branch_advance_weight_lt D a b hD f g h cs out.reverse q).trans_le
        (by rw [← hstate]; exact normalize_weight_le _)

theorem path_length_le_weight {root : Code} {B R : Nat}
    {s last : State} {tape tapeLast : List Bool}
    (h : CodeFullRepeatPath.Path root B R s tape last tapeLast) :
    h.length ≤ weight s := by
  induction h with
  | refl s tape => simp [CodeFullRepeatPath.Path.length]
  | cons head tail ih =>
      have hw := accepted_weight_lt head
      simp only [CodeFullRepeatPath.Path.length]
      omega

theorem weight_le_potential (s : State) : weight s ≤ potential s := by
  have hsum : (s.todo.map nodes).sum ≤ codesSize s.todo := by
    induction s.todo with
    | nil => rfl
    | cons c cs ih =>
        simp only [List.map_cons,List.sum_cons,codesSize]
        have hn := nodes_le_codeSize c
        omega
  unfold weight potential
  omega

theorem path_length_le_root {root : Code} {B R : Nat}
    {s last : State} {tape tapeLast : List Bool}
    (ht : Trace root s)
    (h : CodeFullRepeatPath.Path root B R s tape last tapeLast) :
    h.length ≤ codeSize root := by
  exact (path_length_le_weight h).trans
    ((weight_le_potential s).trans (trace_potential_le root s ht))

theorem physical_path_root_clock {root : Code} {B R : Nat}
    {s last : State} {tape tapeLast : List Bool}
    (ht : Trace root s)
    (h : CodeFullRepeatPath.Path root B R s tape last tapeLast) :
    ∃ u ≤ codeSize root * CodeFullRepeatPublic.repeatStepCap root B R,
      CodeFullRepeat.run u (CodeFullRepeat.start s tape B R) =
        CodeFullRepeat.start last tapeLast B R := by
  obtain ⟨u,hu,hr⟩ := CodeFullRepeatPublic.path_run_public h
  refine ⟨u,?_,hr⟩
  have hl := path_length_le_root ht h
  exact hu.trans (Nat.mul_le_mul_right _ hl)

#print axioms accepted_weight_lt
#print axioms path_length_le_root
#print axioms physical_path_root_clock

end
end Paper2.CodeFullRepeatFuel
