import Paper2.CodeFullRepeat
import Mathlib.Tactic

/-! A source-defined sequence of accepted draws is realized by repeated
execution of the same encoded fixed controller. The path constructors state
only source states and capped-tape/sample facts, never a prepared machine
configuration or an already materialized physical run. -/

namespace Paper2.CodeFullRepeatPath

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.GeneratorPositive Paper2.GeneratorStateSize

noncomputable section

inductive Accepted (root : Code) (B R : Nat) :
    State → List Bool → State → List Bool → Prop where
  | ticket (s : State) (hp : PositiveState s) (ht : Trace root s)
      (D : Nat) (hD : 0 < D) (cs : List Code) (out : List Bool)
      (hstate : GeneratorCode.normalize s =
        ⟨.ticket D::cs,out.reverse⟩)
      (N : Nat) (hB : Nat.clog 2 D ≤ B)
      (tape : CappedSampler.Adaptive.Tape B R (N+1))
      (q : Fin D)
      (hq : CappedSampler.runWideBits D B R hB tape.1 = some q) :
      Accepted root B R s
        (RecursiveSamplingTape.writeTape B R (N+1) tape).val
        (GeneratorCode.advance ⟨.ticket D::cs,out.reverse⟩ q.val)
        (RecursiveSamplingTape.writeTape B R N tape.2).val
  | bit (s : State) (hp : PositiveState s) (ht : Trace root s)
      (cs : List Code) (out : List Bool)
      (hstate : GeneratorCode.normalize s = ⟨.bit::cs,out.reverse⟩)
      (N : Nat) (hB : Nat.clog 2 2 ≤ B)
      (tape : CappedSampler.Adaptive.Tape B R (N+1))
      (q : Fin 2)
      (hq : CappedSampler.runWideBits 2 B R hB tape.1 = some q) :
      Accepted root B R s
        (RecursiveSamplingTape.writeTape B R (N+1) tape).val
        (GeneratorCode.advance ⟨.bit::cs,out.reverse⟩ q.val)
        (RecursiveSamplingTape.writeTape B R N tape.2).val
  | branch (s : State) (hp : PositiveState s) (ht : Trace root s)
      (D a b : Nat) (hD : 0 < D) (f g h : Code)
      (cs : List Code) (out : List Bool)
      (hstate : GeneratorCode.normalize s =
        ⟨.branch3 D a b f g h::cs,out.reverse⟩)
      (N : Nat) (hB : Nat.clog 2 D ≤ B)
      (tape : CappedSampler.Adaptive.Tape B R (N+1))
      (q : Fin D)
      (hq : CappedSampler.runWideBits D B R hB tape.1 = some q) :
      Accepted root B R s
        (RecursiveSamplingTape.writeTape B R (N+1) tape).val
        (GeneratorCode.advance
          ⟨.branch3 D a b f g h::cs,out.reverse⟩ q.val)
        (RecursiveSamplingTape.writeTape B R N tape.2).val

theorem accepted_run {root : Code} {B R : Nat}
    {s s' : State} {tape tape' : List Bool}
    (h : Accepted root B R s tape s' tape') :
    ∃ u, CodeFullRepeat.run u (CodeFullRepeat.start s tape B R) =
      CodeFullRepeat.start s' tape' B R := by
  cases h with
  | ticket hp ht D hD cs out hstate N hB tape q hq =>
      exact CodeFullRepeat.ticket_reenters root _ hp ht
        D hD cs out hstate B R N hB tape q hq
  | bit hp ht cs out hstate N hB tape q hq =>
      exact CodeFullRepeat.bit_reenters root _ hp ht
        cs out hstate B R N hB tape q hq
  | branch hp ht D a b hD f g h cs out hstate N hB tape q hq =>
      exact CodeFullRepeat.branch_reenters root _ hp ht
        D a b hD f g h cs out hstate B R N hB tape q hq

inductive Path (root : Code) (B R : Nat) :
    State → List Bool → State → List Bool → Type where
  | refl (s : State) (tape : List Bool) : Path root B R s tape s tape
  | cons {s mid last : State} {tape tapeMid tapeLast : List Bool}
      (head : Accepted root B R s tape mid tapeMid)
      (tail : Path root B R mid tapeMid last tapeLast) :
      Path root B R s tape last tapeLast

def Path.length {root : Code} {B R : Nat}
    {s last : State} {tape tapeLast : List Bool}
    (h : Path root B R s tape last tapeLast) : Nat :=
  match h with
  | .refl _ _ => 0
  | .cons _ tail => tail.length + 1

private theorem run_add (a b : Nat) (c : CodeFullRepeat.Config) :
    CodeFullRepeat.run (a+b) c =
      CodeFullRepeat.run b (CodeFullRepeat.run a c) := by
  change ((advance CodeFullRepeat.program)^[a+b]) c =
    ((advance CodeFullRepeat.program)^[b])
      (((advance CodeFullRepeat.program)^[a]) c)
  rw [Nat.add_comm a b,Function.iterate_add_apply]

theorem path_run {root : Code} {B R : Nat}
    {s last : State} {tape tapeLast : List Bool}
    (h : Path root B R s tape last tapeLast) :
    ∃ u, CodeFullRepeat.run u (CodeFullRepeat.start s tape B R) =
      CodeFullRepeat.start last tapeLast B R := by
  induction h with
  | refl s tape =>
      exact ⟨0,rfl⟩
  | cons head tail ih =>
      obtain ⟨a,ha⟩ := accepted_run head
      obtain ⟨b,hb⟩ := ih
      refine ⟨a+b,?_⟩
      rw [run_add a b,ha,hb]

#print axioms accepted_run
#print axioms path_run

end
end Paper2.CodeFullRepeatPath
