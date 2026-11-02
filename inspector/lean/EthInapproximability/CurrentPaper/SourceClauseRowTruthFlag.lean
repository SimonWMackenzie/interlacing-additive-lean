import EthInapproximability.CurrentPaper.SourceClauseRowTruthBranch

/-! The selected source truth bit is written to a physical dispatch stack. -/

namespace EthInapproximability.CurrentPaper.SourceClauseRowTruthFlag

open Turing Turing.TM2.Stmt BitMachineEncoding

abbrev Stack (q : ℕ) := SourceClauseRowTruthBranch.Stack q
abbrev Label (N : ℕ) := SourceClauseRowTruthBranch.Label N

def program {q N : ℕ} (k : Fin N) : Label N →
    TM2.Stmt (fun _ : Stack q => Bool) (Label N) (Option Bool)
  | .accept => push (.inr 1) (fun _ => true) halt
  | .reject => push (.inr 1) (fun _ => false) halt
  | l => SourceClauseRowTruthBranch.program k l

theorem marker_step {q N : ℕ} (k : Fin N)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (bits : List Bool) :
    advance (program k)
      (SourceClauseRowTruthBranch.state row (some .marker) none (true :: bits)) =
    SourceClauseRowTruthBranch.state row (some (.skip 0)) (some true) bits := by
  change advance (SourceClauseRowTruthBranch.program k)
      (SourceClauseRowTruthBranch.state row (some .marker) none (true :: bits)) = _
  exact SourceClauseRowTruthBranch.marker_step k row bits

theorem skip_step {q N : ℕ} (k : Fin N)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (i : Fin (N + 1)) (hi : i.val < k.val)
    (b : Bool) (bits : List Bool) (v : Option Bool) :
    advance (program k)
      (SourceClauseRowTruthBranch.state row (some (.skip i)) v (b :: bits)) =
    SourceClauseRowTruthBranch.state row
      (some (.skip ⟨i.val + 1, by omega⟩)) (some b) bits := by
  change advance (SourceClauseRowTruthBranch.program k)
      (SourceClauseRowTruthBranch.state row (some (.skip i)) v (b :: bits)) = _
  exact SourceClauseRowTruthBranch.skip_step k row i hi b bits v

theorem choice_step {q N : ℕ} (k : Fin N)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (b : Bool) (bits : List Bool) (v : Option Bool) :
    advance (program k)
      (SourceClauseRowTruthBranch.state row
        (some (.skip ⟨k.val, by omega⟩)) v (b :: bits)) =
    SourceClauseRowTruthBranch.state row
      (some (SourceClauseRowTruthBranch.choice b N)) (some b) bits := by
  change advance (SourceClauseRowTruthBranch.program k)
      (SourceClauseRowTruthBranch.state row
        (some (.skip ⟨k.val, by omega⟩)) v (b :: bits)) = _
  exact SourceClauseRowTruthBranch.choice_step k row b bits v

theorem skip_run {q N : ℕ} (k : Fin N)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (i : Fin (N + 1)) (pre suffix : List Bool)
    (hi : i.val + pre.length = k.val) (v : Option Bool) :
    ∃ v', ((advance (program k))^[pre.length])
      (SourceClauseRowTruthBranch.state row (some (.skip i)) v
        (pre ++ suffix)) =
      SourceClauseRowTruthBranch.state row
        (some (.skip ⟨k.val, by omega⟩)) v' suffix := by
  induction pre generalizing i v with
  | nil =>
      have he : i = ⟨k.val, by omega⟩ := Fin.ext (by simpa using hi)
      rw [he]
      exact ⟨v, by simp [SourceClauseRowTruthBranch.state]⟩
  | cons b bs ih =>
      have hlt : i.val < k.val := by
        simp only [List.length_cons] at hi
        omega
      let next : Fin (N + 1) := ⟨i.val + 1, by omega⟩
      have hn : next.val + bs.length = k.val := by
        simp only [next, Fin.val_mk]
        simp only [List.length_cons] at hi
        omega
      obtain ⟨v', hv'⟩ := ih next hn (some b)
      refine ⟨v', ?_⟩
      rw [List.length_cons, show bs.length + 1 = bs.length + 1 by rfl,
        Function.iterate_succ_apply]
      rw [List.cons_append, skip_step k row i hlt b (bs ++ suffix) v]
      exact hv'

theorem branch_run {q N : ℕ} (k : Fin N)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (pre suffix : List Bool) (b : Bool)
    (hlen : pre.length = k.val) :
    ((advance (program k))^[k.val + 2])
      (SourceClauseRowTruthBranch.state row (some .marker) none
        (true :: (pre ++ b :: suffix))) =
      SourceClauseRowTruthBranch.state row
        (some (SourceClauseRowTruthBranch.choice b N)) (some b) suffix := by
  obtain ⟨v, hv⟩ := skip_run k row (0 : Fin (N + 1)) pre (b :: suffix)
    (by simpa using hlen) (some true)
  rw [show k.val + 2 = (k.val + 1) + 1 by omega,
    Function.iterate_succ_apply, marker_step]
  rw [show k.val + 1 = pre.length + 1 by omega,
    Function.iterate_succ_apply']
  rw [hv, choice_step]

theorem typed_branch_run {q N : ℕ} (k : Fin N)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (table : Fin N → Bool)
    (h : row (.inr 2) = true :: List.ofFn table) :
    ((advance (program k))^[k.val + 2])
      (⟨some .marker, none,
        SourceClauseRowTruthCopy.finalBank row (true :: List.ofFn table)⟩ :
          TM2.Cfg (fun _ : Stack q => Bool) (Label N) (Option Bool)) =
      SourceClauseRowTruthBranch.state row
        (some (SourceClauseRowTruthBranch.choice (table k) N))
        (some (table k)) ((List.ofFn table).drop (k.val + 1)) := by
  rw [SourceClauseRowTruthBranch.copied_ready (N := N) row
    (List.ofFn table) h]
  have hpre : ((List.ofFn table).take k.val).length = k.val := by
    simp [List.length_take, show k.val ≤ (List.ofFn table).length by
      simp [k.isLt.le]]
  have ht := branch_run k row ((List.ofFn table).take k.val)
    ((List.ofFn table).drop (k.val + 1)) (table k) hpre
  simpa only [← SourceClauseRowTruthBranch.table_split table k] using ht

def flagged {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (b : Bool) (remaining : List Bool) : Stack q → List Bool :=
  Function.update (Sum.elim row ![remaining, []]) (.inr 1) [b]

theorem flag_step {q N : ℕ} (k : Fin N)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (b : Bool) (remaining : List Bool) :
    advance (program k)
      (SourceClauseRowTruthBranch.state row
        (some (SourceClauseRowTruthBranch.choice b N))
        (some b) remaining) =
      (⟨none, some b, flagged row b remaining⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) (Label N) (Option Bool)) := by
  cases b <;>
    simp only [SourceClauseRowTruthBranch.choice, if_false, if_true,
      program, SourceClauseRowTruthBranch.state, flagged,
      advance, TM2.step, TM2.stepAux] <;>
    simp only [Option.getD_some, Sum.elim_inr, Matrix.cons_val_one] <;>
    rfl

theorem typed_flag_run {q N : ℕ} (k : Fin N)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (table : Fin N → Bool)
    (h : row (.inr 2) = true :: List.ofFn table) :
    ((advance (program k))^[k.val + 3])
      (⟨some .marker, none,
        SourceClauseRowTruthCopy.finalBank row (true :: List.ofFn table)⟩ :
          TM2.Cfg (fun _ : Stack q => Bool) (Label N) (Option Bool)) =
      ⟨none, some (table k),
        flagged row (table k) ((List.ofFn table).drop (k.val + 1))⟩ := by
  rw [show k.val + 3 = k.val + 2 + 1 by omega,
    Function.iterate_succ_apply', typed_branch_run k row table h,
    flag_step]

end EthInapproximability.CurrentPaper.SourceClauseRowTruthFlag
