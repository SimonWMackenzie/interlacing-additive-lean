import Paper2.FallbackIdentityCell
import Paper2.CodeFallbackScheduledClock

/-! U16 printing piece (private): physical row-major printers for every
fallback output of frozen v12 D:107-110 at the announced dimensions
`FiniteFallbackOutput.rows k × cols k`: the zero table (three-colourable
graph, and the unused `k = 0` hard case), the one-row matrix `[0 1]` (`k = 1`)
and the `2^(k-1)` identity (`k ≥ 2`). Each is an actual fixed entry program
fed to the admitted `MatrixTableWriter.write_rowMajor`, with its clock. The
exhaustive colouring search and the branch that selects among these printers
are NOT part of this module. -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

namespace Paper2.FallbackOutputPrint

open Turing TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

abbrev Stack := MatrixTableWriter.CellStack 0
abbrev Control := Option Bool × Option Bool

/-- One-step cell for `[0 1]`: reads the column index (at most two units),
restores it, and writes `decide (y = 1)`. -/
def oneCell : Unit → TM2.Stmt (fun _ : Stack => Bool) Unit Control
  | () => pop (.inr 1) (fun s a => (a, s.2))
      (pop (.inr 1) (fun s b => (s.1, b))
        (branch (fun s => s.2.isSome)
          (push (.inr 1) (fun _ => true) (push (.inr 1) (fun _ => true)
            (push (.inr 2) (fun _ => false) halt)))
          (branch (fun s => s.1.isSome)
            (push (.inr 1) (fun _ => true) (push (.inr 2) (fun _ => true) halt))
            (push (.inr 2) (fun _ => false) halt))))

theorem cellCfg_eq {c : TM2.Cfg (fun _ : Stack => Bool) Unit Control}
    {l : Option Unit} {v : Control} {x y : Nat} {ans : List Bool}
    (hl : c.l = l) (hv : c.var = v)
    (hs : ∀ k, c.stk k =
      (MatrixTableWriter.cellCfg l v CodeTableFallback.emptyBank x y ans).stk k) :
    c = MatrixTableWriter.cellCfg l v CodeTableFallback.emptyBank x y ans := by
  cases c with
  | mk l' v' S =>
    simp only at hl hv
    subst hl hv
    have : S = (MatrixTableWriter.cellCfg l' v' CodeTableFallback.emptyBank x y ans).stk :=
      funext hs
    subst this
    rfl

theorem oneCell_run (x y : Nat) :
    ∃ v, ((advance oneCell)^[1])
        (MatrixTableWriter.cellCfg (some ()) ((none, none) : Control)
          CodeTableFallback.emptyBank x y []) =
      MatrixTableWriter.cellCfg none v CodeTableFallback.emptyBank x y
        [decide (y = 1)] := by
  rw [Function.iterate_one]
  rcases y with _ | _ | y
  · refine ⟨(none, none), cellCfg_eq rfl rfl ?_⟩
    intro k
    rcases k with k | k
    · exact k.elim0
    · fin_cases k <;> rfl
  · refine ⟨(some true, none), cellCfg_eq rfl rfl ?_⟩
    intro k
    rcases k with k | k
    · exact k.elim0
    · fin_cases k <;> rfl
  · refine ⟨(some true, some true), cellCfg_eq rfl rfl ?_⟩
    intro k
    rcases k with k | k
    · exact k.elim0
    · fin_cases k <;> rfl

theorem oneCell_entryRuns (r c : Nat) :
    MatrixTableWriter.EntryRuns oneCell () ((none, none) : Control)
      CodeTableFallback.emptyBank r c 1 (fun _ y => decide (y = 1)) := by
  intro x hx y hy
  obtain ⟨v, h⟩ := oneCell_run x y
  exact ⟨1, le_refl _, v, h⟩

/-- Physical print of `FiniteFallbackIdentity.oneRow` (`k = 1`). -/
theorem write_oneRow_table :
    ∃ t ≤ MatrixTableWriter.writerBound 1 2 1, ∃ v,
      MatrixTableWriter.run oneCell () ((none, none) : Control) t
        (MatrixTableWriter.cfg (some (.inr (.copy .rows)))
          (((none, none) : Control), none)
          (MatrixTableWriter.ready CodeTableFallback.emptyBank 1 2 0 0 0 0 [] [])) =
      MatrixTableWriter.cfg none v
        (MatrixTableWriter.ready CodeTableFallback.emptyBank 1 2 0 0 0 0 []
          (MatrixMaterialization.rowMajor FiniteFallbackIdentity.oneRow)) := by
  simpa using MatrixTableWriter.write_rowMajor oneCell () ((none, none) : Control)
    CodeTableFallback.emptyBank 1 2 1 (fun _ y => decide (y = 1))
    FiniteFallbackIdentity.oneRow
    (by intro x y; simp [FiniteFallbackIdentity.oneRow, Fin.ext_iff])
    (oneCell_entryRuns 1 2) []

theorem oneRow_print_clock : MatrixTableWriter.writerBound 1 2 1 = 27 := by
  decide

/-- The three-colourable output (and the `k = 0` hard case): the admitted
false-cell writer at the announced dimensions, with a `2^{O(k)}` clock. -/
theorem zero_print_clock_le (k : Nat) :
    MatrixTableWriter.writerBound (FiniteFallbackOutput.rows k)
      (FiniteFallbackOutput.cols k) 1 ≤ 20 * 4 ^ k := by
  have hr : FiniteFallbackOutput.rows k ≤ 2 ^ k := by
    rcases k with _ | _ | k
    · decide
    · decide
    · show 2 ^ (k + 1) ≤ 2 ^ (k + 2)
      exact pow_le_pow_right₀ (by decide) (by omega)
  have hc : FiniteFallbackOutput.cols k ≤ 2 ^ k := by
    rcases k with _ | _ | k
    · decide
    · decide
    · show 2 ^ (k + 1) ≤ 2 ^ (k + 2)
      exact pow_le_pow_right₀ (by decide) (by omega)
  have h := CodeFallbackScheduledClock.writerBound_le_dims _ _ (2 ^ k) hr hc
    Nat.one_le_two_pow
  have e : (2 ^ k) ^ 2 = 4 ^ k := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rwa [e] at h

/-- The identity output (`k = j + 2`) at the announced dimensions. -/
theorem identity_print_at (j : Nat) :
    ∃ t ≤ MatrixTableWriter.writerBound (FiniteFallbackOutput.rows (j + 2))
        (FiniteFallbackOutput.cols (j + 2)) (3 * 2 ^ (j + 1) + 3), ∃ v,
      MatrixTableWriter.run FallbackIdentityCell.eqCell FallbackIdentityCell.Label.move
        ((none, none, false) : FallbackIdentityCell.Control) t
        (MatrixTableWriter.cfg (some (.inr (.copy .rows)))
          (((none, none, false) : FallbackIdentityCell.Control), none)
          (MatrixTableWriter.ready FallbackIdentityCell.emptyBank
            (FiniteFallbackOutput.rows (j + 2)) (FiniteFallbackOutput.cols (j + 2))
            0 0 0 0 [] [])) =
      MatrixTableWriter.cfg none v
        (MatrixTableWriter.ready FallbackIdentityCell.emptyBank
          (FiniteFallbackOutput.rows (j + 2)) (FiniteFallbackOutput.cols (j + 2))
          0 0 0 0 []
          (MatrixMaterialization.rowMajor (FiniteFallbackOutput.hardMatrix (j + 2)))) :=
  FallbackIdentityCell.write_identity_table (2 ^ (j + 1))

#print axioms oneCell_run
#print axioms oneCell_entryRuns
#print axioms write_oneRow_table
#print axioms oneRow_print_clock
#print axioms zero_print_clock_le
#print axioms identity_print_at

end Paper2.FallbackOutputPrint
