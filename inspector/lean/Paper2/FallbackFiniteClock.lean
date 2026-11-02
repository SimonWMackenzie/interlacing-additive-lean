import Paper2.FallbackBranchT
import Paper2.FallbackBranchClock
import Paper2.PublicScheduleSourceSize

/-! The actual finite exceptional branch has one source-dependent constant
times `2^(3*k)` as its clock. The constant does not depend on the input graph
or on k. Public parsing and the encoded output header are not supplied here. -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

namespace Paper2.FallbackFiniteClock

open EthInapproximability.CurrentPaper
open CompletePublicScheduleScratch

def coefficient (threshold degree : Nat) : Nat :=
  threshold + 2 + 3 ^ threshold * (10 * (threshold * degree + 1) *
    (threshold + 1)) + 2 ^ 15

theorem clock_le (v e threshold degree k : Nat)
    (hv : v ≤ threshold) (he : e ≤ v * degree) :
    (v + 2) + 3 ^ v * (10 * (e + 1) * (v + 1)) + 2 ^ (3 * k + 15) ≤
      coefficient threshold degree * 2 ^ (3 * k) := by
  have he' : e ≤ threshold * degree :=
    he.trans (Nat.mul_le_mul_right degree hv)
  have hpow : 3 ^ v ≤ 3 ^ threshold :=
    Nat.pow_le_pow_right (by decide) hv
  have hprod : 10 * (e + 1) * (v + 1) ≤
      10 * (threshold * degree + 1) * (threshold + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 10 (Nat.add_le_add_right he' 1))
      (Nat.add_le_add_right hv 1)
  have hbase : (v + 2) + 3 ^ v * (10 * (e + 1) * (v + 1)) ≤
      threshold + 2 + 3 ^ threshold *
        (10 * (threshold * degree + 1) * (threshold + 1)) :=
    Nat.add_le_add (Nat.add_le_add_right hv 2) (Nat.mul_le_mul hpow hprod)
  have hone : 1 ≤ 2 ^ (3 * k) := Nat.one_le_pow (3 * k) 2 (by decide)
  have hscale := Nat.mul_le_mul_left
    (threshold + 2 + 3 ^ threshold *
      (10 * (threshold * degree + 1) * (threshold + 1))) hone
  simp only [Nat.mul_one] at hscale
  rw [Nat.pow_add]
  unfold coefficient
  nlinarith

/-- A literal whole-bank endpoint of the already fixed ternary program. -/
def RunsToTable {v e : Nat} (edge : Fin e → Bool → Fin v) (k t : Nat)
    (ctl : FallbackBranchT.ACtl) (q : List Bool) : Prop :=
  (FallbackBranchT.astep^[t]) (FallbackBranchT.start edge k) =
    ⟨none, ctl, Sum.elim (FallbackBranch.SA (FallbackColourSearch.edgeList edge) q)
      (Sum.elim (Sum.elim (FallbackDimsPrinter.pbank k 0)
        (MatrixTableWriter.ready (fun _ => [])
          (FiniteFallbackOutput.rows k) (FiniteFallbackOutput.cols k) 0 0 0 0 []
          (MatrixMaterialization.rowMajor
            (FiniteFallbackOutput.fallbackMatrix edge k))).contents) (fun _ => []))⟩

theorem bounded_input_run {v e threshold degree : Nat}
    (edge : Fin e → Bool → Fin v) (k : Nat)
    (hv : v ≤ threshold)
    (hdegree : ∀ u, SourceItems.degree edge u ≤ degree) :
    ∃ t ≤ coefficient threshold degree * 2 ^ (3 * k),
      ∃ (ctl : FallbackBranchT.ACtl) (q : List Bool),
        RunsToTable edge k t ctl q := by
  obtain ⟨t, ht, ctl, q, hrun⟩ := FallbackBranchT.fallback_branch_run_ternary edge k
  have hclock := FallbackBranchT.fallback_branch_ternary_clock edge k
  have he2 := FallbackBranchClock.two_e_le edge hdegree
  have he : e ≤ v * degree := by omega
  have hbound := clock_le v e threshold degree k hv he
  exact ⟨t, ht.trans (hclock.trans hbound), ctl, q, hrun⟩

/-- The fixed public cutoff makes the actual failed-schedule branch uniformly
single-exponential in the requested gap. No colouring or halting witness is
an input to the machine or a hypothesis of this theorem. -/
theorem failed_schedule_run {v e : Nat} [Nonempty (Fin v)]
    (edge : Fin e → Bool → Fin v) (degree : Nat) (gap : Rat)
    (hgap : 0 < gap) (hdegreepos : 0 < degree)
    (hincident : ∀ u, ∃ i b, edge i b = u)
    (hdegree : ∀ u, SourceItems.degree edge u ≤ degree)
    (hfail : ¬ Checks (V := Fin v) (E := Fin e)
      (Nat.clog 2 v) degree gap) (k : Nat) :
    ∃ t ≤ coefficient (sizeThreshold degree gap) degree * 2 ^ (3 * k),
      ∃ (ctl : FallbackBranchT.ACtl) (q : List Bool),
        RunsToTable edge k t ctl q := by
  have hv : v < sizeThreshold degree gap := by
    simpa only [Fintype.card_fin] using
      failure_below_size_threshold edge degree gap hgap hdegreepos
        hincident hdegree (by simpa only [Fintype.card_fin] using hfail)
  exact bounded_input_run edge k hv.le hdegree

#print axioms clock_le
#print axioms bounded_input_run
#print axioms failed_schedule_run

end Paper2.FallbackFiniteClock
