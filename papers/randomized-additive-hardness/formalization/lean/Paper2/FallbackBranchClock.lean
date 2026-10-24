import Paper2.FallbackBranch
import Paper2.SourceItems

/-! U16 clock without the edge count (private, lane owner:a-uniform-clock-2): under
the admitted bounded-degree hypothesis `∀ u, SourceItems.degree edge u ≤ Δ`
(labelled incidences, parallel edges counted with multiplicity), `2e ≤ vΔ`, so
the complete fallback branch of `FallbackBranch.fallback_branch_run` halts within
a clock depending only on `v`, `Δ` and `k`. -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

namespace Paper2.FallbackBranchClock

open scoped BigOperators

theorem two_e_le {v e Δ : Nat} (edge : Fin e → Bool → Fin v)
    (hdeg : ∀ u, SourceItems.degree edge u ≤ Δ) : 2 * e ≤ v * Δ := by
  classical
  have hsum : ∑ u : Fin v, SourceItems.degree edge u = 2 * e := by
    have h := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (Fin e × Bool))) (t := (Finset.univ : Finset (Fin v)))
      (f := fun eb : Fin e × Bool => edge eb.1 eb.2) (fun _ _ => Finset.mem_univ _)
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at h
    rw [mul_comm 2 e, h]
    apply Finset.sum_congr rfl
    intro u _
    unfold SourceItems.degree
    congr 1
    ext x
    simp
  have hle : ∑ u : Fin v, SourceItems.degree edge u ≤ ∑ _u : Fin v, Δ :=
    Finset.sum_le_sum (fun u _ => hdeg u)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hle
  omega

/-- Complete fallback branch clock as a function of `v`, `Δ`, `k` only. -/
theorem fallback_branch_run_degree {v e Δ : Nat} (edge : Fin e → Bool → Fin v)
    (hdeg : ∀ u, SourceItems.degree edge u ≤ Δ) (k : Nat) :
    ∃ t ≤ (v + 2) + 4 ^ v * (10 * (v * Δ + 1) * (v + 1)) + 2 ^ (3 * k + 15),
      ∃ (ctl : FallbackBranch.ACtl) (q' : List Bool),
        (FallbackBranch.astep^[t]) (FallbackBranch.start edge k) =
          ⟨none, ctl, Sum.elim (FallbackBranch.SA (FallbackColourSearch.edgeList edge) q')
            (Sum.elim (Sum.elim (FallbackDimsPrinter.pbank k 0)
              (EthInapproximability.CurrentPaper.MatrixTableWriter.ready (fun _ => [])
                (FiniteFallbackOutput.rows k) (FiniteFallbackOutput.cols k) 0 0 0 0 []
                (EthInapproximability.CurrentPaper.MatrixMaterialization.rowMajor
                  (FiniteFallbackOutput.fallbackMatrix edge k))).contents) (fun _ => []))⟩ := by
  obtain ⟨t, ht, ctl, q', h⟩ := FallbackBranch.fallback_branch_run edge k
  have hc := FallbackBranch.fallback_branch_clock edge k
  have he : e ≤ v * Δ := by have := two_e_le edge hdeg; omega
  have hm : 10 * (e + 1) * (v + 1) ≤ 10 * (v * Δ + 1) * (v + 1) := by
    apply Nat.mul_le_mul_right; omega
  have hm2 := Nat.mul_le_mul_left (4 ^ v) hm
  exact ⟨t, by omega, ctl, q', h⟩

#print axioms two_e_le
#print axioms fallback_branch_run_degree

end Paper2.FallbackBranchClock
