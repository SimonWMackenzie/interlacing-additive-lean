import Paper2.YaoSelectorEvents
import Paper2.YaoSelectorEventsConcentration

/-!
# The simultaneous selector sampling event

Frozen v12 T29(i), Appendix B `yao:rectangle-event`.
Hoeffding is proved for the actual finite IID law in the imported local
concentration module; the product-set family and public sample count are
the concrete objects from `YaoSelectorEvents`.
-/

namespace Paper2.Yao

open scoped BigOperators

theorem selector_one_rectangle_failure_le (q H S lambda : ℕ) [NeZero H]
    (hS : 0 < S) (hlambda : 0 < lambda)
    (J : Fin q → Finset (Fin H)) :
    ((selectorLaw q H).iid (selectorSampleCount q H S lambda)).prob
      (fun C => selectorVolume J + 1 / (4 * (S : ℝ)) <
        selectorEmpirical (selectorSampleCount q H S lambda) C J) ≤
      Real.exp (-((q * H + lambda : ℕ) : ℝ)) := by
  classical
  have hs : (0 : ℝ) < S := Nat.cast_pos.mpr hS
  have hh := FiniteLaw.iid_empirical_sum_upper_tail (selectorLaw q H)
    (selectorRectangle J) (selectorSampleCount q H S lambda)
    (selectorSampleCount_positive q H S lambda hS hlambda)
    (1 / (4 * (S : ℝ))) (by positivity)
  rw [selector_rectangle_probability, selector_sample_exponent _ _ _ _ hS] at hh
  simpa only [selectorEmpirical, Finset.sum_boole] using hh

/-- Full selector half T29(i). Every product set is tested simultaneously,
so both its factors and any retained sample-label set may be chosen after
sampling. The sample count is exactly `8*S^2*(q*H+lambda)`. -/
theorem selector_explicit_counts_failure_le (q H S lambda : ℕ) [NeZero H]
    (hS : 0 < S) (hlambda : 0 < lambda) :
    ((selectorLaw q H).iid (selectorSampleCount q H S lambda)).prob
      (fun C => ¬ selectorGood q H S (selectorSampleCount q H S lambda) C) ≤
      (1 / 2 : ℝ) ^ lambda := by
  classical
  let N := selectorSampleCount q H S lambda
  let B := fun (J : Fin q → Finset (Fin H)) (C : Fin N → Fin q → Fin H) =>
    selectorVolume J + 1 / (4 * (S : ℝ)) < selectorEmpirical N C J
  have he : (fun C : Fin N → Fin q → Fin H => ¬ selectorGood q H S N C) =
      (fun C => ∃ J ∈ (Finset.univ : Finset (Fin q → Finset (Fin H))), B J C) := by
    funext C
    simp [selectorGood, B]
  change ((selectorLaw q H).iid N).prob
    (fun C => ¬ selectorGood q H S N C) ≤ _
  rw [he]
  calc
    _ ≤ ∑ J ∈ (Finset.univ : Finset (Fin q → Finset (Fin H))),
        ((selectorLaw q H).iid N).prob (B J) := FiniteLaw.prob_exists_le_sum _ _ _
    _ ≤ ∑ _J ∈ (Finset.univ : Finset (Fin q → Finset (Fin H))),
        Real.exp (-((q * H + lambda : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro J _
      exact selector_one_rectangle_failure_le q H S lambda hS hlambda J
    _ = (2 : ℝ) ^ (q * H) * Real.exp (-((q * H + lambda : ℕ) : ℝ)) := by
      simp [← pow_mul, mul_comm]
    _ ≤ (1 / 2 : ℝ) ^ lambda := selector_exp_union_bound _ _

end Paper2.Yao
