import CurrentAdditive.RestorationBudget
import CurrentAdditive.IndexedProfileConditioning

/-! The source-specific good-block selection in v27 Appendix H `det:restore`.
The width is `Q=2^r`, the final tuple law is the actual indexed `CodeSource`,
and each of the three profile thresholds is used literally. -/

namespace CurrentAdditive.DeterministicRestoration

open Paper2
open CurrentAdditive.DeterministicIndexedMatrix

theorem restore_selected_blocks
    {X Z : Type*} [Fintype X] [Fintype Z]
    [DecidableEq X] [DecidableEq Z]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Z)
    (r : ℕ) (src : CodeSource 8192 (2 ^ r) Z ν)
    (U : Set (Fin (2 ^ r) × X)) (Y : Set src.Label)
    (j : Fin 3) (θ φ δ : ℝ)
    (hθ0 : 0 < θ) (hφ : 0 < φ) (hδ : 0 < δ)
    (hQ : (128 : ℝ) *
      ((CurrentAdditive.conditioningExceptionCountR 1024 φ (δ / 2) : ℝ) + 1) ≤
        ((2 ^ r : ℕ) : ℝ))
    (hθ : ((2 ^ r : ℕ) : ℝ) * θ ≤ 1 / 20)
    (hU : ((3 / 5 : ℝ) * (1 / 2 : ℝ) ^ j.val) ≤
      ((PositiveRationalLaw.uniform (Fin (2 ^ r))).prod μ).toFiniteLaw.prob
        (· ∈ U))
    (hY : φ ≤ src.law.toFiniteLaw.prob (· ∈ Y)) :
    ∃ (E : Finset (Fin (2 ^ r)))
      (pick : Fin (2 ^ (r - j.val - 1) + 1) ↪ Fin (2 ^ r)),
      E.card ≤ CurrentAdditive.conditioningExceptionCountR 1024 φ (δ / 2) ∧
      (∀ h, pick h ∉ E) ∧
      (∀ h, ((2 ^ (r - j.val) : ℕ) : ℝ) * θ ≤
        μ.toFiniteLaw.prob (fun x => (pick h, x) ∈ U)) ∧
      (∀ J : Finset (Fin (2 ^ r)),
        J ⊆ Finset.univ \ E → J.card ≤ 8 →
          CurrentAdditive.projectionTV
            (CurrentAdditive.condition src.law.toFiniteLaw (· ∈ Y)
              (hφ.trans_le hY)) ν.toFiniteLaw src.decode J ≤
                CurrentAdditive.conditioningEpsilonR 1024 φ (δ / 2)) := by
  have hr : 3 ≤ r := by
    have h := width_exponent_seven r
      (CurrentAdditive.conditioningExceptionCountR 1024 φ (δ / 2)) hQ
    omega
  have hj : j.val + 1 ≤ r := by have := j.isLt; omega
  have hpow : 2 ^ (r - j.val) ≤ 2 ^ r :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpowR : (((2 ^ (r - j.val) : ℕ) : ℝ)) ≤ ((2 ^ r : ℕ) : ℝ) := by
    exact_mod_cast hpow
  have ht : ((2 ^ (r - j.val) : ℕ) : ℝ) * θ < 1 := by
    have hmul := mul_le_mul_of_nonneg_right hpowR hθ0.le
    linarith
  have hbudget := profile_population_budget r
    (CurrentAdditive.conditioningExceptionCountR 1024 φ (δ / 2))
    j θ hQ hθ hθ0.le
  letI : NeZero (2 ^ r) := ⟨by positivity⟩
  exact codeSource_select_conditioned_blocks μ ν src U Y
    (2 ^ (r - j.val - 1) + 1)
    ((3 / 5 : ℝ) * (1 / 2 : ℝ) ^ j.val)
    (((2 ^ (r - j.val) : ℕ) : ℝ) * θ)
    φ (δ / 2) ht hφ (by linarith) hU hY hbudget

#print axioms restore_selected_blocks

end CurrentAdditive.DeterministicRestoration
