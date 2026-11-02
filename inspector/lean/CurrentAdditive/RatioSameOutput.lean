import CurrentAdditive.RatioPositiveScaling
import CurrentAdditive.CodeDUpdateFullPipeline
import CurrentAdditive.MinimumRatioWitness

set_option maxHeartbeats 800000

namespace CurrentAdditive.RatioSameOutput
open SequentialCode RatioPositiveScaling CodeDUpdatedArithmeticABI

theorem candidateWeights_scaled {α : Type*} (source : Array (α × ℚ))
    (coeff : Array ℚ) (lambda s : ℚ) (hs : 0 < s) :
    candidateWeights source (scaled s coeff) (lambda / s) =
      candidateWeights source coeff lambda := by
  apply congrArg Array.ofFn
  funext i
  rw [scaled_get]
  congr 1
  field_simp

theorem candidateWeights_integer {α : Type*} (source : Array (α × ℚ))
    (coeff : Array ℚ) (lambda : ℚ) (D : Nat) (hD : 0 < D)
    (z : Fin coeff.size → ℤ)
    (hcoeff : ∀ i : Fin coeff.size,
      coeff[i.val]?.getD 0 = (z i : ℚ) / (D : ℚ)) :
    candidateWeights source (Array.ofFn fun i => (z i : ℚ)) (lambda / D) =
      candidateWeights source coeff lambda := by
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  have he : Array.ofFn (fun i => (z i : ℚ)) = scaled (D : ℚ) coeff := by
    apply scaled_eq_of_entrywise
    · simp
    · intro i hi
      rw [show (Array.ofFn fun i => (z i : ℚ))[i]?.getD 0 =
        (z ⟨i,hi⟩ : ℚ) by simp [hi],hcoeff ⟨i,hi⟩]
      field_simp
  rw [he,candidateWeights_scaled source coeff lambda (D : ℚ) hDq]

/-- Positive relation normalization preserves all weights, all tied zero
positions, and the order of every retained original source position. -/
theorem retained_integer {q : Nat} (source : Array ((Fin q → Nat) × ℚ))
    (coeff : Array ℚ) (lambda : ℚ) (D : Nat) (hD : 0 < D)
    (z : Fin coeff.size → ℤ)
    (hcoeff : ∀ i : Fin coeff.size,
      coeff[i.val]?.getD 0 = (z i : ℚ) / (D : ℚ)) :
    CodeDCompactSequentialBridge.retainedSource source
      (candidateWeights source (Array.ofFn fun i => (z i : ℚ)) (lambda / D)) =
    CodeDCompactSequentialBridge.retainedSource source
      (candidateWeights source coeff lambda) := by
  rw [candidateWeights_integer source coeff lambda D hD z hcoeff]

/-- The minimum used by the actual rational relation is attained at an
original position, and that same position attains the normalized minimum. -/
theorem attained_integer (weights coeff : Array ℚ) (lambda : ℚ)
    (hmin : minimumRatio weights coeff = some lambda)
    (D : Nat) (hD : 0 < D) (z : Fin coeff.size → ℤ)
    (hcoeff : ∀ i : Fin coeff.size,
      coeff[i.val]?.getD 0 = (z i : ℚ) / (D : ℚ)) :
    ∃ j : Fin coeff.size, j.val < weights.size ∧
      0 < z j ∧ lambda = weights[j.val]?.getD 0 / coeff[j.val]?.getD 0 ∧
      lambda / D = weights[j.val]?.getD 0 / (z j : ℚ) := by
  obtain ⟨j,hj,hpos,hratio⟩ := RationalBitBounds.minimumRatio_attained weights coeff lambda hmin
  have hbound := List.mem_range.mp hj
  have hc : j < coeff.size := lt_of_lt_of_le hbound (Nat.min_le_right _ _)
  have hw : j < weights.size := lt_of_lt_of_le hbound (Nat.min_le_left _ _)
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  have hzq : (0 : ℚ) < z ⟨j,hc⟩ := by
    rw [hcoeff ⟨j,hc⟩] at hpos
    exact (div_pos_iff_of_pos_right hDq).mp hpos
  refine ⟨⟨j,hc⟩,hw,by exact_mod_cast hzq,hratio,?_⟩
  rw [hratio,hcoeff ⟨j,hc⟩]
  field_simp

#print axioms candidateWeights_integer
#print axioms retained_integer
#print axioms attained_integer
end CurrentAdditive.RatioSameOutput
