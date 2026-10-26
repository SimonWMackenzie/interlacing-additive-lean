import CurrentAdditive.MaterializedCandidateBound
import CurrentAdditive.MinimumRatioWitness
import CurrentAdditive.RationalBitBounds

set_option maxHeartbeats 1000000

namespace CurrentAdditive.RationalCandidateCompletion

open CurrentAdditive.SequentialCode
open CurrentAdditive.RationalBitBounds

/-- A rational relation represented using one positive determinant denominator
induces exactly the manuscript's integer numerator update. The physical array
operation still takes the rational coefficients; no integer-clearing routine
is substituted. -/
theorem eliminateWeights_shared_denominator
    (weights coeff out : Array ℚ)
    (hsize : coeff.size = weights.size)
    (hout : eliminateWeights weights coeff = some out)
    (D : ℕ) (hD : 0 < D) (z : Fin weights.size → ℤ)
    (hcoeff : ∀ i : Fin weights.size,
      coeff[i.val]?.getD 0 = (z i : ℚ) / (D : ℚ))
    (enc : CommonDenominator (fun i : Fin weights.size => weights[i])) :
    ∃ j : Fin weights.size,
      0 < z j ∧
      out.size = weights.size ∧
      ∀ i : Fin weights.size,
        out[i.val]?.getD 0 =
          (removedNumerator enc.numerator z j i : ℚ) /
            ((enc.denominator * (z j).toNat : ℕ) : ℚ) := by
  cases hmin : minimumRatio weights coeff with
  | none => simp [eliminateWeights, hmin] at hout
  | some t =>
      obtain ⟨j, hj, hjpos, hratio⟩ := minimumRatio_attained weights coeff t hmin
      have hjlt : j < weights.size :=
        lt_of_lt_of_le (List.mem_range.mp hj) (Nat.min_le_left _ _)
      let jf : Fin weights.size := ⟨j, hjlt⟩
      have hdq : (D : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
      have hdpos : (0 : ℚ) < D := by exact_mod_cast hD
      have hjrep : coeff[j]?.getD 0 = (z jf : ℚ) / (D : ℚ) := by
        simpa [jf] using hcoeff jf
      have hzq : (0 : ℚ) < (z jf : ℚ) := by
        have hmul := mul_pos hjpos hdpos
        rw [hjrep] at hmul
        simpa [div_mul_cancel₀, hdq] using hmul
      have hz : 0 < z jf := by exact_mod_cast hzq
      have hmin' : minimumRatio weights coeff =
          some (weights[jf] / (coeff[jf.val]?.getD 0)) := by
        rw [hmin, hratio]
        simp [jf, hjlt]
      have hfactor (i : Fin weights.size) :
          (weights[jf.val] / (coeff[jf.val]?.getD 0)) *
              (coeff[i.val]?.getD 0) =
            (weights[jf.val] / (z jf : ℚ)) * (z i : ℚ) := by
        rw [hcoeff jf, hcoeff i]
        have hzneq : (z jf : ℚ) ≠ 0 := ne_of_gt hzq
        field_simp
      unfold eliminateWeights at hout
      rw [hmin'] at hout
      simp at hout
      subst out
      refine ⟨jf, hz, by simp, ?_⟩
      intro i
      have hrepr := removeWeight_represents enc z jf i hz
      simp only [Array.getElem?_ofFn, dif_pos i.isLt, Option.getD_some]
      rw [hfactor i]
      exact hrepr

#print axioms eliminateWeights_shared_denominator

end CurrentAdditive.RationalCandidateCompletion
