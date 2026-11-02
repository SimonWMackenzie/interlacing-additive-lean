import CurrentAdditive.RationalBitBounds
import CurrentAdditive.MinimumRatioWitness
import CurrentAdditive.SequentialCode

/-! The algebraic bit budget is tied here to the executable array update. -/

namespace CurrentAdditive.RationalBitBounds

open CurrentAdditive.SequentialCode

/-- The actual array update is precisely the displayed rational operation
once `minimumRatio` has selected a particular positive integer coefficient. -/
theorem eliminateWeights_representation
    (weights coeff : Array ℚ) (z : Fin weights.size → ℤ)
    (j : Fin weights.size) (out : Array ℚ)
    (hcoeff : ∀ i : Fin weights.size,
      (coeff[i.val]?.getD 0) = (z i : ℚ))
    (hmin : minimumRatio weights coeff =
      some (weights[j] / (z j : ℚ)))
    (hout : eliminateWeights weights coeff = some out)
    (enc : CommonDenominator (fun i : Fin weights.size => weights[i]))
    (hz : 0 < z j) :
    out.size = weights.size ∧
      ∀ i : Fin weights.size,
        out[i.val]?.getD 0 =
          (removedNumerator enc.numerator z j i : ℚ) /
            ((enc.denominator * (z j).toNat : ℕ) : ℚ) := by
  unfold eliminateWeights at hout
  simp only [hmin] at hout
  cases hout
  constructor
  · simp
  · intro i
    have hvalue :
        ((Array.ofFn (n := weights.size)
          (fun k => weights[k] -
            (weights[j] / (z j : ℚ)) * (coeff[k.val]?.getD 0)))[i.val]?.getD 0) =
          removeWeight (fun k : Fin weights.size => weights[k]) z j i := by
      simp [removeWeight, hcoeff i]
    rw [hvalue]
    exact removeWeight_represents enc z j i hz

/-- The selected positive coefficient multiplies the common denominator
for the *literal* `eliminateWeights` result, not merely an abstract update. -/
def executableCommonDenominator
    (weights coeff : Array ℚ) (z : Fin weights.size → ℤ)
    (j : Fin weights.size) (out : Array ℚ)
    (hcoeff : ∀ i : Fin weights.size,
      (coeff[i.val]?.getD 0) = (z i : ℚ))
    (hmin : minimumRatio weights coeff =
      some (weights[j] / (z j : ℚ)))
    (hout : eliminateWeights weights coeff = some out)
    (enc : CommonDenominator (fun i : Fin weights.size => weights[i]))
    (hz : 0 < z j) :
    CommonDenominator (fun i : Fin weights.size => out[i.val]?.getD 0) :=
  { denominator := enc.denominator * (z j).toNat
    positive := Nat.mul_pos enc.positive (by omega)
    numerator := removedNumerator enc.numerator z j
    represents := (eliminateWeights_representation weights coeff z j out
      hcoeff hmin hout enc hz).2 }

/-- Every successful literal integer-coefficient array update has a selected
positive coefficient that gives the next common denominator. -/
theorem eliminateWeights_has_commonDenominator
    (weights coeff : Array ℚ) (z : Fin weights.size → ℤ)
    (out : Array ℚ)
    (hcoeff : ∀ i : Fin weights.size,
      (coeff[i.val]?.getD 0) = (z i : ℚ))
    (hout : eliminateWeights weights coeff = some out)
    (enc : CommonDenominator (fun i : Fin weights.size => weights[i])) :
    ∃ j : Fin weights.size,
      0 < z j ∧
      Nonempty (CommonDenominator
        (fun i : Fin weights.size => out[i.val]?.getD 0)) := by
  cases hmin : minimumRatio weights coeff with
  | none =>
      simp [eliminateWeights, hmin] at hout
  | some t =>
      obtain ⟨j, hj, hjpos, hratio⟩ := minimumRatio_attained weights coeff t hmin
      have hjlt : j < weights.size := by
        have hbound := List.mem_range.mp hj
        omega
      let jf : Fin weights.size := ⟨j, hjlt⟩
      have hz : 0 < z jf := by
        have hc := hcoeff jf
        have hpos : (0 : ℚ) < (z jf : ℚ) := by simpa [jf, hc] using hjpos
        exact_mod_cast hpos
      have hmin' : minimumRatio weights coeff =
          some (weights[jf] / (z jf : ℚ)) := by
        rw [hmin, hratio]
        simp [jf, hcoeff jf, Array.getElem?_eq_getElem hjlt]
      exact ⟨jf, hz, ⟨executableCommonDenominator weights coeff z jf out
          hcoeff hmin' hout enc hz⟩⟩

end CurrentAdditive.RationalBitBounds
