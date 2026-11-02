import CurrentAdditive.GaussContextBridge
import CurrentAdditive.RationalProductSignedPhysical

namespace CurrentAdditive.GaussPhysical

open CurrentAdditive.CodeDCodec
open EthInapproximability.CurrentPaper.RationalProductSignedPhysical
open EthInapproximability.CurrentPaper

theorem numerator_positive_of_nonzero_value (r : RawRat)
    (h : r.value ≠ 0) :
    0 < EncodedCommunication.bitsValue r.numerator := by
  by_contra hz
  have hzero : EncodedCommunication.bitsValue r.numerator = 0 := by omega
  have hv : r.value = 0 := by
    simp [RawRat.value, hzero]
  exact h hv

/-- The positive-denominator signed product/quotient packets supply exactly
the two arithmetic stages used by each Gauss cell. Signed subtraction and
canonical normalization remain separate physical packet stages. -/
def quotientProduct (column row pivot : RawRat) : RawRat :=
  productRat (quotientRat column pivot) row

theorem quotientProduct_valid (column row pivot : RawRat)
    (hcolumn : column.Valid) (hrow : row.Valid)
    (hpn : pivot.value ≠ 0) :
    (quotientProduct column row pivot).Valid := by
  apply productRat_valid
  · exact quotientRat_valid column pivot hcolumn
      (numerator_positive_of_nonzero_value pivot hpn)
  · exact hrow

theorem quotientProduct_value (column row pivot : RawRat)
    (hcolumn : column.Valid) (hpivot : pivot.Valid)
    (hpn : pivot.value ≠ 0) :
    (quotientProduct column row pivot).value =
      (column.value / pivot.value) * row.value := by
  rw [quotientProduct, productRat_value,
    quotientRat_value column pivot hcolumn hpivot
      (numerator_positive_of_nonzero_value pivot hpn)]

theorem pivotQuotient_value (row pivot : RawRat)
    (hrow : row.Valid) (hpivot : pivot.Valid)
    (hpn : pivot.value ≠ 0) :
    (quotientRat row pivot).value = row.value / pivot.value :=
  quotientRat_value row pivot hrow hpivot
    (numerator_positive_of_nonzero_value pivot hpn)

theorem cellFormula_pipeline (pivotRow : Bool)
    (current column row pivot : RawRat)
    (hcolumn : column.Valid) (hrow : row.Valid)
    (hpivot : pivot.Valid) (hpn : pivot.value ≠ 0) :
    cellPacketValue pivotRow current column row pivot =
      if pivotRow then (quotientRat row pivot).value
      else current.value - (quotientProduct column row pivot).value := by
  cases pivotRow
  · simpa [cellPacketValue, cellFormula] using
      congrArg (fun q : ℚ => current.value - q)
        (quotientProduct_value column row pivot hcolumn hpivot hpn).symm
  · simpa [cellPacketValue, cellFormula] using
      (pivotQuotient_value row pivot hrow hpivot hpn).symm

end CurrentAdditive.GaussPhysical
