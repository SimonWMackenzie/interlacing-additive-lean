import CurrentAdditive.GaussRawCross
import CurrentAdditive.GaussContextCallback

namespace CurrentAdditive.GaussPhysical

open CurrentAdditive.CodeDCodec
open CurrentAdditive.GaussListContext

/-- The physically useful unreduced cross fraction, followed by canonical
normalization, is exactly the expected output of the row-major context
mapper. This is an interface identity, not a claimed physical cell machine. -/
theorem callbackResult_eq_normalizedCross (x : CellContext)
    (hcurrent : x.current.Valid) (hcolumn : x.column.Valid)
    (hrow : x.row.Valid) (hpivot : x.pivot.Valid)
    (hp : x.pivot.value ≠ 0) :
    callbackResult (packet x) =
      encodeRawRat (rawOfRat ((crossRaw x.pivotRow
        x.current.value x.column.value x.row.value x.pivot.value).value)) := by
  rw [callbackResult_packet x hcurrent hcolumn hrow hpivot]
  rw [crossRaw_value x.pivotRow _ _ _ _ hp]
  rfl

end CurrentAdditive.GaussPhysical
