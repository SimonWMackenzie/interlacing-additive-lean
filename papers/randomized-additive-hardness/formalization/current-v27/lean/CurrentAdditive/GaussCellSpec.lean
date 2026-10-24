import CurrentAdditive.GaussTypedPacket

namespace CurrentAdditive.GaussPhysical

open CurrentAdditive.CodeDCodec
open EthInapproximability.CurrentPaper.BitMachineBankCodec

/-- The four rational operands of one clear operation: the current entry,
the same row's pivot-column entry, the pivot row's entry in the current
column, and the nonzero pivot. -/
def cellFormula (pivotRow : Bool) (current column row pivot : ℚ) : ℚ :=
  if pivotRow then row / pivot else current - (column / pivot) * row

theorem clearTyped_cellFormula {m k : ℕ}
    (B : Fin m → Fin k → ℚ) (r : Fin m) (c : Fin k)
    (i : Fin m) (j : Fin k) :
    CurrentAdditive.SequentialTotality.clearTyped B r c i j =
      cellFormula (decide (i = r)) (B i j) (B i c) (B r j) (B r c) := by
  by_cases h : i = r
  · subst i
    simp [cellFormula, CurrentAdditive.SequentialTotality.clearTyped]
  · simp [cellFormula, CurrentAdditive.SequentialTotality.clearTyped, h]

def cellBank (pivotRow : Bool) (current column row pivot : RawRat) :
    Bank 12 :=
  fun i =>
    if i = 0 then [pivotRow] else
    if i = 1 then encodeRawRat current else
    if i = 2 then encodeRawRat column else
    if i = 3 then encodeRawRat row else
    if i = 4 then encodeRawRat pivot else []

def cellPacket (pivotRow : Bool) (current column row pivot : RawRat) :
    List Bool :=
  encode (cellBank pivotRow current column row pivot)

@[simp] theorem decode_cellPacket
    (pivotRow : Bool) (current column row pivot : RawRat) :
    decode 12 (cellPacket pivotRow current column row pivot) =
      some (cellBank pivotRow current column row pivot) := by
  exact decode_encode _

def cellPacketValue (pivotRow : Bool)
    (current column row pivot : RawRat) : ℚ :=
  cellFormula pivotRow current.value column.value row.value pivot.value

theorem cellPacketValue_canonical (pivotRow : Bool)
    (current column row pivot : ℚ) :
    cellPacketValue pivotRow (rawOfRat current) (rawOfRat column)
      (rawOfRat row) (rawOfRat pivot) =
    cellFormula pivotRow current column row pivot := by
  simp [cellPacketValue, rawOfRat_value]

end CurrentAdditive.GaussPhysical
