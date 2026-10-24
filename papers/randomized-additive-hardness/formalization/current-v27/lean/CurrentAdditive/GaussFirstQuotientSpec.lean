import CurrentAdditive.GaussArithmeticPipeline

namespace CurrentAdditive.GaussPhysical

open CurrentAdditive.CodeDCodec
open CurrentAdditive.GaussListContext
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.RationalProductSignedPhysical

def decodeCellContext (input : List Bool) : Option CellContext := do
  let S ← BitMachineBankCodec.decode 12 input
  let flag ← if S 0 = [true] then some true else
    if S 0 = [false] then some false else none
  let current ← decodeRawRat (S 1)
  let column ← decodeRawRat (S 2)
  let row ← decodeRawRat (S 3)
  let pivot ← decodeRawRat (S 4)
  pure ⟨flag, current, column, row, pivot⟩

theorem decodeCellContext_packet (x : CellContext)
    (hcurrent : x.current.Valid) (hcolumn : x.column.Valid)
    (hrow : x.row.Valid) (hpivot : x.pivot.Valid) :
    decodeCellContext (packet x) = some x := by
  cases x with
  | mk flag current column row pivot =>
      cases flag <;>
        simp [decodeCellContext, packet, cellPacket, cellBank,
          BitMachineBankCodec.decode_encode,
          decodeRawRat_encodeRawRat, hcurrent, hcolumn, hrow, hpivot]

/-- Exact output contract for the physical nested Bank12/Bank3 extractor.
The quotient machine will then consume this already packed arithmetic word. -/
def firstQuotientPacked (input : List Bool) : List Bool :=
  match decodeCellContext input with
  | none => []
  | some x =>
      quotientInput (if x.pivotRow then x.row else x.column) x.pivot

theorem firstQuotientPacked_packet (x : CellContext)
    (hcurrent : x.current.Valid) (hcolumn : x.column.Valid)
    (hrow : x.row.Valid) (hpivot : x.pivot.Valid) :
    firstQuotientPacked (packet x) =
      quotientInput (if x.pivotRow then x.row else x.column) x.pivot := by
  simp [firstQuotientPacked,
    decodeCellContext_packet x hcurrent hcolumn hrow hpivot]

end CurrentAdditive.GaussPhysical
