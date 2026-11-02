import CurrentAdditive.RationalProductCellSelectBridge
import CurrentAdditive.GaussCellSpec

/-! The fixed physical selectors on the exact Gauss cell packet. -/

namespace EthInapproximability.CurrentPaper.RationalProductGaussCellBridge

open RationalProductCellSelectBridge
open CurrentAdditive.CodeDCodec CurrentAdditive.GaussPhysical

theorem row_pivot_outputs (pivotRow : Bool)
    (current column row pivot : RawRat) :
    (RationalProductCellSelect.machine 3 4 (by decide)).OutputsWithin
      (cellPacket pivotRow current column row pivot)
      (CurrentAdditive.CodeDPairProductTargetV2.pairBytes row pivot)
      (35*((cellPacket pivotRow current column row pivot).length+1)) := by
  unfold cellPacket
  apply RationalProductCellSelectBridge.row_pivot_outputs
  · simp [cellBank]
  · simp [cellBank]

theorem column_pivot_outputs (pivotRow : Bool)
    (current column row pivot : RawRat) :
    (RationalProductCellSelect.machine 2 4 (by decide)).OutputsWithin
      (cellPacket pivotRow current column row pivot)
      (CurrentAdditive.CodeDPairProductTargetV2.pairBytes column pivot)
      (35*((cellPacket pivotRow current column row pivot).length+1)) := by
  unfold cellPacket
  apply RationalProductCellSelectBridge.column_pivot_outputs
  · simp [cellBank]
  · simp [cellBank]

theorem column_pivot_retains_context (pivotRow : Bool)
    (current column row pivot : RawRat) :
    ∃ t ≤ 35*((cellPacket pivotRow current column row pivot).length+1),
      let c := RationalProductCellSelect.run 2 4 (by decide) t
        (RationalProductCellSelect.cfg (some (.inl (.scan 0))) none
          (fun _ => []) (cellPacket pivotRow current column row pivot) [] [])
      c.l = none ∧ c.stk (.inr 2) =
        CurrentAdditive.CodeDPairProductTargetV2.pairBytes column pivot ∧
      c.stk (.inl 1) = encodeRawRat current ∧
      c.stk (.inl 3) = encodeRawRat row := by
  unfold cellPacket
  have h := RationalProductCellSelectBridge.column_pivot_retains_context
    (cellBank pivotRow current column row pivot) column pivot
    (by simp [cellBank]) (by simp [cellBank])
  simpa [cellBank] using h

end EthInapproximability.CurrentPaper.RationalProductGaussCellBridge
