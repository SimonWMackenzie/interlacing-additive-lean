import CurrentAdditive.GaussFetchedArithmetic

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-! A single arithmetic coefficient is fixed before every input, every frame,
and every matrix dimension. -/
namespace CurrentAdditive.GaussFixedArithmeticClock
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.MinimumRatioContext GaussFetchedArithmetic

def inputPacket (flag : Bool) (current column row pivot : CodeDCodec.RawRat) :=
  GaussFetchedAdaptedRequest.packet flag
    (CodeDCodec.encodeRawRat current) (CodeDCodec.encodeRawRat column)
    (CodeDCodec.encodeRawRat row) (CodeDCodec.encodeRawRat pivot)

theorem packet_eq (flag : Bool) (current column row pivot : CodeDCodec.RawRat) :
    inputPacket flag current column row pivot =
      GaussUniformCellAlgebra.adaptedPacket flag current column row pivot := by
  cases flag <;>
    simp [inputPacket,GaussFetchedAdaptedRequest.packet,
      GaussFetchedAdaptedRequest.adjustedCurrent,
      GaussFetchedAdaptedRequest.adjustedColumn,
      GaussUniformCellAlgebra.adaptedPacket,
      GaussUniformCellAlgebra.adaptedCurrent,
      GaussUniformCellAlgebra.adaptedColumn,
      GaussAdaptPrepare64.zeroWord,GaussAdaptPrepare64.minusOneWord,
      GaussRequestTypedBridge64.packet_eq_cellPacket]

theorem exists_global_coefficient : ∃ C : Nat,
    ∀ (flag : Bool) (current column row pivot : CodeDCodec.RawRat),
      current.Valid → column.Valid → row.Valid → pivot.Valid →
      0 < EncodedCommunication.bitsValue pivot.numerator →
      M.OutputsWithin (inputPacket flag current column row pivot)
        (CodeDCodec.encodeRawRat
          (GaussCellArithmeticTarget.cellRaw flag current column row pivot))
        (C*((inputPacket flag current column row pivot).length+1)^
          GaussUniformMatrixRun.exponent) := by
  obtain ⟨f,C,hclock,hf⟩ := GaussUniformMatrixRun.uniform_cell_clock
  refine ⟨C,?_⟩
  intro flag current column row pivot hc hcol hr hp hn
  rw [packet_eq]
  simpa only [hf flag current column row pivot hc hcol hr hp hn]
    using hclock (GaussUniformCellAlgebra.adaptedPacket flag current column row pivot)

noncomputable def coefficient : Nat := Classical.choose exists_global_coefficient

theorem outputs_cell (flag : Bool) (current column row pivot : CodeDCodec.RawRat)
    (hc : current.Valid) (hcol : column.Valid) (hr : row.Valid) (hp : pivot.Valid)
    (hn : 0 < EncodedCommunication.bitsValue pivot.numerator) :
    M.OutputsWithin (inputPacket flag current column row pivot)
      (CodeDCodec.encodeRawRat
        (GaussCellArithmeticTarget.cellRaw flag current column row pivot))
      (coefficient*((inputPacket flag current column row pivot).length+1)^
        GaussUniformMatrixRun.exponent) :=
  Classical.choose_spec exists_global_coefficient flag current column row pivot hc hcol hr hp hn

theorem invoke_cell (S : Bank → List Bool) (flag : Bool)
    (current column row pivot : CodeDCodec.RawRat)
    (hc : current.Valid) (hcol : column.Valid) (hr : row.Valid) (hp : pivot.Valid)
    (hn : 0 < EncodedCommunication.bitsValue pivot.numerator)
    (hs : S slots.source = inputPacket flag current column row pivot)
    (ht : S slots.target = []) (hx : S slots.scratch = [])
    (hb : ∀ i, S (slots.machine i) = []) :
    ∃ t ≤ MachineInvokeFull.uniformBound M (inputPacket flag current column row pivot)
      (coefficient*((inputPacket flag current column row pivot).length+1)^
        GaussUniformMatrixRun.exponent),
      ((advance (MachineInvokeFull.program slots))^[t])
        (⟨some (MachineInvokeFull.start slots),MachineInvokeFull.control slots,S⟩ :
          TM2.Cfg (fun _ : Bank => Bool) _ _) =
        ⟨none,MachineInvokeFull.control slots,Function.update S slots.target
          (CodeDCodec.encodeRawRat
            (GaussCellArithmeticTarget.cellRaw flag current column row pivot))⟩ :=
  MachineInvokeFull.invoke_run_uniform slots S _ _ _ hs ht hx hb
    (outputs_cell flag current column row pivot hc hcol hr hp hn)

#print axioms exists_global_coefficient
#print axioms outputs_cell
#print axioms invoke_cell
end CurrentAdditive.GaussFixedArithmeticClock
