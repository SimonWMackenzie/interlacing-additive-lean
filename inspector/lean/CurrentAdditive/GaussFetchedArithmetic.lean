import CurrentAdditive.GaussFetchedAdaptedRequest
import CurrentAdditive.MachineInvokeFull
import CurrentAdditive.GaussUniformMatrixRun

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

namespace CurrentAdditive.GaussFetchedArithmetic
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.MinimumRatioContext

noncomputable def M : BitMachine.Machine := GaussCellSubtractCall.machine
abbrev Bank := MachineInvokeCore.StackN (32 + M.stackCount)

def lower : Fin 64 ↪ Bank := ⟨fun i => ⟨i.val, by omega⟩, by
  intro i j h; exact Fin.ext (congrArg (fun z : Bank => z.val) h)⟩

noncomputable def slots : MachineInvokeCore.Slots M (32 + M.stackCount) where
  machine := ⟨fun i => ⟨64+i.val, by omega⟩, by
    intro i j h; apply Fin.ext; have hv := congrArg Fin.val h; change 64+i.val=64+j.val at hv; omega⟩
  source := ⟨23,by omega⟩
  target := ⟨29,by omega⟩
  scratch := ⟨30,by omega⟩
  source_target := by decide
  source_scratch := by decide
  target_scratch := by decide
  source_machine := by intro i h; have hv := congrArg Fin.val h; change 23=64+i.val at hv; omega
  target_machine := by intro i h; have hv := congrArg Fin.val h; change 29=64+i.val at hv; omega
  scratch_machine := by intro i h; have hv := congrArg Fin.val h; change 30=64+i.val at hv; omega

def requestProgram (l : GaussFetchedAdaptedRequest.Label) :=
  BitMachineStackEmbedding.stmt lower id id id none
    (GaussFetchedAdaptedRequest.program l)

noncomputable def program := BitMachineRawSequence.program
  requestProgram (MachineInvokeFull.program slots)
  (MachineInvokeFull.start slots)
  ((GaussFetchedAdaptedRequest.fourControl,((),none)),none)
  (MachineInvokeFull.control slots)

abbrev Label := BitMachineRawSequence.Label GaussFetchedAdaptedRequest.Label (MachineInvokeFull.LabelFull M)
abbrev Control := BitMachineRawSequence.Control GaussFetchedAdaptedRequest.Control (MachineInvokeFull.ControlFull M)

noncomputable def start : Label := BitMachineRawSequence.leftLabel
  (BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel GaussFetchedAdaptedRequest.fourStart))

noncomputable def control : Control :=
  (((GaussFetchedAdaptedRequest.fourControl,((),none)),none),
    MachineInvokeFull.control slots)

/-- Closed physical arithmetic invocation. It consumes the literal packet
already on source23, writes a canonical rational to29, clears all embedded
arithmetic banks, and preserves the complete remaining bank. -/
theorem invoke_cell
    (S : Bank → List Bool) (flag : Bool)
    (current column row pivot : CodeDCodec.RawRat)
    (hc : current.Valid) (hcol : column.Valid)
    (hr : row.Valid) (hp : pivot.Valid)
    (hnum : 0 < EncodedCommunication.bitsValue pivot.numerator)
    (hsource : S slots.source = GaussFetchedAdaptedRequest.packet flag
      (CodeDCodec.encodeRawRat current) (CodeDCodec.encodeRawRat column)
      (CodeDCodec.encodeRawRat row) (CodeDCodec.encodeRawRat pivot))
    (htarget : S slots.target = []) (hscratch : S slots.scratch = [])
    (hblank : ∀ i, S (slots.machine i) = []) :
    ∃ C t : Nat,
      t ≤ MachineInvokeFull.uniformBound M
        (GaussFetchedAdaptedRequest.packet flag
          (CodeDCodec.encodeRawRat current) (CodeDCodec.encodeRawRat column)
          (CodeDCodec.encodeRawRat row) (CodeDCodec.encodeRawRat pivot))
        (C * ((GaussFetchedAdaptedRequest.packet flag
          (CodeDCodec.encodeRawRat current) (CodeDCodec.encodeRawRat column)
          (CodeDCodec.encodeRawRat row) (CodeDCodec.encodeRawRat pivot)).length+1)^
          GaussUniformMatrixRun.exponent) ∧
      ((advance (MachineInvokeFull.program slots))^[t])
        (⟨some (MachineInvokeFull.start slots), MachineInvokeFull.control slots,S⟩ :
          TM2.Cfg (fun _ : Bank => Bool) _ _) =
        ⟨none,MachineInvokeFull.control slots,
          Function.update S slots.target
            (CodeDCodec.encodeRawRat
              (GaussCellArithmeticTarget.cellRaw flag current column row pivot))⟩ := by
  have hpacket : GaussFetchedAdaptedRequest.packet flag
      (CodeDCodec.encodeRawRat current) (CodeDCodec.encodeRawRat column)
      (CodeDCodec.encodeRawRat row) (CodeDCodec.encodeRawRat pivot) =
      GaussUniformCellAlgebra.adaptedPacket flag current column row pivot := by
    cases flag <;>
      simp [GaussFetchedAdaptedRequest.packet,
        GaussFetchedAdaptedRequest.adjustedCurrent,
        GaussFetchedAdaptedRequest.adjustedColumn,
        GaussUniformCellAlgebra.adaptedPacket,
        GaussUniformCellAlgebra.adaptedCurrent,
        GaussUniformCellAlgebra.adaptedColumn,
        GaussAdaptPrepare64.zeroWord, GaussAdaptPrepare64.minusOneWord,
        GaussRequestTypedBridge64.packet_eq_cellPacket]
  obtain ⟨f,C,hclock,hf⟩ := GaussUniformMatrixRun.uniform_cell_clock
  have hM : M.OutputsWithin
      (GaussFetchedAdaptedRequest.packet flag
        (CodeDCodec.encodeRawRat current) (CodeDCodec.encodeRawRat column)
        (CodeDCodec.encodeRawRat row) (CodeDCodec.encodeRawRat pivot))
      (CodeDCodec.encodeRawRat
        (GaussCellArithmeticTarget.cellRaw flag current column row pivot))
      (C*((GaussFetchedAdaptedRequest.packet flag
        (CodeDCodec.encodeRawRat current) (CodeDCodec.encodeRawRat column)
        (CodeDCodec.encodeRawRat row) (CodeDCodec.encodeRawRat pivot)).length+1)^
          GaussUniformMatrixRun.exponent) := by
    rw [hpacket]
    simpa only [hf flag current column row pivot hc hcol hr hp hnum]
      using hclock (GaussUniformCellAlgebra.adaptedPacket flag current column row pivot)
  obtain ⟨t,ht,h⟩ := MachineInvokeFull.invoke_run_uniform slots S _ _ _
    hsource htarget hscratch hblank hM
  exact ⟨C,t,ht,h⟩

#print axioms invoke_cell
end CurrentAdditive.GaussFetchedArithmetic
