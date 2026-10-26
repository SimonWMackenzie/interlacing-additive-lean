import EthInapproximability.CurrentPaper.SourceOriginalCNFPacketizerMachine
import EthInapproximability.CurrentPaper.SourceOriginalDinurListMapperCost
import EthInapproximability.CurrentPaper.BitMachineComposition

/-! Actual original-CNF to ordered original-n Dinur CSP packet-list prefix. -/

namespace EthInapproximability.CurrentPaper.SourceOriginalDinurPrefixMachine

variable {η : ℚ} (S : EncodedETHSource.Sparsification η)
  (D : EncodedETHSource.DinurReduction)

noncomputable def machine : BitMachine.Machine :=
  BitMachineComposition.composition
    (SourceOriginalCNFPacketizer.machine S)
    (SourceOriginalDinurListMapper.machine D)

noncomputable def totalTime (f : EncodedETHSource.ValidFormula) : ℕ :=
  SourceOriginalCNFPacketizer.totalTime S f +
    2*(SourceOriginalBranchPackets.packetList S f).length+2 +
    SourceOriginalDinurListMapper.mapTime S D f

/-- Cited sparsification runs first. Its canonical packet list is physically
transferred, bit by bit, into one fixed framed-list mapper, which invokes the
cited Dinur machine separately on every retained-original-n packet. -/
theorem canonical_outputsWithin (f : EncodedETHSource.ValidFormula) :
    (machine S D).OutputsWithin (EncodedCNF.encode f.val)
      (SourceOriginalDinurListMapper.outputList S D f) (totalTime S D f) := by
  exact BitMachineComposition.composition_outputsWithin
    (SourceOriginalCNFPacketizer.machine S)
    (SourceOriginalDinurListMapper.machine D)
    (SourceOriginalCNFPacketizer.canonical_outputsWithin S f)
    (SourceOriginalDinurListMapper.mapped_outputs S D f)

noncomputable def mapperEnvelope (f : EncodedETHSource.ValidFormula) : ℕ :=
  let b := (S.branches f).length
  let w := b.bits.length
  let n := f.val.variables
  5*w+7 + (b*SourceOriginalDinurListMapper.itemEnvelope S D n + b*(4*w+7)) +
    (4*w+(EncodedCommunication.natField b).length+
      b*SourceOriginalDinurListMapper.framedEnvelope S D n+9)

noncomputable def originalEnvelope (f : EncodedETHSource.ValidFormula) : ℕ :=
  SourceOriginalSparsificationMachine.totalTime S f +
    SourceOriginalCNFPacketizer.envelopeTime S f+1 +
    2*(3*(S.branches f).length*
      (SourceOriginalDinurListMapper.inputEnvelope S f.val.variables+1)+1)+2 +
    mapperEnvelope S D f

theorem totalTime_le_originalEnvelope (f : EncodedETHSource.ValidFormula)
    (hn : 1 ≤ f.val.variables) :
    totalTime S D f ≤ originalEnvelope S D f := by
  have hs := SourceOriginalCNFPacketizer.totalTime_le_envelope S f hn
  have hl := SourceOriginalBranchPackets.packetList_length S f hn
  have hm := SourceOriginalDinurListMapper.mapTime_le_count S D f hn
  have hl' : (SourceOriginalBranchPackets.packetList S f).length ≤
      3*(S.branches f).length*
        (SourceOriginalDinurListMapper.inputEnvelope S f.val.variables+1)+1 := by
    calc
      _ ≤ 3*(S.branches f).length*
        (2*(f.val.variables+
          (8*S.density+3)*f.val.variables*(f.val.variables.size+1))+3)+1 := hl
      _ = _ := by unfold SourceOriginalDinurListMapper.inputEnvelope; ring
  dsimp [totalTime, originalEnvelope, mapperEnvelope]
  omega

end EthInapproximability.CurrentPaper.SourceOriginalDinurPrefixMachine
