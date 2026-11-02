import EthInapproximability.CurrentPaper.SourceOriginalCNFPacketizerProgram

/-! Exact shared-bank handoff: source output cells are packetizer input cells. -/

namespace EthInapproximability.CurrentPaper.SourceOriginalCNFPacketizer

open Turing BitMachineEncoding BitMachineStackEmbedding

variable {η : ℚ} (S : EncodedETHSource.Sparsification η)

noncomputable def sourceFinalBank (f : EncodedETHSource.ValidFormula) :
    Stack S → List Bool :=
  bank (sourceSlots S) (emptyBank S)
    (SourceOriginalSparsificationMachine.finalBank S
      (EncodedCNF.encode f.val) f.val.variables
      (SourceOriginalSparsificationMachine.sparseTime S
        (EncodedCNF.encode f.val)))

theorem sourceFinal_n (f : EncodedETHSource.ValidFormula) :
    sourceFinalBank S f (.inl (SourceOriginalSparsificationMachine.outputSlots S 0)) =
      List.replicate f.val.variables true := by
  change bank (sourceSlots S) (emptyBank S)
    (SourceOriginalSparsificationMachine.finalBank S
      (EncodedCNF.encode f.val) f.val.variables
      (SourceOriginalSparsificationMachine.sparseTime S
        (EncodedCNF.encode f.val)))
    (sourceSlots S (SourceOriginalSparsificationMachine.outputSlots S 0)) = _
  rw [bank_at]
  exact SourceOriginalSparsificationMachine.final_original_n S _ _ _

theorem sourceFinal_list (f : EncodedETHSource.ValidFormula) :
    sourceFinalBank S f (.inl (SourceOriginalSparsificationMachine.outputSlots S 1)) =
      EncodedETHSource.formulaListBits (S.branches f) := by
  change bank (sourceSlots S) (emptyBank S)
    (SourceOriginalSparsificationMachine.finalBank S
      (EncodedCNF.encode f.val) f.val.variables
      (SourceOriginalSparsificationMachine.sparseTime S
        (EncodedCNF.encode f.val)))
    (sourceSlots S (SourceOriginalSparsificationMachine.outputSlots S 1)) = _
  rw [bank_at]
  exact SourceOriginalSparsificationMachine.final_sparse_list_runtime S f

theorem sourceFinal_fresh (f : EncodedETHSource.ValidFormula)
    (k : PacketStack) : sourceFinalBank S f (.inr k) = [] := by
  rw [sourceFinalBank, bank_outside]
  · rfl
  · rintro ⟨j,h⟩
    cases h

theorem packetSlots_n :
    packetSlots S (.inl SourceOriginalPacketFraming.nStack) =
      .inl (SourceOriginalSparsificationMachine.outputSlots S 0) := by
  simp [packetSlots, packetSlotFn]

theorem packetSlots_source :
    packetSlots S (.inr 0) =
      .inl (SourceOriginalSparsificationMachine.outputSlots S 1) := by
  simp [packetSlots, packetSlotFn]

theorem packetSlots_other (k : PacketStack)
    (hn : k ≠ .inl SourceOriginalPacketFraming.nStack)
    (hs : k ≠ (.inr 0 : PacketStack)) :
    packetSlots S k = .inr k := by
  simp [packetSlots, packetSlotFn, hn, hs]

theorem packetStart_eq_sourceFinal (f : EncodedETHSource.ValidFormula) :
    bank (packetSlots S) (sourceFinalBank S f)
      (SourceOriginalListPacketizer.startCfg f.val.variables
        (EncodedETHSource.formulaListBits (S.branches f))).stk =
      sourceFinalBank S f := by
  apply bank_eq_self
  intro k
  by_cases hn : k = .inl SourceOriginalPacketFraming.nStack
  · subst k
    rw [SourceOriginalListPacketizer.startCfg]
    simp [SourceOriginalListPacketizer.startBank, packetSlots_n,
      sourceFinal_n]
  · by_cases hs : k = (.inr 0 : PacketStack)
    · subst k
      simp [SourceOriginalListPacketizer.startCfg,
        SourceOriginalListPacketizer.startBank, packetSlots_source,
        sourceFinal_list]
    · rw [packetSlots_other S k hn hs, sourceFinal_fresh]
      simp [SourceOriginalListPacketizer.startCfg,
        SourceOriginalListPacketizer.startBank, hn, hs]

end EthInapproximability.CurrentPaper.SourceOriginalCNFPacketizer
