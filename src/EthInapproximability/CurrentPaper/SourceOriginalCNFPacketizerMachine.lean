import EthInapproximability.CurrentPaper.SourceOriginalCNFPacketizerRun

/-! Ordinary finite-stack machine endpoint for canonical original CNF inputs. -/

namespace EthInapproximability.CurrentPaper.SourceOriginalCNFPacketizer

open Turing BitMachineEncoding BitMachineStackEmbedding

variable {η : ℚ} (S : EncodedETHSource.Sparsification η)

def inputStack : Stack S := .inl (.inl (0 : SourceOriginalVariableCapture.Stack))
def startLabel : Label S := BitMachineRawSequence.leftLabel
  (BitMachineRawSequence.leftLabel SourceOriginalVariableCapture.Label.scan)
noncomputable def initialControl : Control S :=
  ((none,S.machine.initial),SourceOriginalListPacketizer.initialControl)

noncomputable def machine : BitMachine.Machine :=
  ofFinite (inputStack S) (outputStack S) (startLabel S)
    (initialControl S) (program S)

def captureSlots : SourceOriginalVariableCapture.Stack ↪ SourceStack S where
  toFun := Sum.inl
  inj' := Sum.inl_injective

theorem entry_rawInit (input : List Bool) :
    entry S input = rawInit (inputStack S) (startLabel S)
      (initialControl S) input := by
  have hbank : bank (sourceSlots S) (emptyBank S)
      (SourceOriginalSparsificationMachine.startBank S input) =
      (fun k => if k = inputStack S then input else []) := by
    funext k
    cases k with
    | inr k =>
        have hk : ¬ ∃ j : SourceStack S, sourceSlots S j = (.inr k : Stack S) := by
          rintro ⟨j,hj⟩
          cases hj
        rw [bank_outside (sourceSlots S) _ _ _ hk]
        simp [emptyBank, inputStack]
    | inl k =>
        change bank (sourceSlots S) (emptyBank S)
          (SourceOriginalSparsificationMachine.startBank S input)
          (sourceSlots S k) = _
        rw [bank_at]
        cases k with
        | inl j =>
            unfold SourceOriginalSparsificationMachine.startBank
            change bank (captureSlots S) (fun _ => [])
              (SourceOriginalVariableCapture.cfg (some .scan) none input [] []).stk
              (captureSlots S j) = _
            rw [bank_at]
            fin_cases j <;> simp [SourceOriginalVariableCapture.cfg,
              inputStack]
        | inr j =>
            unfold SourceOriginalSparsificationMachine.startBank
            change bank (captureSlots S) (fun _ => [])
              (SourceOriginalVariableCapture.cfg (some .scan) none input [] []).stk
              (.inr j) = _
            rw [bank_outside]
            · change ([] : List Bool) = _
              simp [inputStack]
            · rintro ⟨i,hi⟩
              fin_cases i <;> cases hi
  exact congrArg (fun B : Stack S → List Bool =>
    (⟨some (startLabel S), initialControl S,B⟩ : Config S)) hbank

theorem canonical_outputsWithin (f : EncodedETHSource.ValidFormula) :
    (machine S).OutputsWithin (EncodedCNF.encode f.val)
      (SourceOriginalBranchPackets.packetList S f) (totalTime S f) := by
  obtain ⟨t, ht, hh, ho⟩ := canonical_run S f
  have hraw : entry S (EncodedCNF.encode f.val) =
      rawInit (inputStack S) (startLabel S) (initialControl S)
        (EncodedCNF.encode f.val) := entry_rawInit S _
  rw [hraw] at hh ho
  exact outputsWithin_of_raw_run (inputStack S) (outputStack S)
    (startLabel S) (initialControl S) (program S)
    (EncodedCNF.encode f.val) (SourceOriginalBranchPackets.packetList S f)
    t (totalTime S f) ht hh ho

end EthInapproximability.CurrentPaper.SourceOriginalCNFPacketizer
