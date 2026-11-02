import CurrentAdditive.CodeDRawPass

namespace CurrentAdditive.CodeDInnerFuelPreparation
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
open EthInapproximability.CurrentPaper

def rowCoefficient := Classical.choose GaussGridInputPolynomial.row_clock_polynomial
def rowExponent := Classical.choose (Classical.choose_spec GaussGridInputPolynomial.row_clock_polynomial)
def entries {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) :=
  (CodeDCanonicalSourceV2.canonicalSource source).map CodeDSourceCodecV2.encodeEntry

theorem encoded_entries {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) :
    SourceListEncoding.encode (entries source)=CodeDCanonicalSourceV2.encodedSource source := rfl

theorem entries_length {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) :
    (entries source).length=source.size := by simp [entries,CodeDCanonicalSourceV2.canonicalSource]

theorem row_outputs {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) :
    GaussRowCount.machine.OutputsWithin (CodeDCanonicalSourceV2.encodedSource source)
      (List.replicate source.size true)
      (rowCoefficient*((CodeDCanonicalSourceV2.encodedSource source).length+1)^rowExponent) := by
  have h:=GaussRowCount.outputs_polynomial (entries source)
  rw [encoded_entries,entries_length] at h
  apply BitMachine.outputsWithin_mono _ h
  simpa only [Nat.zero_add] using
    (Classical.choose_spec (Classical.choose_spec GaussGridInputPolynomial.row_clock_polynomial))
      0 (CodeDCanonicalSourceV2.encodedSource source).length

abbrev S := BankFieldProjection.machine (2 : Fin 3)
def countMachine := BitMachineComposition.composition S GaussRowCount.machine
def countCoefficient := OrdinaryPolynomialComposition.coefficient S 10 rowCoefficient rowExponent
def countExponent := OrdinaryPolynomialComposition.degree 1 rowExponent

theorem count_outputs (q : Nat) (alphabet : Array (Nat × ℚ)) (source : Array ((Fin q → Nat) × ℚ)) :
    countMachine.OutputsWithin (CylinderRawMatrixProducer.input alphabet source)
      (List.replicate source.size true)
      (countCoefficient*((CylinderRawMatrixProducer.input alphabet source).length+1)^countExponent) := by
  have hs : S.OutputsWithin (CylinderRawMatrixProducer.input alphabet source)
      (CodeDCanonicalSourceV2.encodedSource source)
      (10*((CylinderRawMatrixProducer.input alphabet source).length+1)^1) := by
    simpa [CylinderRawMatrixProducer.input,CylinderRawInputProjection.input,BankFieldProjection.result_encode] using
      BankFieldProjection.outputs (2 : Fin 3) (CylinderRawMatrixProducer.input alphabet source)
  exact OrdinaryPolynomialComposition.outputsWithin S GaussRowCount.machine hs (row_outputs source)

abbrev I := BitMachineCopy.bitMachine
def machine := OrdinaryBankFork.machine I countMachine
def coefficient := OrdinaryBankFork.coefficient I countMachine 2 countCoefficient
def exponent := OrdinaryBankFork.degree 1 countExponent

theorem outputs (q : Nat) (alphabet : Array (Nat × ℚ)) (source : Array ((Fin q → Nat) × ℚ)) :
    machine.OutputsWithin (CylinderRawMatrixProducer.input alphabet source)
      (BitMachineBankCodec.encode ![CylinderRawMatrixProducer.input alphabet source,List.replicate source.size true])
      (coefficient*((CylinderRawMatrixProducer.input alphabet source).length+1)^exponent) := by
  have hi : I.OutputsWithin (CylinderRawMatrixProducer.input alphabet source)
      (CylinderRawMatrixProducer.input alphabet source)
      (2*((CylinderRawMatrixProducer.input alphabet source).length+1)^1) := by
    simpa only [pow_one] using BitMachineCopy.bitMachine_outputs (CylinderRawMatrixProducer.input alphabet source)
  exact OrdinaryPolynomialComposition.fork_outputsWithin I countMachine hi (count_outputs q alphabet source)

theorem source_size_le_input (q : Nat) (alphabet : Array (Nat × ℚ)) (source : Array ((Fin q → Nat) × ℚ)) :
    source.size≤(CylinderRawMatrixProducer.input alphabet source).length := by
  have h:=GaussRowCount.rows_le_input (entries source)
  rw [encoded_entries,entries_length] at h
  exact h.trans (BitMachineBankCodec.word_length_le_encode
    (![List.replicate q true,CodeDTargetV2.alphabetBytes alphabet,CodeDCanonicalSourceV2.encodedSource source]) (2 : Fin 3))

#print axioms outputs
#print axioms source_size_le_input
end
end CurrentAdditive.CodeDInnerFuelPreparation
