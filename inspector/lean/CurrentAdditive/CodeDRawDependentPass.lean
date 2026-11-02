import CurrentAdditive.CodeDPacketRouting
import CurrentAdditive.OrdinaryPolynomialComposition
import EthInapproximability.CurrentPaper.BitMachineCopy
import CurrentAdditive.CylinderRawMatrixProducer
import CurrentAdditive.GaussRationalPostloop
import CurrentAdditive.RatioBranchPacketMachine
import CurrentAdditive.CylinderWholeGauss

namespace CurrentAdditive.CodeDRawDependentPass
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
set_option synthInstance.maxSize 16384
open EthInapproximability.CurrentPaper
open CylinderFeatureCodec GaussCertificateVectorABI

def rawWords {q : Nat} (alphabet : Array (Nat × ℚ)) (source : Array ((Fin q → Nat) × ℚ)) : Fin 3 → List Bool :=
  ![List.replicate q true,CodeDTargetV2.alphabetBytes alphabet,CodeDCanonicalSourceV2.encodedSource source]

abbrev I := BitMachineCopy.bitMachine
def relationMachine := BitMachineComposition.composition CylinderRawMatrixProducer.machine
  GaussMatrixPostloopMachines.relationMachine
def relationCoefficient := OrdinaryPolynomialComposition.coefficient CylinderRawMatrixProducer.machine
  CylinderRawMatrixProducer.coefficient GaussRationalPostloop.relationCoefficient GaussRationalPostloop.relationExponent
def relationExponent := OrdinaryPolynomialComposition.degree CylinderRawMatrixProducer.exponent GaussRationalPostloop.relationExponent
def forkMachine := OrdinaryBankFork.machine I relationMachine
def forkCoefficient := OrdinaryBankFork.coefficient I relationMachine 2 relationCoefficient
def forkExponent := OrdinaryBankFork.degree 1 relationExponent
def requestMachine := BitMachineComposition.composition forkMachine CodeDPacketRouting.sourceCoefficients.machine
def requestCoefficient := OrdinaryPolynomialComposition.coefficient forkMachine forkCoefficient
  CodeDPacketRouting.sourceCoefficients.coefficient CodeDPacketRouting.sourceCoefficients.degree
def requestExponent := OrdinaryPolynomialComposition.degree forkExponent CodeDPacketRouting.sourceCoefficients.degree
def updateMachine := BitMachineComposition.composition requestMachine RatioBranchPacketMachine.machine
def updateCoefficient := OrdinaryPolynomialComposition.coefficient requestMachine requestCoefficient
  (RatioBranchPacketMachine.coefficient+6) (RatioBranchPacketMachine.exponent+1)
def updateExponent := OrdinaryPolynomialComposition.degree requestExponent (RatioBranchPacketMachine.exponent+1)
def retainMachine := OrdinaryBankFork.machine I updateMachine
def retainCoefficient := OrdinaryBankFork.coefficient I updateMachine 2 updateCoefficient
def retainExponent := OrdinaryBankFork.degree 1 updateExponent
def machine := BitMachineComposition.composition retainMachine CodeDPacketRouting.replaceLast.machine
def coefficient := OrdinaryPolynomialComposition.coefficient retainMachine retainCoefficient
  CodeDPacketRouting.replaceLast.coefficient CodeDPacketRouting.replaceLast.degree
def exponent := OrdinaryPolynomialComposition.degree retainExponent CodeDPacketRouting.replaceLast.degree

theorem columnCount_eq (q : Nat) (alphabet : Array (Nat × ℚ)) (source : Array ((Fin q → Nat) × ℚ)) :
    SequentialCode.columnCount (cylinders q 8192 (alphabet.map Prod.fst) source)=source.size := by
  simpa only [cylinders] using SequentialCompressionTotality.featureRows_columnCount
    (SequentialCode.generatedFeatures q 8192 (alphabet.map Prod.fst)).size
    (fun v j => SequentialCode.generatedFeatureValue v (SequentialCode.generatedFeatures q 8192 (alphabet.map Prod.fst))[j]) source
    (SequentialSourceCode.generatedFeatures_pos q 8192 (alphabet.map Prod.fst))

theorem rows_pos (q : Nat) (alphabet : Array (Nat × ℚ)) (source : Array ((Fin q → Nat) × ℚ)) :
    0 < (cylinders q 8192 (alphabet.map Prod.fst) source).size := by
  rw [cylinders_rows]
  exact SequentialSourceCode.generatedFeatures_pos q 8192 (alphabet.map Prod.fst)

theorem relation_outputs (q : Nat) (alphabet : Array (Nat × ℚ)) (source : Array ((Fin q → Nat) × ℚ))
    (cert : {x : Array ℚ // SequentialCode.IsDependence (cylinders q 8192 (alphabet.map Prod.fst) source) x})
    (hcert : MaterializedGauss.certifiedMaterializedDependence (cylinders q 8192 (alphabet.map Prod.fst) source)=some cert)
    (hdependent : SequentialTotality.typedFree
      (GaussControlTrace.after (SequentialArrayBridge.matrixOfArray (cylinders q 8192 (alphabet.map Prod.fst) source))
        (SequentialCode.columnCount (cylinders q 8192 (alphabet.map Prod.fst) source))).pivots≠none) :
    relationMachine.OutputsWithin (CylinderRawMatrixProducer.input alphabet source) (vectorPacket cert.val)
      (relationCoefficient*((CylinderRawMatrixProducer.input alphabet source).length+1)^relationExponent) := by
  have hr := GaussRationalPostloop.certificate_outputs (cylinders q 8192 (alphabet.map Prod.fst) source)
    (CylinderWholeGauss.matrix_zero_one q 8192 (alphabet.map Prod.fst) source) (rows_pos q alphabet source) hdependent cert hcert
  rw [←CylinderGaussABI.cylinder_to_gauss_bytes q 8192 (alphabet.map Prod.fst) source] at hr
  exact OrdinaryPolynomialComposition.outputsWithin CylinderRawMatrixProducer.machine
    GaussMatrixPostloopMachines.relationMachine (CylinderRawMatrixProducer.outputs_polynomial alphabet source) hr

theorem outputs (q : Nat) (alphabet : Array (Nat × ℚ)) (source : Array ((Fin q → Nat) × ℚ))
    (cert : {x : Array ℚ // SequentialCode.IsDependence (cylinders q 8192 (alphabet.map Prod.fst) source) x})
    (hcert : MaterializedGauss.certifiedMaterializedDependence (cylinders q 8192 (alphabet.map Prod.fst) source)=some cert)
    (hdependent : SequentialTotality.typedFree
      (GaussControlTrace.after (SequentialArrayBridge.matrixOfArray (cylinders q 8192 (alphabet.map Prod.fst) source))
        (SequentialCode.columnCount (cylinders q 8192 (alphabet.map Prod.fst) source))).pivots≠none)
    (lambda : ℚ) (hmin : SequentialCode.minimumRatio (source.map Prod.snd) cert.val=some lambda)
    (hnonneg : (CodeDUpdatedArithmeticABI.candidateWeights source cert.val lambda).all (fun w => decide (0 ≤ w))=true) :
    let out := CodeDCompactSequentialBridge.retainedSource source (CodeDUpdatedArithmeticABI.candidateWeights source cert.val lambda)
    machine.OutputsWithin (CylinderRawMatrixProducer.input alphabet source)
      (CylinderRawMatrixProducer.input alphabet out)
      (coefficient*((CylinderRawMatrixProducer.input alphabet source).length+1)^exponent) := by
  let x:=CylinderRawMatrixProducer.input alphabet source
  let out:=CodeDCompactSequentialBridge.retainedSource source (CodeDUpdatedArithmeticABI.candidateWeights source cert.val lambda)
  have hi : I.OutputsWithin x x (2*(x.length+1)^1) := by
    simpa only [pow_one] using BitMachineCopy.bitMachine_outputs x
  have hf:=OrdinaryPolynomialComposition.fork_outputsWithin I relationMachine hi
    (relation_outputs q alphabet source cert hcert hdependent)
  have hp:=CodeDPacketRouting.sourceCoefficients_outputs (rawWords alphabet source) (vectorPacket cert.val)
  have hr:=OrdinaryPolynomialComposition.outputsWithin forkMachine CodeDPacketRouting.sourceCoefficients.machine hf hp
  have hsize : cert.val.size=source.size :=
    ((SequentialCode.dependence_spec (cylinders q 8192 (alphabet.map Prod.fst) source) cert.val).mp cert.property).1.trans
      (columnCount_eq q alphabet source)
  have hu:=RatioBranchPacketMachine.outputs_polynomial source cert.val lambda hsize hmin hnonneg
  have hupdate:=OrdinaryPolynomialComposition.outputsWithin requestMachine RatioBranchPacketMachine.machine hr hu
  have hretain:=OrdinaryPolynomialComposition.fork_outputsWithin I updateMachine hi hupdate
  have hprint:=CodeDPacketRouting.replaceLast_outputs (rawWords alphabet source)
    (CodeDCanonicalSourceV2.encodedSource out)
  exact OrdinaryPolynomialComposition.outputsWithin retainMachine CodeDPacketRouting.replaceLast.machine hretain hprint

#print axioms relation_outputs
#print axioms outputs
end
end CurrentAdditive.CodeDRawDependentPass
