import CurrentAdditive.CodeDPacketRouting
import CurrentAdditive.OrdinaryPolynomialComposition
import EthInapproximability.CurrentPaper.BitMachineCopy
import CurrentAdditive.GenericCylinderRawMatrixProducer
import CurrentAdditive.GaussRationalPostloop
import CurrentAdditive.RatioBranchPacketMachine
import CurrentAdditive.CylinderWholeGauss

namespace CurrentAdditive.GenericCodeDDependentPass
noncomputable section
variable (D : Nat)
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
set_option synthInstance.maxSize 16384
open EthInapproximability.CurrentPaper
open CylinderFeatureCodec GaussCertificateVectorABI

def rawWords {q : Nat} (alphabet : Array (Nat × ℚ)) (source : Array ((Fin q → Nat) × ℚ)) : Fin 3 → List Bool :=
  ![List.replicate q true,CodeDTargetV2.alphabetBytes alphabet,CodeDCanonicalSourceV2.encodedSource source]

abbrev I := BitMachineCopy.bitMachine
def relationMachine := BitMachineComposition.composition (GenericCylinderRawMatrixProducer.machine D)
  GaussMatrixPostloopMachines.relationMachine
def relationCoefficient := OrdinaryPolynomialComposition.coefficient (GenericCylinderRawMatrixProducer.machine D)
  (GenericCylinderRawMatrixProducer.coefficient D) GaussRationalPostloop.relationCoefficient GaussRationalPostloop.relationExponent
def relationExponent := OrdinaryPolynomialComposition.degree (GenericCylinderRawMatrixProducer.exponent D) GaussRationalPostloop.relationExponent
def forkMachine := OrdinaryBankFork.machine I (relationMachine D)
def forkCoefficient := OrdinaryBankFork.coefficient I (relationMachine D) 2 (relationCoefficient D)
def forkExponent := OrdinaryBankFork.degree 1 (relationExponent D)
def requestMachine := BitMachineComposition.composition (forkMachine D) CodeDPacketRouting.sourceCoefficients.machine
def requestCoefficient := OrdinaryPolynomialComposition.coefficient (forkMachine D) (forkCoefficient D)
  CodeDPacketRouting.sourceCoefficients.coefficient CodeDPacketRouting.sourceCoefficients.degree
def requestExponent := OrdinaryPolynomialComposition.degree (forkExponent D) CodeDPacketRouting.sourceCoefficients.degree
def updateMachine := BitMachineComposition.composition (requestMachine D) RatioBranchPacketMachine.machine
def updateCoefficient := OrdinaryPolynomialComposition.coefficient (requestMachine D) (requestCoefficient D)
  (RatioBranchPacketMachine.coefficient+6) (RatioBranchPacketMachine.exponent+1)
def updateExponent := OrdinaryPolynomialComposition.degree (requestExponent D) (RatioBranchPacketMachine.exponent+1)
def retainMachine := OrdinaryBankFork.machine I (updateMachine D)
def retainCoefficient := OrdinaryBankFork.coefficient I (updateMachine D) 2 (updateCoefficient D)
def retainExponent := OrdinaryBankFork.degree 1 (updateExponent D)
def machine := BitMachineComposition.composition (retainMachine D) CodeDPacketRouting.replaceLast.machine
def coefficient := OrdinaryPolynomialComposition.coefficient (retainMachine D) (retainCoefficient D)
  CodeDPacketRouting.replaceLast.coefficient CodeDPacketRouting.replaceLast.degree
def exponent := OrdinaryPolynomialComposition.degree (retainExponent D) CodeDPacketRouting.replaceLast.degree

theorem columnCount_eq (q : Nat) (alphabet : Array (Nat × ℚ)) (source : Array ((Fin q → Nat) × ℚ)) :
    SequentialCode.columnCount (cylinders q D (alphabet.map Prod.fst) source)=source.size := by
  simpa only [cylinders] using SequentialCompressionTotality.featureRows_columnCount
    (SequentialCode.generatedFeatures q D (alphabet.map Prod.fst)).size
    (fun v j => SequentialCode.generatedFeatureValue v (SequentialCode.generatedFeatures q D (alphabet.map Prod.fst))[j]) source
    (SequentialSourceCode.generatedFeatures_pos q D (alphabet.map Prod.fst))

theorem rows_pos (q : Nat) (alphabet : Array (Nat × ℚ)) (source : Array ((Fin q → Nat) × ℚ)) :
    0 < (cylinders q D (alphabet.map Prod.fst) source).size := by
  rw [cylinders_rows]
  exact SequentialSourceCode.generatedFeatures_pos q D (alphabet.map Prod.fst)

theorem relation_outputs (hD : 1 ≤ D) (q : Nat) (alphabet : Array (Nat × ℚ)) (source : Array ((Fin q → Nat) × ℚ))
    (cert : {x : Array ℚ // SequentialCode.IsDependence (cylinders q D (alphabet.map Prod.fst) source) x})
    (hcert : MaterializedGauss.certifiedMaterializedDependence (cylinders q D (alphabet.map Prod.fst) source)=some cert)
    (hdependent : SequentialTotality.typedFree
      (GaussControlTrace.after (SequentialArrayBridge.matrixOfArray (cylinders q D (alphabet.map Prod.fst) source))
        (SequentialCode.columnCount (cylinders q D (alphabet.map Prod.fst) source))).pivots≠none) :
    (relationMachine D).OutputsWithin (GenericCylinderRawMatrixProducer.input alphabet source) (vectorPacket cert.val)
      ((relationCoefficient D)*((GenericCylinderRawMatrixProducer.input alphabet source).length+1)^(relationExponent D)) := by
  have hr := GaussRationalPostloop.certificate_outputs (cylinders q D (alphabet.map Prod.fst) source)
    (CylinderWholeGauss.matrix_zero_one q D (alphabet.map Prod.fst) source) ((rows_pos D) q alphabet source) hdependent cert hcert
  rw [←CylinderGaussABI.cylinder_to_gauss_bytes q D (alphabet.map Prod.fst) source] at hr
  exact OrdinaryPolynomialComposition.outputsWithin (GenericCylinderRawMatrixProducer.machine D)
    GaussMatrixPostloopMachines.relationMachine ((GenericCylinderRawMatrixProducer.outputs_polynomial D hD) alphabet source) hr

theorem outputs (hD : 1 ≤ D) (q : Nat) (alphabet : Array (Nat × ℚ)) (source : Array ((Fin q → Nat) × ℚ))
    (cert : {x : Array ℚ // SequentialCode.IsDependence (cylinders q D (alphabet.map Prod.fst) source) x})
    (hcert : MaterializedGauss.certifiedMaterializedDependence (cylinders q D (alphabet.map Prod.fst) source)=some cert)
    (hdependent : SequentialTotality.typedFree
      (GaussControlTrace.after (SequentialArrayBridge.matrixOfArray (cylinders q D (alphabet.map Prod.fst) source))
        (SequentialCode.columnCount (cylinders q D (alphabet.map Prod.fst) source))).pivots≠none)
    (lambda : ℚ) (hmin : SequentialCode.minimumRatio (source.map Prod.snd) cert.val=some lambda)
    (hnonneg : (CodeDUpdatedArithmeticABI.candidateWeights source cert.val lambda).all (fun w => decide (0 ≤ w))=true) :
    let out := CodeDCompactSequentialBridge.retainedSource source (CodeDUpdatedArithmeticABI.candidateWeights source cert.val lambda)
    (machine D).OutputsWithin (GenericCylinderRawMatrixProducer.input alphabet source)
      (GenericCylinderRawMatrixProducer.input alphabet out)
      ((coefficient D)*((GenericCylinderRawMatrixProducer.input alphabet source).length+1)^(exponent D)) := by
  let x:=GenericCylinderRawMatrixProducer.input alphabet source
  let out:=CodeDCompactSequentialBridge.retainedSource source (CodeDUpdatedArithmeticABI.candidateWeights source cert.val lambda)
  have hi : I.OutputsWithin x x (2*(x.length+1)^1) := by
    simpa only [pow_one] using BitMachineCopy.bitMachine_outputs x
  have hf:=OrdinaryPolynomialComposition.fork_outputsWithin I (relationMachine D) hi
    ((relation_outputs D hD) q alphabet source cert hcert hdependent)
  have hp:=CodeDPacketRouting.sourceCoefficients_outputs (rawWords alphabet source) (vectorPacket cert.val)
  have hr:=OrdinaryPolynomialComposition.outputsWithin (forkMachine D) CodeDPacketRouting.sourceCoefficients.machine hf hp
  have hsize : cert.val.size=source.size :=
    ((SequentialCode.dependence_spec (cylinders q D (alphabet.map Prod.fst) source) cert.val).mp cert.property).1.trans
      ((columnCount_eq D) q alphabet source)
  have hu:=RatioBranchPacketMachine.outputs_polynomial source cert.val lambda hsize hmin hnonneg
  have hupdate:=OrdinaryPolynomialComposition.outputsWithin (requestMachine D) RatioBranchPacketMachine.machine hr hu
  have hretain:=OrdinaryPolynomialComposition.fork_outputsWithin I (updateMachine D) hi hupdate
  have hprint:=CodeDPacketRouting.replaceLast_outputs (rawWords alphabet source)
    (CodeDCanonicalSourceV2.encodedSource out)
  exact OrdinaryPolynomialComposition.outputsWithin (retainMachine D) CodeDPacketRouting.replaceLast.machine hretain hprint

#print axioms relation_outputs
#print axioms outputs
end
end CurrentAdditive.GenericCodeDDependentPass
