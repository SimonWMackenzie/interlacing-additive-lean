import CurrentAdditive.GenericCodeDDependentPass
import CurrentAdditive.OrdinaryBitBranch
import CurrentAdditive.CodeDCompressionIteration
import CurrentAdditive.CodeDMaterializedSuccessCertificate

namespace CurrentAdditive.GenericCodeDRawPass
noncomputable section
variable (D : Nat)
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
set_option synthInstance.maxSize 65536
open EthInapproximability.CurrentPaper
open CylinderFeatureCodec GaussCellPolynomialClock

def features (q : Nat) (alphabet : Array (Nat × ℚ)) :=
  SequentialCode.generatedFeatures q D (alphabet.map Prod.fst)
def phi (q : Nat) (alphabet : Array (Nat × ℚ)) (v : Fin q → Nat) (j : Fin ((features D) q alphabet).size) : ℚ :=
  SequentialCode.generatedFeatureValue v ((features D) q alphabet)[j]
def freeColumn (q : Nat) (alphabet : Array (Nat × ℚ)) (source : Array ((Fin q → Nat) × ℚ)) :=
  IndependentSupport.sourceFreeColumn ((features D) q alphabet).size ((phi D) q alphabet) source

def guardMachine := BitMachineComposition.composition (GenericCylinderRawMatrixProducer.machine D)
  GaussMatrixPostloopMachines.decisionMachine
def guardCoefficient := OrdinaryPolynomialComposition.coefficient (GenericCylinderRawMatrixProducer.machine D)
  (GenericCylinderRawMatrixProducer.coefficient D) GaussRationalPostloop.decisionCoefficient GaussRationalPostloop.decisionExponent
def guardExponent := OrdinaryPolynomialComposition.degree (GenericCylinderRawMatrixProducer.exponent D) GaussRationalPostloop.decisionExponent
abbrev I := BitMachineCopy.bitMachine
abbrev B := (GenericCodeDDependentPass.machine D)
def machine := OrdinaryBitBranch.machine (guardMachine D) I (B D)
def clock (n : Nat) :=
  OrdinaryBitBranch.invocationBound (guardMachine D) n ((guardCoefficient D)*(n+1)^(guardExponent D))+
  OrdinaryBitBranch.invocationBound I n (2*(n+1)^1)+
  OrdinaryBitBranch.invocationBound (B D) n ((GenericCodeDDependentPass.coefficient D)*(n+1)^(GenericCodeDDependentPass.exponent D))+1

theorem invocation_polynomial (M : BitMachine.Machine) (a d : Nat) :
    PolynomialBound (fun _ n => OrdinaryBitBranch.invocationBound M n (a*(n+1)^d)) :=
  uniform_invocation M second (mul (constant a) (power (add second (constant 1)) d))

theorem clock_polynomial : PolynomialBound (fun _ n => (clock D) n) :=
  add (add (add (invocation_polynomial (guardMachine D) (guardCoefficient D) (guardExponent D))
    (invocation_polynomial I 2 1))
    (invocation_polynomial (B D) (GenericCodeDDependentPass.coefficient D) (GenericCodeDDependentPass.exponent D))) (constant 1)
def coefficient := Classical.choose (clock_polynomial D)
def exponent := Classical.choose (Classical.choose_spec (clock_polynomial D))
theorem clock_le (n : Nat) : (clock D) n ≤ (coefficient D)*(n+1)^(exponent D) := by
  simpa only [Nat.zero_add] using (Classical.choose_spec (Classical.choose_spec (clock_polynomial D))) 0 n

theorem freeColumn_eq (q : Nat) (alphabet : Array (Nat × ℚ)) (source : Array ((Fin q → Nat) × ℚ)) :
    SequentialTotality.typedFree
      (GaussControlTrace.after (SequentialArrayBridge.matrixOfArray (cylinders q D (alphabet.map Prod.fst) source))
        (SequentialCode.columnCount (cylinders q D (alphabet.map Prod.fst) source))).pivots=
      (freeColumn D) q alphabet source := by
  rw [(GaussControlTrace.after_exact _ _).2]
  rfl

theorem guard_outputs (hD : 1 ≤ D) (q : Nat) (alphabet : Array (Nat × ℚ)) (source : Array ((Fin q → Nat) × ℚ)) :
    (guardMachine D).OutputsWithin (GenericCylinderRawMatrixProducer.input alphabet source)
      [decide ((freeColumn D) q alphabet source≠none)]
      ((guardCoefficient D)*((GenericCylinderRawMatrixProducer.input alphabet source).length+1)^(guardExponent D)) := by
  have hg:=GaussRationalPostloop.decision_outputs
    (SequentialArrayBridge.matrixOfArray (cylinders q D (alphabet.map Prod.fst) source))
    (CylinderWholeGauss.matrix_zero_one q D (alphabet.map Prod.fst) source)
    ((GenericCodeDDependentPass.rows_pos D) q alphabet source)
  rw [(freeColumn_eq D),←CylinderGaussABI.cylinder_to_gauss_bytes q D (alphabet.map Prod.fst) source] at hg
  exact OrdinaryPolynomialComposition.outputsWithin (GenericCylinderRawMatrixProducer.machine D)
    GaussMatrixPostloopMachines.decisionMachine ((GenericCylinderRawMatrixProducer.outputs_polynomial D hD) alphabet source) hg

theorem outputs_idle (hD : 1 ≤ D) (q : Nat) (alphabet : Array (Nat × ℚ)) (source : Array ((Fin q → Nat) × ℚ))
    (hfree : (freeColumn D) q alphabet source=none) :
    (machine D).OutputsWithin (GenericCylinderRawMatrixProducer.input alphabet source)
      (GenericCylinderRawMatrixProducer.input alphabet source)
      ((coefficient D)*((GenericCylinderRawMatrixProducer.input alphabet source).length+1)^(exponent D)) := by
  let x:=GenericCylinderRawMatrixProducer.input alphabet source
  have hg:=(guard_outputs D hD) q alphabet source
  simp [hfree] at hg
  have hi : I.OutputsWithin x x (2*(x.length+1)^1) := by
    simpa only [pow_one] using BitMachineCopy.bitMachine_outputs x
  have h:=OrdinaryBitBranch.outputsWithin (guardMachine D) I (B D) x x false
    ((guardCoefficient D)*(x.length+1)^(guardExponent D)) (2*(x.length+1)^1) hg hi
  apply BitMachine.outputsWithin_mono (machine D) h
  apply Nat.le_trans (m:=(clock D) x.length) ?_ ((clock_le D) x.length)
  change OrdinaryBitBranch.invocationBound (guardMachine D) x.length ((guardCoefficient D)*(x.length+1)^(guardExponent D))+
    OrdinaryBitBranch.invocationBound I x.length (2*(x.length+1)^1)+1≤(clock D) x.length
  unfold clock
  omega

theorem outputs_dependent (hD : 1 ≤ D) (q : Nat) (alphabet : Array (Nat × ℚ)) (source : Array ((Fin q → Nat) × ℚ))
    (hfree : (freeColumn D) q alphabet source≠none)
    (cert : {c : Array ℚ // SequentialCode.IsDependence (cylinders q D (alphabet.map Prod.fst) source) c})
    (hcert : MaterializedGauss.certifiedMaterializedDependence (cylinders q D (alphabet.map Prod.fst) source)=some cert)
    (lambda : ℚ) (hmin : SequentialCode.minimumRatio (source.map Prod.snd) cert.val=some lambda)
    (hnonneg : (CodeDUpdatedArithmeticABI.candidateWeights source cert.val lambda).all (fun w => decide (0 ≤ w))=true) :
    let out:=CodeDCompactSequentialBridge.retainedSource source (CodeDUpdatedArithmeticABI.candidateWeights source cert.val lambda)
    (machine D).OutputsWithin (GenericCylinderRawMatrixProducer.input alphabet source)
      (GenericCylinderRawMatrixProducer.input alphabet out)
      ((coefficient D)*((GenericCylinderRawMatrixProducer.input alphabet source).length+1)^(exponent D)) := by
  let x:=GenericCylinderRawMatrixProducer.input alphabet source
  let out:=CodeDCompactSequentialBridge.retainedSource source (CodeDUpdatedArithmeticABI.candidateWeights source cert.val lambda)
  let y:=GenericCylinderRawMatrixProducer.input alphabet out
  have hg:=(guard_outputs D hD) q alphabet source
  simp [hfree] at hg
  have hd : SequentialTotality.typedFree
      (GaussControlTrace.after (SequentialArrayBridge.matrixOfArray (cylinders q D (alphabet.map Prod.fst) source))
        (SequentialCode.columnCount (cylinders q D (alphabet.map Prod.fst) source))).pivots≠none := by
    rw [(freeColumn_eq D)]; exact hfree
  have hb:=(GenericCodeDDependentPass.outputs D hD) q alphabet source cert hcert hd lambda hmin hnonneg
  have h:=OrdinaryBitBranch.outputsWithin (guardMachine D) I (B D) x y true
    ((guardCoefficient D)*(x.length+1)^(guardExponent D))
    ((GenericCodeDDependentPass.coefficient D)*(x.length+1)^(GenericCodeDDependentPass.exponent D)) hg hb
  apply BitMachine.outputsWithin_mono (machine D) h
  apply Nat.le_trans (m:=(clock D) x.length) ?_ ((clock_le D) x.length)
  change OrdinaryBitBranch.invocationBound (guardMachine D) x.length ((guardCoefficient D)*(x.length+1)^(guardExponent D))+
    OrdinaryBitBranch.invocationBound (B D) x.length ((GenericCodeDDependentPass.coefficient D)*(x.length+1)^(GenericCodeDDependentPass.exponent D))+1≤(clock D) x.length
  unfold clock
  omega

theorem outputs (hD : 1 ≤ D) (q : Nat) (alphabet : Array (Nat × ℚ)) (source : Array ((Fin q → Nat) × ℚ))
    (hpositive : SequentialSourceCode.SourcePositive source) :
    (machine D).OutputsWithin (GenericCylinderRawMatrixProducer.input alphabet source)
      (GenericCylinderRawMatrixProducer.input alphabet
        (CodeDCompressionIteration.onePass ((features D) q alphabet).size ((phi D) q alphabet) source))
      ((coefficient D)*((GenericCylinderRawMatrixProducer.input alphabet source).length+1)^(exponent D)) := by
  cases hf : (freeColumn D) q alphabet source with
  | none =>
    have hp:=CodeDCompressionIteration.onePass_of_none ((features D) q alphabet).size ((phi D) q alphabet) source hf
    rw [hp]
    exact (outputs_idle D hD) q alphabet source hf
  | some f =>
    obtain ⟨next,hs⟩:=IndependentSupport.compressSourceOnce_total_of_free
      ((features D) q alphabet).size ((phi D) q alphabet) source
      (SequentialSourceCode.generatedFeatures_pos q D (alphabet.map Prod.fst))
      (SequentialSourceCode.generatedFeatures_constant q D (alphabet.map Prod.fst)) ⟨f,hf⟩ hpositive
    obtain ⟨cert,hcert,lambda,hmin,hnonneg,hnext⟩:=
      CodeDMaterializedSuccessCertificate.successful_step_certificate ((phi D) q alphabet) source next hs
    have hfree : (freeColumn D) q alphabet source≠none := by rw [hf]; simp
    have hout:=(outputs_dependent D hD) q alphabet source hfree cert hcert lambda hmin hnonneg
    rw [←hnext] at hout
    have hp:=CodeDCompressionIteration.onePass_of_step ((features D) q alphabet).size ((phi D) q alphabet) source next f hf hs
    rw [hp]
    exact hout

#print axioms guard_outputs
#print axioms outputs_idle
#print axioms outputs_dependent
#print axioms outputs
end
end CurrentAdditive.GenericCodeDRawPass
