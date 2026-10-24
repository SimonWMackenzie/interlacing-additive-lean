import CurrentAdditive.CodeDRawDependentPass
import CurrentAdditive.OrdinaryBitBranch
import CurrentAdditive.CodeDCompressionIteration
import CurrentAdditive.CodeDMaterializedSuccessCertificate

namespace CurrentAdditive.CodeDRawPass
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
set_option synthInstance.maxSize 65536
open EthInapproximability.CurrentPaper
open CylinderFeatureCodec GaussCellPolynomialClock

def features (q : Nat) (alphabet : Array (Nat × ℚ)) :=
  SequentialCode.generatedFeatures q 8192 (alphabet.map Prod.fst)
def phi (q : Nat) (alphabet : Array (Nat × ℚ)) (v : Fin q → Nat) (j : Fin (features q alphabet).size) : ℚ :=
  SequentialCode.generatedFeatureValue v (features q alphabet)[j]
def freeColumn (q : Nat) (alphabet : Array (Nat × ℚ)) (source : Array ((Fin q → Nat) × ℚ)) :=
  IndependentSupport.sourceFreeColumn (features q alphabet).size (phi q alphabet) source

def guardMachine := BitMachineComposition.composition CylinderRawMatrixProducer.machine
  GaussMatrixPostloopMachines.decisionMachine
def guardCoefficient := OrdinaryPolynomialComposition.coefficient CylinderRawMatrixProducer.machine
  CylinderRawMatrixProducer.coefficient GaussRationalPostloop.decisionCoefficient GaussRationalPostloop.decisionExponent
def guardExponent := OrdinaryPolynomialComposition.degree CylinderRawMatrixProducer.exponent GaussRationalPostloop.decisionExponent
abbrev I := BitMachineCopy.bitMachine
abbrev B := CodeDRawDependentPass.machine
def machine := OrdinaryBitBranch.machine guardMachine I B
def clock (n : Nat) :=
  OrdinaryBitBranch.invocationBound guardMachine n (guardCoefficient*(n+1)^guardExponent)+
  OrdinaryBitBranch.invocationBound I n (2*(n+1)^1)+
  OrdinaryBitBranch.invocationBound B n (CodeDRawDependentPass.coefficient*(n+1)^CodeDRawDependentPass.exponent)+1

theorem invocation_polynomial (M : BitMachine.Machine) (a d : Nat) :
    PolynomialBound (fun _ n => OrdinaryBitBranch.invocationBound M n (a*(n+1)^d)) :=
  uniform_invocation M second (mul (constant a) (power (add second (constant 1)) d))

theorem clock_polynomial : PolynomialBound (fun _ n => clock n) :=
  add (add (add (invocation_polynomial guardMachine guardCoefficient guardExponent)
    (invocation_polynomial I 2 1))
    (invocation_polynomial B CodeDRawDependentPass.coefficient CodeDRawDependentPass.exponent)) (constant 1)
def coefficient := Classical.choose clock_polynomial
def exponent := Classical.choose (Classical.choose_spec clock_polynomial)
theorem clock_le (n : Nat) : clock n ≤ coefficient*(n+1)^exponent := by
  simpa only [Nat.zero_add] using (Classical.choose_spec (Classical.choose_spec clock_polynomial)) 0 n

theorem freeColumn_eq (q : Nat) (alphabet : Array (Nat × ℚ)) (source : Array ((Fin q → Nat) × ℚ)) :
    SequentialTotality.typedFree
      (GaussControlTrace.after (SequentialArrayBridge.matrixOfArray (cylinders q 8192 (alphabet.map Prod.fst) source))
        (SequentialCode.columnCount (cylinders q 8192 (alphabet.map Prod.fst) source))).pivots=
      freeColumn q alphabet source := by
  rw [(GaussControlTrace.after_exact _ _).2]
  rfl

theorem guard_outputs (q : Nat) (alphabet : Array (Nat × ℚ)) (source : Array ((Fin q → Nat) × ℚ)) :
    guardMachine.OutputsWithin (CylinderRawMatrixProducer.input alphabet source)
      [decide (freeColumn q alphabet source≠none)]
      (guardCoefficient*((CylinderRawMatrixProducer.input alphabet source).length+1)^guardExponent) := by
  have hg:=GaussRationalPostloop.decision_outputs
    (SequentialArrayBridge.matrixOfArray (cylinders q 8192 (alphabet.map Prod.fst) source))
    (CylinderWholeGauss.matrix_zero_one q 8192 (alphabet.map Prod.fst) source)
    (CodeDRawDependentPass.rows_pos q alphabet source)
  rw [freeColumn_eq,←CylinderGaussABI.cylinder_to_gauss_bytes q 8192 (alphabet.map Prod.fst) source] at hg
  exact OrdinaryPolynomialComposition.outputsWithin CylinderRawMatrixProducer.machine
    GaussMatrixPostloopMachines.decisionMachine (CylinderRawMatrixProducer.outputs_polynomial alphabet source) hg

theorem outputs_idle (q : Nat) (alphabet : Array (Nat × ℚ)) (source : Array ((Fin q → Nat) × ℚ))
    (hfree : freeColumn q alphabet source=none) :
    machine.OutputsWithin (CylinderRawMatrixProducer.input alphabet source)
      (CylinderRawMatrixProducer.input alphabet source)
      (coefficient*((CylinderRawMatrixProducer.input alphabet source).length+1)^exponent) := by
  let x:=CylinderRawMatrixProducer.input alphabet source
  have hg:=guard_outputs q alphabet source
  simp [hfree] at hg
  have hi : I.OutputsWithin x x (2*(x.length+1)^1) := by
    simpa only [pow_one] using BitMachineCopy.bitMachine_outputs x
  have h:=OrdinaryBitBranch.outputsWithin guardMachine I B x x false
    (guardCoefficient*(x.length+1)^guardExponent) (2*(x.length+1)^1) hg hi
  apply BitMachine.outputsWithin_mono machine h
  apply Nat.le_trans (m:=clock x.length) ?_ (clock_le x.length)
  change OrdinaryBitBranch.invocationBound guardMachine x.length (guardCoefficient*(x.length+1)^guardExponent)+
    OrdinaryBitBranch.invocationBound I x.length (2*(x.length+1)^1)+1≤clock x.length
  unfold clock
  omega

theorem outputs_dependent (q : Nat) (alphabet : Array (Nat × ℚ)) (source : Array ((Fin q → Nat) × ℚ))
    (hfree : freeColumn q alphabet source≠none)
    (cert : {c : Array ℚ // SequentialCode.IsDependence (cylinders q 8192 (alphabet.map Prod.fst) source) c})
    (hcert : MaterializedGauss.certifiedMaterializedDependence (cylinders q 8192 (alphabet.map Prod.fst) source)=some cert)
    (lambda : ℚ) (hmin : SequentialCode.minimumRatio (source.map Prod.snd) cert.val=some lambda)
    (hnonneg : (CodeDUpdatedArithmeticABI.candidateWeights source cert.val lambda).all (fun w => decide (0 ≤ w))=true) :
    let out:=CodeDCompactSequentialBridge.retainedSource source (CodeDUpdatedArithmeticABI.candidateWeights source cert.val lambda)
    machine.OutputsWithin (CylinderRawMatrixProducer.input alphabet source)
      (CylinderRawMatrixProducer.input alphabet out)
      (coefficient*((CylinderRawMatrixProducer.input alphabet source).length+1)^exponent) := by
  let x:=CylinderRawMatrixProducer.input alphabet source
  let out:=CodeDCompactSequentialBridge.retainedSource source (CodeDUpdatedArithmeticABI.candidateWeights source cert.val lambda)
  let y:=CylinderRawMatrixProducer.input alphabet out
  have hg:=guard_outputs q alphabet source
  simp [hfree] at hg
  have hd : SequentialTotality.typedFree
      (GaussControlTrace.after (SequentialArrayBridge.matrixOfArray (cylinders q 8192 (alphabet.map Prod.fst) source))
        (SequentialCode.columnCount (cylinders q 8192 (alphabet.map Prod.fst) source))).pivots≠none := by
    rw [freeColumn_eq]; exact hfree
  have hb:=CodeDRawDependentPass.outputs q alphabet source cert hcert hd lambda hmin hnonneg
  have h:=OrdinaryBitBranch.outputsWithin guardMachine I B x y true
    (guardCoefficient*(x.length+1)^guardExponent)
    (CodeDRawDependentPass.coefficient*(x.length+1)^CodeDRawDependentPass.exponent) hg hb
  apply BitMachine.outputsWithin_mono machine h
  apply Nat.le_trans (m:=clock x.length) ?_ (clock_le x.length)
  change OrdinaryBitBranch.invocationBound guardMachine x.length (guardCoefficient*(x.length+1)^guardExponent)+
    OrdinaryBitBranch.invocationBound B x.length (CodeDRawDependentPass.coefficient*(x.length+1)^CodeDRawDependentPass.exponent)+1≤clock x.length
  unfold clock
  omega

theorem outputs (q : Nat) (alphabet : Array (Nat × ℚ)) (source : Array ((Fin q → Nat) × ℚ))
    (hpositive : SequentialSourceCode.SourcePositive source) :
    machine.OutputsWithin (CylinderRawMatrixProducer.input alphabet source)
      (CylinderRawMatrixProducer.input alphabet
        (CodeDCompressionIteration.onePass (features q alphabet).size (phi q alphabet) source))
      (coefficient*((CylinderRawMatrixProducer.input alphabet source).length+1)^exponent) := by
  cases hf : freeColumn q alphabet source with
  | none =>
    have hp:=CodeDCompressionIteration.onePass_of_none (features q alphabet).size (phi q alphabet) source hf
    rw [hp]
    exact outputs_idle q alphabet source hf
  | some f =>
    obtain ⟨next,hs⟩:=IndependentSupport.compressSourceOnce_total_of_free
      (features q alphabet).size (phi q alphabet) source
      (SequentialSourceCode.generatedFeatures_pos q 8192 (alphabet.map Prod.fst))
      (SequentialSourceCode.generatedFeatures_constant q 8192 (alphabet.map Prod.fst)) ⟨f,hf⟩ hpositive
    obtain ⟨cert,hcert,lambda,hmin,hnonneg,hnext⟩:=
      CodeDMaterializedSuccessCertificate.successful_step_certificate (phi q alphabet) source next hs
    have hfree : freeColumn q alphabet source≠none := by rw [hf]; simp
    have hout:=outputs_dependent q alphabet source hfree cert hcert lambda hmin hnonneg
    rw [←hnext] at hout
    have hp:=CodeDCompressionIteration.onePass_of_step (features q alphabet).size (phi q alphabet) source next f hf hs
    rw [hp]
    exact hout

#print axioms guard_outputs
#print axioms outputs_idle
#print axioms outputs_dependent
#print axioms outputs
end
end CurrentAdditive.CodeDRawPass
