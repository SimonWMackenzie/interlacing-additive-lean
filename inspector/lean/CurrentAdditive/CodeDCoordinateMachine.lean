import CurrentAdditive.CodeDInnerMachine
import CurrentAdditive.CodeDUniformStateBytes
import CurrentAdditive.CodeDAppendCoordinate

namespace CurrentAdditive.CodeDCoordinateMachine
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
open EthInapproximability.CurrentPaper GaussCellPolynomialClock
open CodeDUniformStateBytes

/-- This fixed program appends one coordinate, derives the new candidate count,
and executes that many actual compression passes. -/
def machine := BitMachineComposition.composition CodeDAppendCoordinate.machine CodeDInnerMachine.machine

def clock (L : Nat) :=
  CodeDAppendCoordinate.coefficient*(L+1)^CodeDAppendCoordinate.exponent+
  2*L+2+CodeDInnerMachine.coefficient*(L+1)^CodeDInnerMachine.exponent

theorem outputs (alphabet : Array (Nat × ℚ))
    (hnonneg : alphabet.all (fun e => decide (0 ≤ e.2))=true)
    (hmass : SequentialCode.sourceMass alphabet=1)
    (Q j : Nat) (hj : j < Q) (L : Nat)
    (hcap : cap 8192 Q alphabet ≤ L) :
    machine.OutputsWithin (outerState 8192 alphabet j) (outerState 8192 alphabet (j+1)) (clock L) := by
  let alpha := LabelTrace.positiveLaw alphabet
  let start := sourceAt 8192 alphabet j
  let source := source0 8192 alphabet j
  have hpos : SequentialSourceCode.SourcePositive source :=
    SequentialSourceCode.appendSource_positive start alpha
      (sourceAt_positive 8192 alphabet j) (LabelTrace.positiveLaw_positive alphabet)
  have hbound : ∀ t ≤ source.size,
      (CylinderRawMatrixProducer.input alpha (CodeDInnerMachine.current alpha source t)).length ≤ L := by
    intro t ht
    exact (inner_length_le 8192 alphabet hnonneg hmass Q j hj t).trans hcap
  have hi := CodeDInnerMachine.outputs_bounded (j+1) alpha source hpos L hbound
  have ha := CodeDAppendCoordinate.outputs_polynomial alpha start
  have haBound : CodeDAppendCoordinate.coefficient*
      ((CodeDAppendCoordinate.input alpha start).length+1)^CodeDAppendCoordinate.exponent ≤
      CodeDAppendCoordinate.coefficient*(L+1)^CodeDAppendCoordinate.exponent := by
    gcongr
    exact (outer_length_le 8192 alphabet hnonneg hmass Q j (by omega)).trans hcap
  have ha' := BitMachine.outputsWithin_mono _ ha haBound
  have h := BitMachineComposition.composition_outputsWithin _ _ ha' hi
  have hmiddle : (CylinderRawMatrixProducer.input alpha source).length ≤ L := by
    simpa only [CodeDInnerMachine.current,Function.iterate_zero,id_eq] using hbound 0 (Nat.zero_le _)
  have hmiddle' : (CodeDAppendCoordinate.input alpha (SequentialCode.appendSource start alpha)).length ≤ L := hmiddle
  have heq : CylinderRawMatrixProducer.input alpha
      (CodeDInnerMachine.current alpha source source.size)=outerState 8192 alphabet (j+1) := by
    unfold outerState
    rw [succ_iteration]
    rfl
  rw [heq] at h
  apply BitMachine.outputsWithin_mono _ h
  unfold clock
  omega

theorem clock_polynomial {f : Nat → Nat → Nat} (hf : PolynomialBound f) :
    PolynomialBound (fun s n => clock (f s n)) := by
  exact add (add (add
    (mul (constant CodeDAppendCoordinate.coefficient)
      (power (add hf (constant 1)) CodeDAppendCoordinate.exponent))
    (mul (constant 2) hf)) (constant 2))
    (mul (constant CodeDInnerMachine.coefficient)
      (power (add hf (constant 1)) CodeDInnerMachine.exponent))

#print axioms outputs
#print axioms clock_polynomial
end
end CurrentAdditive.CodeDCoordinateMachine
