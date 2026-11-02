import CurrentAdditive.GenericCodeDInnerMachine
import CurrentAdditive.CodeDUniformStateBytes
import CurrentAdditive.CodeDAppendCoordinate

namespace CurrentAdditive.GenericCodeDCoordinateMachine
noncomputable section
variable (D : Nat)
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
open EthInapproximability.CurrentPaper GaussCellPolynomialClock
open CodeDUniformStateBytes

/-- This fixed program appends one coordinate, derives the new candidate count,
and executes that many actual compression passes. -/
def machine := BitMachineComposition.composition CodeDAppendCoordinate.machine (GenericCodeDInnerMachine.machine D)

def clock (L : Nat) :=
  CodeDAppendCoordinate.coefficient*(L+1)^CodeDAppendCoordinate.exponent+
  2*L+2+(GenericCodeDInnerMachine.coefficient D)*(L+1)^(GenericCodeDInnerMachine.exponent D)

theorem outputs (hD : 1 ≤ D) (alphabet : Array (Nat × ℚ))
    (hnonneg : alphabet.all (fun e => decide (0 ≤ e.2))=true)
    (hmass : SequentialCode.sourceMass alphabet=1)
    (Q j : Nat) (hj : j < Q) (L : Nat)
    (hcap : cap D Q alphabet ≤ L) :
    (machine D).OutputsWithin (outerState D alphabet j) (outerState D alphabet (j+1)) ((clock D) L) := by
  let alpha := LabelTrace.positiveLaw alphabet
  let start := sourceAt D alphabet j
  let source := source0 D alphabet j
  have hpos : SequentialSourceCode.SourcePositive source :=
    SequentialSourceCode.appendSource_positive start alpha
      (sourceAt_positive D alphabet j) (LabelTrace.positiveLaw_positive alphabet)
  have hbound : ∀ t ≤ source.size,
      (GenericCylinderRawMatrixProducer.input alpha ((GenericCodeDInnerMachine.current D) alpha source t)).length ≤ L := by
    intro t ht
    exact (inner_length_le D alphabet hnonneg hmass Q j hj t).trans hcap
  have hi := (GenericCodeDInnerMachine.outputs_bounded D hD) (j+1) alpha source hpos L hbound
  have ha := CodeDAppendCoordinate.outputs_polynomial alpha start
  have haBound : CodeDAppendCoordinate.coefficient*
      ((CodeDAppendCoordinate.input alpha start).length+1)^CodeDAppendCoordinate.exponent ≤
      CodeDAppendCoordinate.coefficient*(L+1)^CodeDAppendCoordinate.exponent := by
    gcongr
    exact (outer_length_le D alphabet hnonneg hmass Q j (by omega)).trans hcap
  have ha' := BitMachine.outputsWithin_mono _ ha haBound
  have h := BitMachineComposition.composition_outputsWithin _ _ ha' hi
  have hmiddle : (GenericCylinderRawMatrixProducer.input alpha source).length ≤ L := by
    simpa only [GenericCodeDInnerMachine.current,Function.iterate_zero,id_eq] using hbound 0 (Nat.zero_le _)
  have hmiddle' : (CodeDAppendCoordinate.input alpha (SequentialCode.appendSource start alpha)).length ≤ L := hmiddle
  have heq : GenericCylinderRawMatrixProducer.input alpha
      ((GenericCodeDInnerMachine.current D) alpha source source.size)=outerState D alphabet (j+1) := by
    unfold outerState
    rw [succ_iteration]
    rfl
  rw [heq] at h
  apply BitMachine.outputsWithin_mono _ h
  unfold clock
  omega

theorem clock_polynomial {f : Nat → Nat → Nat} (hf : PolynomialBound f) :
    PolynomialBound (fun s n => (clock D) (f s n)) := by
  exact add (add (add
    (mul (constant CodeDAppendCoordinate.coefficient)
      (power (add hf (constant 1)) CodeDAppendCoordinate.exponent))
    (mul (constant 2) hf)) (constant 2))
    (mul (constant (GenericCodeDInnerMachine.coefficient D))
      (power (add hf (constant 1)) (GenericCodeDInnerMachine.exponent D)))

#print axioms outputs
#print axioms clock_polynomial
end
end CurrentAdditive.GenericCodeDCoordinateMachine
