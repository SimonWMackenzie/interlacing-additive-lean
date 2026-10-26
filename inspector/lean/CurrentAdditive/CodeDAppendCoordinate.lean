import CurrentAdditive.AppendSourceTraversal
import CurrentAdditive.OrdinaryBankFork
import CurrentAdditive.CylinderRawInputProjection

/-! The physical outer coordinate extension for Code D. The ordinary input
contains the unary dimension, the weighted alphabet and the weighted source.
The same fixed machine retains the alphabet, writes the ordered appended
source, and increments the actual unary dimension. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace CurrentAdditive.CodeDAppendCoordinate
open EthInapproximability.CurrentPaper
open PhysicalProducer

def input {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) : List Bool :=
  CylinderRawInputProjection.input alphabet source

/-- A literal one-transition program prepends the next unary dimension bit. -/
def unarySuccessorMachine : BitMachine.Machine where
  stackCount := 1
  labelCount := 1
  controlCount := 1
  input := 0
  output := 0
  start := 0
  initial := 0
  program := fun _ => .push 0 (fun _ => true) .halt

theorem unary_successor_outputs (w : List Bool) :
    unarySuccessorMachine.OutputsWithin w (true :: w) 1 := by
  refine ⟨1, le_rfl, ?_, ?_⟩ <;> rfl

def unarySuccessor : Producer where
  machine := unarySuccessorMachine
  result := List.cons true
  coefficient := 1
  degree := 0
  outputs w := by simpa only [pow_zero, Nat.mul_one] using unary_successor_outputs w

def bank2 (A B : Producer) : Producer :=
  concat (compose A field) (compose B field)

def bank3 (A B C : Producer) : Producer :=
  concat (compose A field) (concat (compose B field) (compose C field))

theorem bank2_result (A B : Producer) (w : List Bool) :
    (bank2 A B).result w = BitMachineBankCodec.encode ![A.result w, B.result w] := by
  simp only [bank2, concat, compose, field, Function.comp_apply,
    BitMachineBankCodec.encode_eq_list, List.ofFn_succ, List.ofFn_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]

theorem bank3_result (A B C : Producer) (w : List Bool) :
    (bank3 A B C).result w =
      BitMachineBankCodec.encode ![A.result w, B.result w, C.result w] := by
  simp only [bank3, concat, compose, field, Function.comp_apply,
    BitMachineBankCodec.encode_eq_list, List.ofFn_succ, List.ofFn_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]

/-- The append worker physically receives the source and alphabet fields,
in its established order, by projecting the original three-field input. -/
def appendInput : Producer := bank2 (projection (2 : Fin 3)) (projection (1 : Fin 3))

theorem append_input_result {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    appendInput.result (input alphabet source) = BitMachineBankCodec.encode
      ![CodeDCanonicalSourceV2.encodedSource source, CodeDTargetV2.alphabetBytes alphabet] := by
  simp only [appendInput, bank2_result, input, CylinderRawInputProjection.input,
    projection, BankFieldProjection.result_encode, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]
  rfl

def appendCoefficient : Nat := Classical.choose AppendSourceTraversal.uniform_append
def appendExponent : Nat :=
  Classical.choose (Classical.choose_spec AppendSourceTraversal.uniform_append)

theorem append_outputs {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    AppendSourceTraversal.machine.OutputsWithin
      (BitMachineBankCodec.encode
        ![CodeDCanonicalSourceV2.encodedSource source, CodeDTargetV2.alphabetBytes alphabet])
      (CodeDCanonicalSourceV2.encodedSource (SequentialCode.appendSource source alphabet))
      (appendCoefficient * ((BitMachineBankCodec.encode
        ![CodeDCanonicalSourceV2.encodedSource source,
          CodeDTargetV2.alphabetBytes alphabet]).length + 1)^appendExponent) :=
  Classical.choose_spec (Classical.choose_spec AppendSourceTraversal.uniform_append)
    q source alphabet

def appendMachine : BitMachine.Machine :=
  BitMachineComposition.composition appendInput.machine AppendSourceTraversal.machine
def branchCoefficient : Nat := AppendNestedPolynomial.composeCoefficient
  appendInput.machine appendInput.coefficient appendCoefficient appendExponent
def branchExponent : Nat :=
  AppendNestedPolynomial.composeDegree appendInput.degree appendExponent

theorem branch_outputs {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    appendMachine.OutputsWithin (input alphabet source)
      (CodeDCanonicalSourceV2.encodedSource (SequentialCode.appendSource source alphabet))
      (branchCoefficient * ((input alphabet source).length + 1)^branchExponent) := by
  have h := appendInput.outputs (input alphabet source)
  rw [append_input_result] at h
  exact AppendNestedPolynomial.compose_outputs _ _ _ _ _ _ _ _ _ h (append_outputs alphabet source)

def forkMachine : BitMachine.Machine :=
  OrdinaryBankFork.machine BitMachineCopy.bitMachine appendMachine
def forkCoefficient : Nat :=
  OrdinaryBankFork.coefficient BitMachineCopy.bitMachine appendMachine 2 branchCoefficient
def forkExponent : Nat := OrdinaryBankFork.degree 1 branchExponent

theorem fork_outputs {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    forkMachine.OutputsWithin (input alphabet source)
      (OrdinaryBankFork.packet (input alphabet source)
        (CodeDCanonicalSourceV2.encodedSource (SequentialCode.appendSource source alphabet)))
      (forkCoefficient * ((input alphabet source).length + 1)^forkExponent) := by
  have hc := BitMachineCopy.bitMachine_computes (input alphabet source)
  have h := OrdinaryBankFork.outputsWithin BitMachineCopy.bitMachine appendMachine
    hc (branch_outputs alphabet source)
  apply BitMachine.outputsWithin_mono _ h
  simpa only [forkCoefficient, forkExponent, pow_one] using
    OrdinaryBankFork.clock_le_polynomial BitMachineCopy.bitMachine appendMachine
      (input alphabet source).length 2 1 branchCoefficient branchExponent

def nested (i : Fin 3) : Producer :=
  compose (projection (0 : Fin 2)) (projection i)
def last : Producer := projection (1 : Fin 2)
def finish : Producer := bank3 (compose (nested 0) unarySuccessor) (nested 1) last

theorem nested_result (i : Fin 3) (w : Fin 3 → List Bool) (bits : List Bool) :
    (nested i).result (OrdinaryBankFork.packet (BitMachineBankCodec.encode w) bits) = w i := by
  simp only [nested, compose, projection, Function.comp_apply, OrdinaryBankFork.packet,
    BankFieldProjection.result_encode, Matrix.cons_val_zero]

theorem finish_result {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    finish.result (OrdinaryBankFork.packet (input alphabet source)
      (CodeDCanonicalSourceV2.encodedSource (SequentialCode.appendSource source alphabet))) =
      input alphabet (SequentialCode.appendSource source alphabet) := by
  simp only [finish, bank3_result, compose, Function.comp_apply, input,
    CylinderRawInputProjection.input, nested, compose, Function.comp_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, unarySuccessor, last, projection,
    OrdinaryBankFork.packet, BankFieldProjection.result_encode, List.replicate_succ]

def machine : BitMachine.Machine := BitMachineComposition.composition forkMachine finish.machine
def coefficient : Nat := AppendNestedPolynomial.composeCoefficient
  forkMachine forkCoefficient finish.coefficient finish.degree
def exponent : Nat := AppendNestedPolynomial.composeDegree forkExponent finish.degree

/-- The fixed physical machine updates the actual dimension header and
serializes the ordered append of the original indexed source and alphabet.
The polynomial is measured in the original input bytes, uniformly in all
typed arrays, including repetitions and arbitrary rational weights. -/
theorem outputs_polynomial {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    machine.OutputsWithin (input alphabet source)
      (input alphabet (SequentialCode.appendSource source alphabet))
      (coefficient * ((input alphabet source).length + 1)^exponent) := by
  have hf := finish.outputs (OrdinaryBankFork.packet (input alphabet source)
    (CodeDCanonicalSourceV2.encodedSource (SequentialCode.appendSource source alphabet)))
  rw [finish_result] at hf
  exact AppendNestedPolynomial.compose_outputs _ _ _ _ _ _ _ _ _
    (fork_outputs alphabet source) hf

#print axioms outputs_polynomial
end CurrentAdditive.CodeDAppendCoordinate
