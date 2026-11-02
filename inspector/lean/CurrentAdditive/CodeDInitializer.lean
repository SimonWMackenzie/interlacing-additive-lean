import CurrentAdditive.CodeDAlphabetCompact
import CurrentAdditive.CodeDSeedLayout
import CurrentAdditive.ContextualInvokePolynomial
import CurrentAdditive.RatioUpdaterPolynomial

/-! A fixed raw initializer: actual zero filtering, a finite seed printer,
and retention of the original unary count as outer iteration fuel. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384
namespace CurrentAdditive.CodeDInitializer
open EthInapproximability.CurrentPaper BitMachineBankCodec
open CodeDTargetV2 LabelTrace

def input (Q : Nat) (alphabet : Array (Nat × ℚ)) :=
  encode ![List.replicate Q true,alphabetBytes alphabet]

def rawState0 (alphabet : Array (Nat × ℚ)) :=
  CodeDSeedLayout.state (alphabetBytes (positiveLaw alphabet))

def output (Q : Nat) (alphabet : Array (Nat × ℚ)) :=
  encode ![rawState0 alphabet,List.replicate Q true]

noncomputable def machine : BitMachine.Machine :=
  BitMachineComposition.composition (ContextualInvoke.machine CodeDCompactJoinV2.machine)
    CodeDSeedLayout.producer.machine

noncomputable def filterClock (alphabet : Array (Nat × ℚ)) :=
  CodeDCompactJoinV2.clock (alphabet.toList.map alphabetEntry)

noncomputable def contextualClock (Q : Nat) (alphabet : Array (Nat × ℚ)) :=
  ContextualInvoke.clock CodeDCompactJoinV2.machine (List.replicate Q true)
    (alphabetBytes alphabet) (alphabetBytes (positiveLaw alphabet)) (filterClock alphabet)

noncomputable def clock (Q : Nat) (alphabet : Array (Nat × ℚ)) :=
  let middle := ContextualInvoke.output (List.replicate Q true) (alphabetBytes (positiveLaw alphabet))
  contextualClock Q alphabet + 2*middle.length+2+
    CodeDSeedLayout.producer.coefficient*(middle.length+1)^CodeDSeedLayout.producer.degree

theorem contextual_outputs (Q : Nat) (alphabet : Array (Nat × ℚ))
    (hnonneg : alphabet.all (fun e => decide (0 ≤ e.2))=true) :
    (ContextualInvoke.machine CodeDCompactJoinV2.machine).OutputsWithin (input Q alphabet)
      (ContextualInvoke.output (List.replicate Q true) (alphabetBytes (positiveLaw alphabet)))
      (contextualClock Q alphabet) :=
  ContextualInvoke.outputs CodeDCompactJoinV2.machine _ _ _ _ (CodeDAlphabetCompact.outputs alphabet hnonneg)

theorem outputs (Q : Nat) (alphabet : Array (Nat × ℚ))
    (hnonneg : alphabet.all (fun e => decide (0 ≤ e.2))=true) :
    machine.OutputsWithin (input Q alphabet) (output Q alphabet) (clock Q alphabet) := by
  have hA := contextual_outputs Q alphabet hnonneg
  have hB := CodeDSeedLayout.outputs (List.replicate Q true) (alphabetBytes (positiveLaw alphabet))
  exact BitMachineComposition.composition_outputsWithin _ _ hA hB

/-- The same fixed initializer has one polynomial in its literal original
packet length. Its only data promise is nonnegative alphabet weights. -/
theorem uniform : ∃ C E : Nat, ∀ (Q : Nat) (alphabet : Array (Nat × ℚ)),
    alphabet.all (fun e => decide (0 ≤ e.2))=true →
    machine.OutputsWithin (input Q alphabet) (output Q alphabet)
      (C*((input Q alphabet).length+1)^E) := by
  obtain ⟨a,e,hcap⟩ := RatioUpdaterPolynomial.compact_clock_poly
  let M := ContextualInvoke.machine CodeDCompactJoinV2.machine
  let cf := ContextualInvoke.polynomialCoefficient CodeDCompactJoinV2.machine a
  let df := e+1
  let cg := CodeDSeedLayout.producer.coefficient
  let dg := CodeDSeedLayout.producer.degree
  refine ⟨cf+2*(cf*M.pushBound+1)+cg*(cf*M.pushBound+1)^dg,(df+1)*(dg+1),?_⟩
  intro Q alphabet hn
  have hcomp := CodeDAlphabetCompact.outputs alphabet hn
  have hT := hcap (alphabet.toList.map alphabetEntry)
  have hsmall : CodeDCompactJoinV2.machine.OutputsWithin (alphabetBytes alphabet)
      (alphabetBytes (positiveLaw alphabet)) (a*((alphabetBytes alphabet).length+1)^e) :=
    BitMachine.outputsWithin_mono _ hcomp hT
  have hA := ContextualInvoke.outputs_polynomial CodeDCompactJoinV2.machine a e
    (List.replicate Q true) (alphabetBytes alphabet) (alphabetBytes (positiveLaw alphabet)) hsmall
  have hB := CodeDSeedLayout.outputs (List.replicate Q true) (alphabetBytes (positiveLaw alphabet))
  have h := BitMachineComposition.composition_outputsWithin _ _ hA hB
  apply BitMachine.outputsWithin_mono _ h
  exact BitMachineCompositionArithmetic.composition_time_bound (input Q alphabet).length
    cf df cg dg M.pushBound
    (ContextualInvoke.output (List.replicate Q true) (alphabetBytes (positiveLaw alphabet))).length
    (BitMachine.output_length_bound M hA)

#print axioms outputs
#print axioms uniform
end CurrentAdditive.CodeDInitializer
