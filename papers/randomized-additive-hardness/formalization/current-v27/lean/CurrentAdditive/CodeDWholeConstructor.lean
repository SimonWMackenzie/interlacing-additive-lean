import CurrentAdditive.CodeDCoordinateMachine
import CurrentAdditive.CodeDInitializer
import CurrentAdditive.IndexedConstructor

namespace CurrentAdditive.CodeDWholeConstructor
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
open EthInapproximability.CurrentPaper GaussCellPolynomialClock
open CodeDUniformStateBytes

abbrev Step := CodeDCoordinateMachine.machine
abbrev Print := BankFieldProjection.machine (2 : Fin 3)
def runMachine := BitMachineComposition.composition CodeDInitializer.machine (OrdinaryIterationPacket.machine Step)
def machine := BitMachineComposition.composition runMachine Print
def input := CodeDInitializer.input
def result (Q : Nat) (alphabet : Array (Nat × ℚ)) :=
  CodeDCanonicalSourceV2.encodedSource (sourceAt 8192 alphabet Q)

def initializeCoefficient := Classical.choose CodeDInitializer.uniform
def initializeExponent := Classical.choose (Classical.choose_spec CodeDInitializer.uniform)
def stateCap (n : Nat) := n+CodeDUniformStateBytes.coefficient 8192*(n+1)^CodeDUniformStateBytes.exponent 8192
def loopPacketCap (L : Nat) := CodeDInnerMachine.packetLength L L
def loopClock (L : Nat) :=
  5*(loopPacketCap L+1)+L*BitMachineIteration.roundBound Step L (CodeDCoordinateMachine.clock L)+2
def clock (L : Nat) :=
  initializeCoefficient*(L+1)^initializeExponent+2*loopPacketCap L+2+loopClock L+
  2*L+2+10*(L+1)

theorem initial_packet (Q : Nat) (alphabet : Array (Nat × ℚ)) :
    CodeDInitializer.output Q alphabet=
      BitMachineBankCodec.encode ![outerState 8192 alphabet 0,List.replicate Q true] := rfl

theorem dimension_le_input (Q : Nat) (alphabet : Array (Nat × ℚ)) : Q ≤ (input Q alphabet).length := by
  simpa only [input,CodeDInitializer.input,Matrix.cons_val_zero,List.length_replicate] using
    BitMachineBankCodec.word_length_le_encode
      (![List.replicate Q true,CodeDTargetV2.alphabetBytes alphabet]) (0 : Fin 2)

/-- A whole physical execution: actual zero filtering and seed, the literal
outer count, every actual source-count compression loop, and final projection.
The only promises concern the original alphabet's nonnegative unit mass. -/
theorem outputs_capped (Q : Nat) (alphabet : Array (Nat × ℚ))
    (hnonneg : alphabet.all (fun e => decide (0 ≤ e.2))=true)
    (hmass : SequentialCode.sourceMass alphabet=1) :
    machine.OutputsWithin (input Q alphabet) (result Q alphabet)
      (clock (stateCap (input Q alphabet).length)) := by
  let N := (input Q alphabet).length
  let L := stateCap N
  have hN : N ≤ L := Nat.le_add_right _ _
  have hcap : cap 8192 Q alphabet ≤ L := Nat.le_add_left _ _
  have hQ : Q ≤ L := (dimension_le_input Q alphabet).trans hN
  have houter (j : Nat) (hj : j ≤ Q) : (outerState 8192 alphabet j).length ≤ L :=
    (outer_length_le 8192 alphabet hnonneg hmass Q j hj).trans hcap
  have hstep : ∀ j < (List.replicate Q true).length,
      Step.OutputsWithin (outerState 8192 alphabet j) (outerState 8192 alphabet (j+1))
        (CodeDCoordinateMachine.clock L) := by
    intro j hj
    exact CodeDCoordinateMachine.outputs alphabet hnonneg hmass Q j (by simpa only [List.length_replicate] using hj) L hcap
  have hlen : ∀ j < (List.replicate Q true).length,(outerState 8192 alphabet j).length ≤ L := by
    intro j hj
    exact houter j (by simp only [List.length_replicate] at hj;omega)
  have hl := OrdinaryIterationPacket.outputsWithin Step (outerState 8192 alphabet)
    (List.replicate Q true) L (CodeDCoordinateMachine.clock L) hstep hlen
  rw [List.length_replicate,←initial_packet] at hl
  have hpacket : (CodeDInitializer.output Q alphabet).length ≤ loopPacketCap L := by
    rw [initial_packet,CodeDInnerMachine.packet_length]
    unfold loopPacketCap CodeDInnerMachine.packetLength
    have h0:=houter 0 (Nat.zero_le _)
    omega
  have hl' : (OrdinaryIterationPacket.machine Step).OutputsWithin
      (CodeDInitializer.output Q alphabet) (outerState 8192 alphabet Q) (loopClock L) := by
    apply BitMachine.outputsWithin_mono _ hl
    unfold loopClock
    gcongr
  have hi := (Classical.choose_spec (Classical.choose_spec CodeDInitializer.uniform)) Q alphabet hnonneg
  have hi' : CodeDInitializer.machine.OutputsWithin (input Q alphabet) (CodeDInitializer.output Q alphabet)
      (initializeCoefficient*(L+1)^initializeExponent) := by
    apply BitMachine.outputsWithin_mono _ hi
    change initializeCoefficient*(N+1)^initializeExponent ≤ _
    gcongr
  have hr := BitMachineComposition.composition_outputsWithin _ _ hi' hl'
  have hp : Print.OutputsWithin (outerState 8192 alphabet Q) (result Q alphabet)
      (10*(L+1)) := by
    have h := BankFieldProjection.outputs (2 : Fin 3) (outerState 8192 alphabet Q)
    have he : BankFieldProjection.result (2 : Fin 3) (outerState 8192 alphabet Q)=result Q alphabet := by
      simp only [outerState,rawPacket,BankFieldProjection.result_encode,Matrix.cons_val_two,result]
      rfl
    rw [he] at h
    apply BitMachine.outputsWithin_mono _ h
    have hh:=houter Q (Nat.le_refl _)
    omega
  have h := BitMachineComposition.composition_outputsWithin _ _ hr hp
  apply BitMachine.outputsWithin_mono _ h
  change _ ≤ clock L
  unfold clock
  have hh:=houter Q (Nat.le_refl _)
  omega

theorem clock_polynomial : PolynomialBound (fun _ n => clock (stateCap n)) := by
  have hb := add second (mul (constant (CodeDUniformStateBytes.coefficient 8192))
    (power (add second (constant 1)) (CodeDUniformStateBytes.exponent 8192)))
  have hp := add (mul (constant 2) (add hb hb)) (constant 2)
  have ht := CodeDCoordinateMachine.clock_polynomial hb
  have hr := add (add (add ht (mul (constant (Step.stackCount+2))
    (add hb (mul ht (constant Step.pushBound))))) (constant Step.stackCount)) (constant 4)
  have hl := add (add (mul (constant 5) (add hp (constant 1))) (mul hb hr)) (constant 2)
  have hi := mul (constant initializeCoefficient) (power (add hb (constant 1)) initializeExponent)
  simpa only [clock,loopClock,loopPacketCap,stateCap,CodeDInnerMachine.packetLength,
    BitMachineIteration.roundBound] using
    add (add (add (add (add (add hi (mul (constant 2) hp)) (constant 2)) hl)
      (mul (constant 2) hb)) (constant 2)) (mul (constant 10) (add hb (constant 1)))

def coefficient := Classical.choose clock_polynomial
def exponent := Classical.choose (Classical.choose_spec clock_polynomial)

/-- One fixed machine and one polynomial, chosen before every original input,
print the exact ordered rational source of the independent-support constructor. -/
theorem outputs_polynomial (Q : Nat) (alphabet : Array (Nat × ℚ))
    (hnonneg : alphabet.all (fun e => decide (0 ≤ e.2))=true)
    (hmass : SequentialCode.sourceMass alphabet=1) :
    machine.OutputsWithin (input Q alphabet) (result Q alphabet)
      (coefficient*((input Q alphabet).length+1)^exponent) := by
  apply BitMachine.outputsWithin_mono _ (outputs_capped Q alphabet hnonneg hmass)
  simpa only [Nat.zero_add] using
    (Classical.choose_spec (Classical.choose_spec clock_polynomial)) 0 (input Q alphabet).length

theorem successful_outputs (Q : Nat) (alphabet : Array (Nat × ℚ))
    (hnonneg : alphabet.all (fun e => decide (0 ≤ e.2))=true)
    (hmass : SequentialCode.sourceMass alphabet=1)
    (out : Array ((Fin Q → Nat) × ℚ))
    (hout : LabelTrace.sequentialPreprocessed 8192 alphabet Q=some out) :
    machine.OutputsWithin (input Q alphabet) (CodeDCanonicalSourceV2.encodedSource out)
      (coefficient*((input Q alphabet).length+1)^exponent) := by
  have he : sourceAt 8192 alphabet Q=out := Option.some.inj ((sourceAt_some 8192 alphabet Q).symm.trans hout)
  simpa only [result,he] using outputs_polynomial Q alphabet hnonneg hmass

/-- The physical output is the same indexed array used by every functional
generated-table call, including its original positions and rational weights. -/
theorem indexed_outputs {m : Nat} (mu : Fin m → ℚ)
    (hnonneg : ∀ i,0 ≤ mu i) (hmass : ∑ i,mu i=1) (Q : Nat) :
    machine.OutputsWithin (input Q (IndexedLaw.indexedAlphabet mu))
      (CodeDCanonicalSourceV2.encodedSource (IndexedLaw.construct 8192 mu Q))
      (coefficient*((input Q (IndexedLaw.indexedAlphabet mu)).length+1)^exponent) :=
  successful_outputs Q (IndexedLaw.indexedAlphabet mu)
    (IndexedLaw.indexedAlphabet_nonnegative mu hnonneg) (by simpa using hmass)
    (IndexedLaw.construct 8192 mu Q) (IndexedLaw.construct_success 8192 mu Q)

#print axioms outputs_capped
#print axioms clock_polynomial
#print axioms outputs_polynomial
#print axioms successful_outputs
#print axioms indexed_outputs
end
end CurrentAdditive.CodeDWholeConstructor
