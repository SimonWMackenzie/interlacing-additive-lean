import CurrentAdditive.GenericCodeDCoordinateMachine
import CurrentAdditive.CodeDInitializer
import CurrentAdditive.IndexedConstructor

namespace CurrentAdditive.GenericCodeDWholeConstructor
noncomputable section
variable (D : Nat)
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
open EthInapproximability.CurrentPaper GaussCellPolynomialClock
open CodeDUniformStateBytes

abbrev Step := (GenericCodeDCoordinateMachine.machine D)
abbrev Print := BankFieldProjection.machine (2 : Fin 3)
def runMachine := BitMachineComposition.composition CodeDInitializer.machine (OrdinaryIterationPacket.machine (Step D))
def machine := BitMachineComposition.composition (runMachine D) Print
def input := CodeDInitializer.input
def result (Q : Nat) (alphabet : Array (Nat × ℚ)) :=
  CodeDCanonicalSourceV2.encodedSource (sourceAt D alphabet Q)

def initializeCoefficient := Classical.choose CodeDInitializer.uniform
def initializeExponent := Classical.choose (Classical.choose_spec CodeDInitializer.uniform)
def stateCap (n : Nat) := n+CodeDUniformStateBytes.coefficient D*(n+1)^CodeDUniformStateBytes.exponent D
def loopPacketCap (L : Nat) := GenericCodeDInnerMachine.packetLength L L
def loopClock (L : Nat) :=
  5*(loopPacketCap L+1)+L*BitMachineIteration.roundBound (Step D) L ((GenericCodeDCoordinateMachine.clock D) L)+2
def clock (L : Nat) :=
  initializeCoefficient*(L+1)^initializeExponent+2*loopPacketCap L+2+(loopClock D) L+
  2*L+2+10*(L+1)

theorem initial_packet (Q : Nat) (alphabet : Array (Nat × ℚ)) :
    CodeDInitializer.output Q alphabet=
      BitMachineBankCodec.encode ![outerState D alphabet 0,List.replicate Q true] := rfl

theorem dimension_le_input (Q : Nat) (alphabet : Array (Nat × ℚ)) : Q ≤ (input Q alphabet).length := by
  simpa only [input,CodeDInitializer.input,Matrix.cons_val_zero,List.length_replicate] using
    BitMachineBankCodec.word_length_le_encode
      (![List.replicate Q true,CodeDTargetV2.alphabetBytes alphabet]) (0 : Fin 2)

/-- A whole physical execution: actual zero filtering and seed, the literal
outer count, every actual source-count compression loop, and final projection.
The only promises concern the original alphabet's nonnegative unit mass. -/
theorem outputs_capped (hD : 1 ≤ D) (Q : Nat) (alphabet : Array (Nat × ℚ))
    (hnonneg : alphabet.all (fun e => decide (0 ≤ e.2))=true)
    (hmass : SequentialCode.sourceMass alphabet=1) :
    (machine D).OutputsWithin (input Q alphabet) ((result D) Q alphabet)
      ((clock D) ((stateCap D) (input Q alphabet).length)) := by
  let N := (input Q alphabet).length
  let L := (stateCap D) N
  have hN : N ≤ L := Nat.le_add_right _ _
  have hcap : cap D Q alphabet ≤ L := Nat.le_add_left _ _
  have hQ : Q ≤ L := (dimension_le_input Q alphabet).trans hN
  have houter (j : Nat) (hj : j ≤ Q) : (outerState D alphabet j).length ≤ L :=
    (outer_length_le D alphabet hnonneg hmass Q j hj).trans hcap
  have hstep : ∀ j < (List.replicate Q true).length,
      (Step D).OutputsWithin (outerState D alphabet j) (outerState D alphabet (j+1))
        ((GenericCodeDCoordinateMachine.clock D) L) := by
    intro j hj
    exact (GenericCodeDCoordinateMachine.outputs D hD) alphabet hnonneg hmass Q j (by simpa only [List.length_replicate] using hj) L hcap
  have hlen : ∀ j < (List.replicate Q true).length,(outerState D alphabet j).length ≤ L := by
    intro j hj
    exact houter j (by simp only [List.length_replicate] at hj;omega)
  have hl := OrdinaryIterationPacket.outputsWithin (Step D) (outerState D alphabet)
    (List.replicate Q true) L ((GenericCodeDCoordinateMachine.clock D) L) hstep hlen
  rw [List.length_replicate,←(initial_packet D)] at hl
  have hpacket : (CodeDInitializer.output Q alphabet).length ≤ loopPacketCap L := by
    rw [(initial_packet D),GenericCodeDInnerMachine.packet_length]
    unfold loopPacketCap GenericCodeDInnerMachine.packetLength
    have h0:=houter 0 (Nat.zero_le _)
    omega
  have hl' : (OrdinaryIterationPacket.machine (Step D)).OutputsWithin
      (CodeDInitializer.output Q alphabet) (outerState D alphabet Q) ((loopClock D) L) := by
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
  have hp : Print.OutputsWithin (outerState D alphabet Q) ((result D) Q alphabet)
      (10*(L+1)) := by
    have h := BankFieldProjection.outputs (2 : Fin 3) (outerState D alphabet Q)
    have he : BankFieldProjection.result (2 : Fin 3) (outerState D alphabet Q)=(result D) Q alphabet := by
      simp only [outerState,rawPacket,BankFieldProjection.result_encode,Matrix.cons_val_two,result]
      rfl
    rw [he] at h
    apply BitMachine.outputsWithin_mono _ h
    have hh:=houter Q (Nat.le_refl _)
    omega
  have h := BitMachineComposition.composition_outputsWithin _ _ hr hp
  apply BitMachine.outputsWithin_mono _ h
  change _ ≤ (clock D) L
  unfold clock
  have hh:=houter Q (Nat.le_refl _)
  omega

theorem clock_polynomial : PolynomialBound (fun _ n => (clock D) ((stateCap D) n)) := by
  have hb := add second (mul (constant (CodeDUniformStateBytes.coefficient D))
    (power (add second (constant 1)) (CodeDUniformStateBytes.exponent D)))
  have hp := add (mul (constant 2) (add hb hb)) (constant 2)
  have ht := (GenericCodeDCoordinateMachine.clock_polynomial D) hb
  have hr := add (add (add ht (mul (constant ((Step D).stackCount+2))
    (add hb (mul ht (constant ((Step D).pushBound)))))) (constant ((Step D).stackCount))) (constant 4)
  have hl := add (add (mul (constant 5) (add hp (constant 1))) (mul hb hr)) (constant 2)
  have hi := mul (constant initializeCoefficient) (power (add hb (constant 1)) initializeExponent)
  simpa only [clock,loopClock,loopPacketCap,stateCap,GenericCodeDInnerMachine.packetLength,
    BitMachineIteration.roundBound] using
    add (add (add (add (add (add hi (mul (constant 2) hp)) (constant 2)) hl)
      (mul (constant 2) hb)) (constant 2)) (mul (constant 10) (add hb (constant 1)))

def coefficient := Classical.choose (clock_polynomial D)
def exponent := Classical.choose (Classical.choose_spec (clock_polynomial D))

/-- One fixed (machine D) and one polynomial, chosen before every original input,
print the exact ordered rational source of the independent-support constructor. -/
theorem outputs_polynomial (hD : 1 ≤ D) (Q : Nat) (alphabet : Array (Nat × ℚ))
    (hnonneg : alphabet.all (fun e => decide (0 ≤ e.2))=true)
    (hmass : SequentialCode.sourceMass alphabet=1) :
    (machine D).OutputsWithin (input Q alphabet) ((result D) Q alphabet)
      ((coefficient D)*((input Q alphabet).length+1)^(exponent D)) := by
  apply BitMachine.outputsWithin_mono _ ((outputs_capped D hD) Q alphabet hnonneg hmass)
  simpa only [Nat.zero_add] using
    (Classical.choose_spec (Classical.choose_spec (clock_polynomial D))) 0 (input Q alphabet).length

theorem successful_outputs (hD : 1 ≤ D) (Q : Nat) (alphabet : Array (Nat × ℚ))
    (hnonneg : alphabet.all (fun e => decide (0 ≤ e.2))=true)
    (hmass : SequentialCode.sourceMass alphabet=1)
    (out : Array ((Fin Q → Nat) × ℚ))
    (hout : LabelTrace.sequentialPreprocessed D alphabet Q=some out) :
    (machine D).OutputsWithin (input Q alphabet) (CodeDCanonicalSourceV2.encodedSource out)
      ((coefficient D)*((input Q alphabet).length+1)^(exponent D)) := by
  have he : sourceAt D alphabet Q=out := Option.some.inj ((sourceAt_some D alphabet Q).symm.trans hout)
  simpa only [result,he] using (outputs_polynomial D hD) Q alphabet hnonneg hmass

/-- The physical output is the same indexed array used by every functional
generated-table call, including its original positions and rational weights. -/
theorem indexed_outputs (hD : 1 ≤ D) {m : Nat} (mu : Fin m → ℚ)
    (hnonneg : ∀ i,0 ≤ mu i) (hmass : ∑ i,mu i=1) (Q : Nat) :
    (machine D).OutputsWithin (input Q (IndexedLaw.indexedAlphabet mu))
      (CodeDCanonicalSourceV2.encodedSource (IndexedLaw.construct D mu Q))
      ((coefficient D)*((input Q (IndexedLaw.indexedAlphabet mu)).length+1)^(exponent D)) :=
  (successful_outputs D hD) Q (IndexedLaw.indexedAlphabet mu)
    (IndexedLaw.indexedAlphabet_nonnegative mu hnonneg) (by simpa using hmass)
    (IndexedLaw.construct D mu Q) (IndexedLaw.construct_success D mu Q)

/-- The program and polynomial are fixed after choosing the depth, before
every coordinate count and every original alphabet. -/
theorem uniform_outputs (hD : 1 ≤ D) : ∃ C E : Nat,
    ∀ (Q : Nat) (alphabet : Array (Nat × ℚ)),
      alphabet.all (fun e => decide (0 ≤ e.2))=true →
      SequentialCode.sourceMass alphabet=1 →
      (machine D).OutputsWithin (input Q alphabet) ((result D) Q alphabet)
        (C*((input Q alphabet).length+1)^E) :=
  ⟨coefficient D,exponent D,outputs_polynomial D hD⟩

#print axioms outputs_capped
#print axioms clock_polynomial
#print axioms outputs_polynomial
#print axioms successful_outputs
#print axioms indexed_outputs
#print axioms uniform_outputs
end
end CurrentAdditive.GenericCodeDWholeConstructor
