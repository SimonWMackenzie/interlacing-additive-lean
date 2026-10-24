import CurrentAdditive.CylinderProductionProjectionClock
import EthInapproximability.CurrentPaper.BitMachineComposition

/-! Actual preparation from Code D's three-field production input. Each
projection reads the original packet, rather than accepting projected labels
or tuples as an input promise. Indexed order and repetitions are retained. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace CurrentAdditive.CylinderRawInputProjection

open EthInapproximability.CurrentPaper
open CurrentAdditive.CylinderProductionProjection

def input {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) : List Bool :=
  BitMachineBankCodec.encode
    ![List.replicate q true,CodeDTargetV2.alphabetBytes alphabet,
      CodeDCanonicalSourceV2.encodedSource source]

noncomputable def qMachine : BitMachine.Machine :=
  BankFieldProjection.machine (0 : Fin 3)

noncomputable def alphabetMachine : BitMachine.Machine :=
  BitMachineComposition.composition
    (BankFieldProjection.machine (1 : Fin 3))
    CylinderProductionProjection.alphabetMachine

noncomputable def tupleMachine : BitMachine.Machine :=
  BitMachineComposition.composition
    (BankFieldProjection.machine (2 : Fin 3))
    CylinderProductionProjection.tupleMachine

theorem field_length_le {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) (i : Fin 3) :
    (![List.replicate q true,CodeDTargetV2.alphabetBytes alphabet,
      CodeDCanonicalSourceV2.encodedSource source] i).length ≤
      (input alphabet source).length :=
  BitMachineBankCodec.word_length_le_encode _ i

theorem q_output {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    qMachine.OutputsWithin (input alphabet source) (List.replicate q true)
      (10*((input alphabet source).length+1)) := by
  simpa only [qMachine,input,BankFieldProjection.result_encode,
    Matrix.cons_val_zero] using
    BankFieldProjection.outputs (0 : Fin 3) (input alphabet source)

theorem alphabet_output {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    alphabetMachine.OutputsWithin (input alphabet source)
      (SourceListEncoding.encode (labelWords alphabet))
      (10*((input alphabet source).length+1)+
        2*(CodeDTargetV2.alphabetBytes alphabet).length+2+
        alphabetClock alphabet) := by
  have hp := BankFieldProjection.outputs (1 : Fin 3) (input alphabet source)
  have hp' : (BankFieldProjection.machine (1 : Fin 3)).OutputsWithin
      (input alphabet source) (CodeDTargetV2.alphabetBytes alphabet)
      (10*((input alphabet source).length+1)) := by
    simpa [input] using hp
  exact BitMachineComposition.composition_outputsWithin _ _ hp'
    (project_alphabet_labels alphabet)

theorem tuple_output {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    tupleMachine.OutputsWithin (input alphabet source)
      (SourceListEncoding.encode (tupleWords source))
      (10*((input alphabet source).length+1)+
        2*(CodeDCanonicalSourceV2.encodedSource source).length+2+
        tupleClock source) := by
  have hp := BankFieldProjection.outputs (2 : Fin 3) (input alphabet source)
  have hp' : (BankFieldProjection.machine (2 : Fin 3)).OutputsWithin
      (input alphabet source) (CodeDCanonicalSourceV2.encodedSource source)
      (10*((input alphabet source).length+1)) := by
    simpa [input] using hp
  exact BitMachineComposition.composition_outputsWithin _ _ hp'
    (project_source_tuple source)

theorem fields_measure_le (xs : List (List Bool)) :
    xs.length+SourceListEncoding.totalLength xs ≤
      (SourceListEncoding.fields xs).length := by
  induction xs with
  | nil => simp [SourceListEncoding.fields,SourceListEncoding.totalLength]
  | cons x xs ih =>
    simp only [SourceListEncoding.fields,SourceListEncoding.totalLength,
      List.map_cons,List.sum_cons,List.length_cons,List.length_append,
      EncodedCommunication.natField,EncodedCommunication.field_length] at *
    omega

theorem input_measure_le (xs : List (List Bool)) :
    CylinderProductionProjectionClock.inputMeasure xs ≤
      (SourceListEncoding.encode xs).length := by
  have h := fields_measure_le xs
  unfold CylinderProductionProjectionClock.inputMeasure SourceListEncoding.encode
  simp only [List.length_append]
  omega

abbrev F := SourceListMachineOuterFramed.itemMachine
  (BankFieldProjection.machine (0 : Fin 2))

noncomputable def itemCoefficient : Nat :=
  UnaryBinaryEncoding.coefficient+100+
    F.stackCount*(10+(UnaryBinaryEncoding.coefficient+25)*F.pushBound)

noncomputable def coefficient : Nat := itemCoefficient+112

theorem projection_clock_bound (n L : Nat) (hn : n ≤ L) :
    CylinderProductionProjectionClock.clockPoly n ≤
      (itemCoefficient+100)*(L+1)^3 := by
  let N := L+1
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hnN : n+1 ≤ N := by dsimp [N]; omega
  have hsq : n+1 ≤ N^2 := hnN.trans (by nlinarith)
  have hpow := Nat.pow_le_pow_left hnN 2
  have ht : CylinderProductionProjectionClock.timeEnv n ≤
      (UnaryBinaryEncoding.coefficient+25)*N^2 := by
    unfold CylinderProductionProjectionClock.timeEnv
    nlinarith
  have hi : CylinderProductionProjectionClock.itemEnv n ≤
      itemCoefficient*N^2 := by
    have hpush := Nat.mul_le_mul_right F.pushBound ht
    have hstack := Nat.mul_le_mul_left F.stackCount
      (show n+CylinderProductionProjectionClock.timeEnv n*F.pushBound+1 ≤
        (10+(UnaryBinaryEncoding.coefficient+25)*F.pushBound)*N^2 by nlinarith)
    unfold CylinderProductionProjectionClock.itemEnv itemCoefficient
    change 20*(n+1)*(n+1)+CylinderProductionProjectionClock.timeEnv n+
      4*n+(3*n+1)+F.stackCount*(n+
        CylinderProductionProjectionClock.timeEnv n*F.pushBound+1)+9 ≤ _
    nlinarith
  have hni := Nat.mul_le_mul hn hi
  have hcube : N^2 ≤ N^3 := by nlinarith
  unfold CylinderProductionProjectionClock.clockPoly
    CylinderProductionProjectionClock.frameEnv
  change _ ≤ (itemCoefficient+100)*N^3
  nlinarith

theorem alphabet_output_polynomial {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    alphabetMachine.OutputsWithin (input alphabet source)
      (SourceListEncoding.encode (labelWords alphabet))
      (coefficient*((input alphabet source).length+1)^3) := by
  let L := (input alphabet source).length
  have ha : (CodeDTargetV2.alphabetBytes alphabet).length ≤ L :=
    field_length_le alphabet source 1
  have hm := input_measure_le (alphabetItems alphabet)
  have hc := CylinderProductionProjectionClock.alphabetClock_poly alphabet
  have hp := projection_clock_bound
    (CylinderProductionProjectionClock.inputMeasure (alphabetItems alphabet)) L
    (hm.trans ha)
  have hN : L+1 ≤ (L+1)^3 := le_self_pow (by omega) (by decide)
  apply BitMachine.outputsWithin_mono alphabetMachine (alphabet_output alphabet source)
  change 10*(L+1)+2*(CodeDTargetV2.alphabetBytes alphabet).length+2+
    alphabetClock alphabet ≤ coefficient*(L+1)^3
  unfold coefficient
  nlinarith

theorem tuple_output_polynomial {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    tupleMachine.OutputsWithin (input alphabet source)
      (SourceListEncoding.encode (tupleWords source))
      (coefficient*((input alphabet source).length+1)^3) := by
  let L := (input alphabet source).length
  have hs : (CodeDCanonicalSourceV2.encodedSource source).length ≤ L :=
    field_length_le alphabet source 2
  have hm := input_measure_le (sourceItems source)
  have hc := CylinderProductionProjectionClock.tupleClock_poly source
  have hp := projection_clock_bound
    (CylinderProductionProjectionClock.inputMeasure (sourceItems source)) L
    (hm.trans hs)
  have hN : L+1 ≤ (L+1)^3 := le_self_pow (by omega) (by decide)
  apply BitMachine.outputsWithin_mono tupleMachine (tuple_output alphabet source)
  change 10*(L+1)+2*(CodeDCanonicalSourceV2.encodedSource source).length+2+
    tupleClock source ≤ coefficient*(L+1)^3
  unfold coefficient
  nlinarith

#print axioms q_output
#print axioms alphabet_output_polynomial
#print axioms tuple_output_polynomial
end CurrentAdditive.CylinderRawInputProjection
