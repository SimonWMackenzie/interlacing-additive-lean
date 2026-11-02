import CurrentAdditive.GenericFeatureOuterStageClock
import CurrentAdditive.GenericFeatureCoordinateTransition
import CurrentAdditive.FeatureStateSize96

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace CurrentAdditive.GenericFeaturePacketClockBound
open EthInapproximability.CurrentPaper
open GenericFeatureOldDescriptorFrame GenericFeatureOldDescriptorSemantics
open GenericFeatureOuterStageClock

theorem old_state_size (D : Nat) (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) :
    (GenericFeatureCoordinateTransition.stateWord j ys cs qfuel jUnary carry).length ≤
      1000*(GenericFeatureOuterMeasure.measure D j ys cs qfuel jUnary carry+1) := by
  have hf : (SourceListEncoding.fields (words cs)).length ≤ (SourceListEncoding.encode (words cs)).length := by
    unfold SourceListEncoding.encode
    simp only [List.length_append]
    omega
  have hm : FeatureStateSize96.measure j ys cs qfuel jUnary carry ≤
      2*GenericFeatureOuterMeasure.measure D j ys cs qfuel jUnary carry := by
    unfold FeatureStateSize96.measure GenericFeatureOuterMeasure.measure
    omega
  have h := (FeatureStateSize96.stateWord_length_le j ys cs qfuel jUnary carry).trans
    (Nat.mul_le_mul_left 300 hm)
  dsimp only [GenericFeatureCoordinateTransition.stateWord]
  omega

theorem next_packet_size (D : Nat) (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) :
    (SourceListEncoding.encode (words (next D j ys cs))).length ≤
      3*GenericFeatureOuterMeasure.measure D j ys cs qfuel jUnary carry+1 := by
  have hc := next_count_le D j ys cs qfuel jUnary carry
  have hh := header_length_le (words (next D j ys cs)).length
  simp only [words,List.length_map] at hh
  unfold SourceListEncoding.encode
  simp only [List.length_append]
  have hb : (SourceListEncoding.fields (words (next D j ys cs))).length ≤
      GenericFeatureOuterMeasure.measure D j ys cs qfuel jUnary carry := by
        unfold GenericFeatureOuterMeasure.measure
        dsimp only [GenericFeatureOldDescriptorSemantics.next]
        omega
  simp only [words,List.length_map]
  simp only [words] at hb
  omega

theorem next_state_size (D : Nat) (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) :
    (GenericFeatureCoordinateTransition.stateWord (j+1) ys (next D j ys cs) qfuel jUnary carry).length ≤
      2000*(GenericFeatureOuterMeasure.measure D j ys cs qfuel jUnary carry+1) := by
  have hc := next_count_le D j ys cs qfuel jUnary carry
  have hp := next_packet_size D j ys cs qfuel jUnary carry
  have hm : FeatureStateSize96.measure (j+1) ys (next D j ys cs) qfuel jUnary carry ≤
      6*(GenericFeatureOuterMeasure.measure D j ys cs qfuel jUnary carry+1) := by
    unfold FeatureStateSize96.measure
    unfold GenericFeatureOuterMeasure.measure at hc hp ⊢
    dsimp only [GenericFeatureOldDescriptorSemantics.next] at hc hp ⊢
    omega
  have h := (FeatureStateSize96.stateWord_length_le (j+1) ys (next D j ys cs) qfuel jUnary carry).trans
    (Nat.mul_le_mul_left 300 hm)
  dsimp only [GenericFeatureCoordinateTransition.stateWord]
  omega

theorem advance_clock_le (D : Nat) (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) :
    FeatureBankAdvance96.clock (GenericFeatureCoordinateStage.finalBank D j ys cs qfuel jUnary carry)
      (List.replicate (next D j ys cs).length true) j ≤
      5*GenericFeatureOuterMeasure.measure D j ys cs qfuel jUnary carry+8 := by
  have h10 := FeatureCoordinateBank96.frame_low (SourceListEncoding.encode (words cs))
    (SourceListEncoding.fields (words (next D j ys cs))) (List.replicate (next D j ys cs).length true)
    cs.length 0 (extra j ys qfuel jUnary carry) 10
  have h10' : GenericFeatureCoordinateStage.finalBank D j ys cs qfuel jUnary carry 10=
      List.replicate cs.length true := by
    simpa [GenericFeatureCoordinateStage.finalBank,GenericFeatureCoordinateStage.beforeHeader,
      FeatureCoordinateBank96.low] using h10
  have hc := next_count_le D j ys cs qfuel jUnary carry
  unfold FeatureBankAdvance96.clock
  rw [h10']
  simp only [List.length_replicate]
  unfold GenericFeatureOuterMeasure.measure at hc ⊢
  dsimp only [GenericFeatureOldDescriptorSemantics.next] at hc ⊢
  omega

theorem packet_scalar (C M old new stage advance : Nat)
    (ho : old ≤ 1000*(M+1)) (hn : new ≤ 2000*(M+1))
    (hs : stage ≤ C*(M+1)^6) (ha : advance ≤ 5*M+8) :
    193*(old+1)+(stage+advance+1)+2*new+4 ≤ (C+1000000)*(M+1)^6 := by
  have h : M+1 ≤ (M+1)^6 := le_self_pow (by omega) (by decide)
  nlinarith

private noncomputable opaque packetDatum (D : Nat) :
    {C : Nat // C=GenericFeatureOuterStageClock.stageCoefficient D+1000000} :=
  ⟨GenericFeatureOuterStageClock.stageCoefficient D+1000000,rfl⟩

def packetCoefficient (D : Nat) := (packetDatum D).val
attribute [local irreducible] packetCoefficient

theorem packetCoefficient_eq (D : Nat) : packetCoefficient D=GenericFeatureOuterStageClock.stageCoefficient D+1000000 := by
  unfold packetCoefficient
  exact (packetDatum D).property

theorem clock_le (D : Nat) (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) :
    GenericFeatureCoordinateTransition.packetClock D j ys cs qfuel jUnary carry ≤
      packetCoefficient D*(GenericFeatureOuterMeasure.measure D j ys cs qfuel jUnary carry+1)^6 := by
  have h := packet_scalar (GenericFeatureOuterStageClock.stageCoefficient D)
    (GenericFeatureOuterMeasure.measure D j ys cs qfuel jUnary carry) _ _ _ _
    (old_state_size D j ys cs qfuel jUnary carry) (next_state_size D j ys cs qfuel jUnary carry)
    (GenericFeatureOuterStageClock.clock_le D j ys cs qfuel jUnary carry)
    (advance_clock_le D j ys cs qfuel jUnary carry)
  change GenericFeatureCoordinateTransition.packetClock D j ys cs qfuel jUnary carry ≤ _ at h
  exact h.trans_eq (congrArg (fun C => C*(GenericFeatureOuterMeasure.measure D j ys cs qfuel jUnary carry+1)^6)
    (packetCoefficient_eq D).symm)

#print axioms clock_le
end CurrentAdditive.GenericFeaturePacketClockBound
