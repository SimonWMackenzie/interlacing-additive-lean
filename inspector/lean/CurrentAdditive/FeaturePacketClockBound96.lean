import CurrentAdditive.FeatureOuterStageClock96
import CurrentAdditive.FeatureStateSize96

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace CurrentAdditive.FeaturePacketClockBound96
open EthInapproximability.CurrentPaper
open FeatureOldDescriptorFrame96 FeatureOldDescriptorSemantics96
open FeatureOuterStageClock96

theorem old_state_size (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) :
    (FeatureCoordinateTransition96.stateWord j ys cs qfuel jUnary carry).length ≤
      1000*(FeatureOuterMeasure96.measure j ys cs qfuel jUnary carry+1) := by
  have hf : (SourceListEncoding.fields (words cs)).length ≤ (SourceListEncoding.encode (words cs)).length := by
    unfold SourceListEncoding.encode
    simp only [List.length_append]
    omega
  have hm : FeatureStateSize96.measure j ys cs qfuel jUnary carry ≤
      2*FeatureOuterMeasure96.measure j ys cs qfuel jUnary carry := by
    unfold FeatureStateSize96.measure FeatureOuterMeasure96.measure
    omega
  have h := (FeatureStateSize96.stateWord_length_le j ys cs qfuel jUnary carry).trans
    (Nat.mul_le_mul_left 300 hm)
  omega

theorem next_packet_size (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) :
    (SourceListEncoding.encode (words (next j ys cs))).length ≤
      3*FeatureOuterMeasure96.measure j ys cs qfuel jUnary carry+1 := by
  have hc := next_count_le j ys cs qfuel jUnary carry
  have hh := header_length_le (words (next j ys cs)).length
  simp only [words,List.length_map] at hh
  unfold SourceListEncoding.encode
  simp only [List.length_append]
  have hb : (SourceListEncoding.fields (words (next j ys cs))).length ≤
      FeatureOuterMeasure96.measure j ys cs qfuel jUnary carry := by unfold FeatureOuterMeasure96.measure; omega
  simp only [words,List.length_map]
  simp only [words] at hb
  omega

theorem next_state_size (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) :
    (FeatureCoordinateTransition96.stateWord (j+1) ys (next j ys cs) qfuel jUnary carry).length ≤
      2000*(FeatureOuterMeasure96.measure j ys cs qfuel jUnary carry+1) := by
  have hc := next_count_le j ys cs qfuel jUnary carry
  have hp := next_packet_size j ys cs qfuel jUnary carry
  have hm : FeatureStateSize96.measure (j+1) ys (next j ys cs) qfuel jUnary carry ≤
      6*(FeatureOuterMeasure96.measure j ys cs qfuel jUnary carry+1) := by
    unfold FeatureStateSize96.measure
    unfold FeatureOuterMeasure96.measure at hc hp ⊢
    omega
  have h := (FeatureStateSize96.stateWord_length_le (j+1) ys (next j ys cs) qfuel jUnary carry).trans
    (Nat.mul_le_mul_left 300 hm)
  omega

theorem advance_clock_le (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) :
    FeatureBankAdvance96.clock (FeatureCoordinateStage96.finalBank j ys cs qfuel jUnary carry)
      (List.replicate (next j ys cs).length true) j ≤
      5*FeatureOuterMeasure96.measure j ys cs qfuel jUnary carry+8 := by
  have h10 := FeatureCoordinateBank96.frame_low (SourceListEncoding.encode (words cs))
    (SourceListEncoding.fields (words (next j ys cs))) (List.replicate (next j ys cs).length true)
    cs.length 0 (extra j ys qfuel jUnary carry) 10
  have h10' : FeatureCoordinateStage96.finalBank j ys cs qfuel jUnary carry 10=
      List.replicate cs.length true := by
    simpa [FeatureCoordinateStage96.finalBank,FeatureCoordinateStage96.beforeHeader,
      FeatureCoordinateBank96.low] using h10
  have hc := next_count_le j ys cs qfuel jUnary carry
  unfold FeatureBankAdvance96.clock
  rw [h10']
  simp only [List.length_replicate]
  unfold FeatureOuterMeasure96.measure at hc ⊢
  omega

theorem packet_scalar (C M old new stage advance : Nat)
    (ho : old ≤ 1000*(M+1)) (hn : new ≤ 2000*(M+1))
    (hs : stage ≤ C*(M+1)^6) (ha : advance ≤ 5*M+8) :
    193*(old+1)+(stage+advance+1)+2*new+4 ≤ (C+1000000)*(M+1)^6 := by
  have h : M+1 ≤ (M+1)^6 := le_self_pow (by omega) (by decide)
  nlinarith

private noncomputable opaque packetDatum :
    {C : Nat // C=FeatureOuterStageClock96.stageCoefficient+1000000} :=
  ⟨FeatureOuterStageClock96.stageCoefficient+1000000,rfl⟩

def packetCoefficient := packetDatum.val
attribute [local irreducible] packetCoefficient

theorem packetCoefficient_eq : packetCoefficient=FeatureOuterStageClock96.stageCoefficient+1000000 := by
  unfold packetCoefficient
  exact packetDatum.property

theorem clock_le (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) :
    FeatureCoordinateTransition96.packetClock j ys cs qfuel jUnary carry ≤
      packetCoefficient*(FeatureOuterMeasure96.measure j ys cs qfuel jUnary carry+1)^6 := by
  have h := packet_scalar FeatureOuterStageClock96.stageCoefficient
    (FeatureOuterMeasure96.measure j ys cs qfuel jUnary carry) _ _ _ _
    (old_state_size j ys cs qfuel jUnary carry) (next_state_size j ys cs qfuel jUnary carry)
    (FeatureOuterStageClock96.clock_le j ys cs qfuel jUnary carry)
    (advance_clock_le j ys cs qfuel jUnary carry)
  change FeatureCoordinateTransition96.packetClock j ys cs qfuel jUnary carry ≤ _ at h
  exact h.trans_eq (congrArg (fun C => C*(FeatureOuterMeasure96.measure j ys cs qfuel jUnary carry+1)^6)
    packetCoefficient_eq.symm)

#print axioms clock_le
end CurrentAdditive.FeaturePacketClockBound96
