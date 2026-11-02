import CurrentAdditive.FeatureOuterBudget96

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace CurrentAdditive.FeatureOuterStageClock96
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open FeatureOldDescriptorFrame96 FeatureOldDescriptorSemantics96
open FeatureOuterMeasure96 FeatureOuterBudget96
open GaussListContext Wide96ContextListScheduler
open MinimumRatioContext

def headerCoefficientAt (a p : Nat) := 100*(1+a)*(1+p)

theorem header_scalar (n a p : Nat) :
    (2*n+2)+(a*(n+1)^2)+(2*(n+a*(n+1)^2*p)+2)+
      (8*(n+a*(n+1)^2*p)+8+2)+3 ≤ headerCoefficientAt a p*(n+1)^2 := by
  let T := (n+1)^2
  have hn : n+1 ≤ T := by dsimp [T]; nlinarith
  have hb : 12*n+17 ≤ 29*T := by nlinarith
  have hc : 29+a+10*a*p ≤ headerCoefficientAt a p := by unfold headerCoefficientAt; nlinarith
  calc
    _ = (12*n+17)+(a+10*a*p)*T := by dsimp [T]; ring
    _ ≤ 29*T+(a+10*a*p)*T := Nat.add_le_add_right hb _
    _ = (29+a+10*a*p)*T := by ring
    _ ≤ _ := Nat.mul_le_mul_right T hc

private noncomputable opaque headerDatum :
    {C : Nat // C=headerCoefficientAt (UnaryBinaryEncoding.coefficient+7)
      FeatureCountHeader96.M.pushBound} :=
  ⟨headerCoefficientAt (UnaryBinaryEncoding.coefficient+7) FeatureCountHeader96.M.pushBound,rfl⟩

def headerCoefficient := headerDatum.val
attribute [local irreducible] headerCoefficient

theorem headerCoefficient_eq : headerCoefficient=headerCoefficientAt (UnaryBinaryEncoding.coefficient+7) FeatureCountHeader96.M.pushBound := by unfold headerCoefficient; exact headerDatum.property

theorem header_clock_le (count : List Bool) :
    FeatureCountHeader96.clock count ≤ headerCoefficient*(count.length+1)^2 := by
  have h := header_scalar count.length (UnaryBinaryEncoding.coefficient+7) FeatureCountHeader96.M.pushBound
  change FeatureCountHeader96.clock count ≤ _ at h
  calc
    _  ≤  headerCoefficientAt (UnaryBinaryEncoding.coefficient+7)
      FeatureCountHeader96.M.pushBound*(count.length+1)^2 := h
    _ = _ := congrArg (fun C => C*(count.length+1)^2) headerCoefficient_eq.symm

def scanCoefficientAt (C G : Nat) := 75+(1+10*G)*C

theorem cycle_scalar (C G M : Nat) :
    50*(M+1)^3+(1+10*G)*(C*(M+1)^5)+10*(M+1)^2+14+1 ≤
      scanCoefficientAt C G*(M+1)^5 := by
  have h3 : (M+1)^3 ≤ (M+1)^5 := pow_le_pow_right₀ (by omega) (by decide)
  have h2 : (M+1)^2 ≤ (M+1)^5 := pow_le_pow_right₀ (by omega) (by decide)
  have h1 : 1 ≤ (M+1)^5 := by exact one_le_pow₀ (by omega)
  unfold scanCoefficientAt
  nlinarith

private noncomputable opaque scanDatum :
    {C : Nat // C=scanCoefficientAt FeatureGuardClockBound96.coefficient FeatureOuterBudget96.growth} :=
  ⟨scanCoefficientAt FeatureGuardClockBound96.coefficient FeatureOuterBudget96.growth,rfl⟩

def scanCoefficient := scanDatum.val
attribute [local irreducible] scanCoefficient

theorem scanCoefficient_eq : scanCoefficient=scanCoefficientAt FeatureGuardClockBound96.coefficient FeatureOuterBudget96.growth := by unfold scanCoefficient; exact scanDatum.property

theorem cycleCap_le (M : Nat) : cycleCap M+1 ≤ scanCoefficient*(M+1)^5 := by
  have h := cycle_scalar FeatureGuardClockBound96.coefficient FeatureOuterBudget96.growth M
  change cycleCap M+1 ≤ _ at h
  exact h.trans_eq (congrArg (fun C => C*(M+1)^5) scanCoefficient_eq.symm)

theorem scanClock_le (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) :
    FeatureCoordinateStage96.scanClock j ys cs qfuel jUnary carry ≤
      scanCoefficient*(FeatureOuterMeasure96.measure j ys cs qfuel jUnary carry+1)^6 := by
  let M := FeatureOuterMeasure96.measure j ys cs qfuel jUnary carry
  have h := MovingContextScheduler96.remainingBudget_fixed_input FeatureGuardedDescriptor96.program
    FeatureGuardedDescriptor96.start FeatureGuardedDescriptor96.control (piece j ys)
    (SourceListEncoding.fields (words cs)) (context (List.replicate cs.length true) ys)
    (words cs) (FeatureOldDescriptorTraversal96.contract (FeatureCoordinateStage96.data j ys cs qfuel jUnary carry))
    (cycleCap M) (fun pre word suffix hsplit => cycleBudget_le j ys cs qfuel jUnary carry pre word suffix hsplit)
    [] (words cs) (by simp)
  simp only [words,List.length_map] at h
  change FeatureCoordinateStage96.scanClock j ys cs qfuel jUnary carry ≤
    (cs.length+1)*(cycleCap M+1) at h
  have hc : cs.length+1 ≤ M+1 := by dsimp [M,FeatureOuterMeasure96.measure]; omega
  calc
    _  ≤  (cs.length+1)*(cycleCap M+1) := h
    _  ≤  (M+1)*(scanCoefficient*(M+1)^5) := Nat.mul_le_mul hc (cycleCap_le M)
    _ = _ := by ring

theorem next_count_le (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) :
    (next j ys cs).length ≤ FeatureOuterMeasure96.measure j ys cs qfuel jUnary carry := by
  have h := CylinderRawInputProjection.fields_measure_le (words (next j ys cs))
  simp only [words,List.length_map] at h
  unfold FeatureOuterMeasure96.measure
  dsimp only [words] at *
  omega

theorem header_length_le (n : Nat) : (EncodedCommunication.natField n).length ≤ 2*n+1 :=
  EncodedGraph.natField_length_upper n

def stageCoefficientAt (C H : Nat) := C+H+50

theorem stage_scalar (C H M scan header source body hdr : Nat)
    (hs : scan ≤ C*(M+1)^6) (hh : header ≤ H*(M+1)^2)
    (hsource : source ≤ M) (hb : body ≤ M) (hhd : hdr ≤ 2*M+1) :
    scan+(header+source+2+(2*body+2*hdr+5)+hdr+2+3)+1 ≤
      stageCoefficientAt C H*(M+1)^6 := by
  have h26 : (M+1)^2 ≤ (M+1)^6 := pow_le_pow_right₀ (by omega) (by decide)
  have h16 : M+1 ≤ (M+1)^6 := le_self_pow (by omega) (by decide)
  have hm := Nat.mul_le_mul_left H h26
  unfold stageCoefficientAt
  nlinarith

private noncomputable opaque stageDatum :
    {C : Nat // C=stageCoefficientAt scanCoefficient headerCoefficient} :=
  ⟨stageCoefficientAt scanCoefficient headerCoefficient,rfl⟩

def stageCoefficient := stageDatum.val
attribute [local irreducible] stageCoefficient

theorem stageCoefficient_eq : stageCoefficient=stageCoefficientAt scanCoefficient headerCoefficient := by unfold stageCoefficient; exact stageDatum.property

theorem beforeHeader_source (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) :
    FeatureCoordinateStage96.beforeHeader j ys cs qfuel jUnary carry 8=
      SourceListEncoding.encode (words cs) := by
  have h := FeatureCoordinateBank96.frame_low (SourceListEncoding.encode (words cs))
    (SourceListEncoding.fields (words (next j ys cs)))
    (List.replicate (next j ys cs).length true) cs.length 0 (extra j ys qfuel jUnary carry) 8
  simpa only [FeatureCoordinateStage96.beforeHeader,FeatureCoordinateBank96.low] using h

theorem clock_le (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) :
    FeatureCoordinateStage96.clock j ys cs qfuel jUnary carry ≤
      stageCoefficient*(FeatureOuterMeasure96.measure j ys cs qfuel jUnary carry+1)^6 := by
  let M := FeatureOuterMeasure96.measure j ys cs qfuel jUnary carry
  have hs := scanClock_le j ys cs qfuel jUnary carry
  have hc := next_count_le j ys cs qfuel jUnary carry
  have hh := header_clock_le (List.replicate (next j ys cs).length true)
  simp only [List.length_replicate] at hh
  have hheader : FeatureCountHeader96.clock (List.replicate (next j ys cs).length true) ≤
      headerCoefficient*(M+1)^2 := hh.trans (Nat.mul_le_mul_left _
        (Nat.pow_le_pow_left (Nat.add_le_add_right hc 1) 2))
  have hsource : (SourceListEncoding.encode (words cs)).length ≤ M := by
    dsimp [M,FeatureOuterMeasure96.measure]; omega
  have hbody : (SourceListEncoding.fields (words (next j ys cs))).length ≤ M := by
    dsimp [M,FeatureOuterMeasure96.measure]; omega
  have hhdr : (EncodedCommunication.natField (next j ys cs).length).length ≤ 2*M+1 :=
    (header_length_le _).trans (by omega)
  have h := stage_scalar scanCoefficient headerCoefficient M _ _ _ _ _ hs hheader hsource hbody hhdr
  have h' : FeatureCoordinateStage96.clock j ys cs qfuel jUnary carry ≤
      stageCoefficientAt scanCoefficient headerCoefficient*(M+1)^6 := by
    simpa only [FeatureCoordinateStage96.clock,FeaturePacketFinalize96.clock,
      beforeHeader_source,List.length_replicate,FeaturePacketJoin96.clock] using h
  exact h'.trans_eq (congrArg (fun C => C*(M+1)^6) stageCoefficient_eq.symm)

#print axioms clock_le

end CurrentAdditive.FeatureOuterStageClock96
