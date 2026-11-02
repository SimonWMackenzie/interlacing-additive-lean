import CurrentAdditive.FeatureOuterMeasure96

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace CurrentAdditive.FeatureOuterBudget96
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open FeatureOldDescriptorFrame96 FeatureOldDescriptorSemantics96
open FeatureOuterMeasure96
open GaussListContext Wide96ContextListScheduler

abbrev data := FeatureCoordinateStage96.data

def timeCap (M : Nat) := FeatureGuardClockBound96.coefficient*(M+1)^5

def growth := BitMachineStackGrowth.perStep FeatureGuardedDescriptor96.program

def cycleCap (M : Nat) := 50*(M+1)^3+(1+10*growth)*timeCap M+10*(M+1)^2+14

theorem callback_time_le (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (hsplit : pre++word::suffix=words cs) :
    (FeatureOldDescriptorTraversal96.contract (data j ys cs qfuel jUnary carry)).time pre word suffix≤
      timeCap (measure j ys cs qfuel jUnary carry) := by
  let D := data j ys cs qfuel jUnary carry
  obtain ⟨c,hc,hw⟩ := FeatureOldDescriptorTraversal96.descriptor_from_split D pre word suffix hsplit
  have h := FeatureOldDescriptorTraversal96.time_le D pre word suffix hsplit
  have hword : D.wordClock pre word=FeatureGuardedDescriptor96.clock j c ys
      (SourceListEncoding.fields (words cs)++joined (piece j ys) pre) := by
    simp only [FeatureOldDescriptorTraversal96.Data.wordClock,hw,
      CylinderFeatureCodec.decodeFeature_encodeFeature,D,data,FeatureCoordinateStage96.data,
      FeatureOldDescriptorTraversal96.Data.piece]
  rw [hword] at h
  have hsize := callback_size j ys cs qfuel jUnary carry pre word suffix hsplit c hc hw
  have hg := FeatureGuardClockBound96.clock_le j c ys
    (SourceListEncoding.fields (words cs)++joined (piece j ys) pre)
  exact h.trans (hg.trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_left (Nat.add_le_add_right hsize 1) 5)))

theorem state_length_le (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (hsplit : pre++word::suffix=words cs) (k : Fin 96) :
    ((FeatureOldDescriptorTraversal96.contract (data j ys cs qfuel jUnary carry)).state pre word suffix k).length≤
      (measure j ys cs qfuel jUnary carry+1)^2+
        growth*timeCap (measure j ys cs qfuel jUnary carry) := by
  let D := data j ys cs qfuel jUnary carry
  let C := FeatureOldDescriptorTraversal96.contract D
  let S := selected j ys qfuel jUnary carry pre word suffix
    (SourceListEncoding.fields (words cs)++joined (piece j ys) pre)
    (context (List.replicate cs.length true) ys pre)
  have hr := C.callback_run pre word suffix hsplit
  have hr' : ((advance FeatureGuardedDescriptor96.program)^[C.time pre word suffix])
      (⟨some FeatureGuardedDescriptor96.start,FeatureGuardedDescriptor96.control,S⟩ :
        TM2.Cfg (fun _ : Fin 96 => Bool) _ _) =
      ⟨none,C.control pre word suffix,C.state pre word suffix⟩ := by
    simpa only [S,selected,D,data,FeatureCoordinateStage96.data,
      FeatureOldDescriptorTraversal96.Data.body,FeatureOldDescriptorTraversal96.Data.context,
      FeatureOldDescriptorTraversal96.Data.extra,FeatureOldDescriptorTraversal96.Data.original,
      FeatureOldDescriptorTraversal96.Data.piece,hsplit] using hr
  have hg := BitMachineStackGrowth.run_growth FeatureGuardedDescriptor96.program
    (⟨some FeatureGuardedDescriptor96.start,FeatureGuardedDescriptor96.control,S⟩ :
      TM2.Cfg (fun _ : Fin 96 => Bool) _ _) (C.time pre word suffix) k
  rw [hr'] at hg
  exact hg.trans (Nat.add_le_add
    (selected_length j ys cs qfuel jUnary carry pre word suffix hsplit k)
    (Nat.mul_le_mul_left growth (callback_time_le j ys cs qfuel jUnary carry pre word suffix hsplit)))

theorem cycle_arithmetic (G T H Z getter time cleanup : Nat)
    (hg : getter≤H) (ht : time≤T) (hc : cleanup≤10*(Z+G*T)) :
    getter+(time+1)+1+(cleanup+11)+1≤H+(1+10*G)*T+10*Z+14 := by nlinarith

theorem cycleBudget_le (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (hsplit : pre++word::suffix=words cs) :
    MovingContextScheduler96.cycleBudget FeatureGuardedDescriptor96.program
      FeatureGuardedDescriptor96.start FeatureGuardedDescriptor96.control
      (piece j ys) (SourceListEncoding.fields (words cs))
      (context (List.replicate cs.length true) ys) (words cs)
      (FeatureOldDescriptorTraversal96.contract (data j ys cs qfuel jUnary carry))
      pre word suffix≤cycleCap (measure j ys cs qfuel jUnary carry) := by
  let M := measure j ys cs qfuel jUnary carry
  have ht := callback_time_le j ys cs qfuel jUnary carry pre word suffix hsplit
  have hg := StatefulListScheduler.getterBudget_cubic pre word suffix
  change getterBudget pre word suffix≤
    50*((SourceListEncoding.encode (pre++word::suffix)).length+1)^3 at hg
  rw [hsplit] at hg
  have hsource : (SourceListEncoding.encode (words cs)).length≤M := by dsimp [M,FeatureOuterMeasure96.measure]; omega
  have hget : getterBudget pre word suffix≤50*(M+1)^3 :=
    hg.trans (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (Nat.add_le_add_right hsource 1) 3))
  have hsum := Finset.sum_le_sum (s:=Finset.univ)
    (fun i _ => state_length_le j ys cs qfuel jUnary carry pre word suffix hsplit (cleanBank i))
  have hs : (∑ i : Fin 10,
      ((FeatureOldDescriptorTraversal96.contract (data j ys cs qfuel jUnary carry)).state pre word suffix (cleanBank i)).length)≤
      10*((M+1)^2+growth*timeCap M) := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] using hsum
  dsimp only [MovingContextScheduler96.cycleBudget,cycleCap]
  exact cycle_arithmetic growth (timeCap M) (50*(M+1)^3) ((M+1)^2)
    _ _ _ hget ht hs

end CurrentAdditive.FeatureOuterBudget96
