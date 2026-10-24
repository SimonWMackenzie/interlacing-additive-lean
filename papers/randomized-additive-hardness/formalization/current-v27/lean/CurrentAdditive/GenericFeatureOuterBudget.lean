import CurrentAdditive.GenericFeatureOuterMeasureSemantics
import CurrentAdditive.GenericFeatureGuardClockBound
import CurrentAdditive.GenericFeatureOldDescriptorTraversal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace CurrentAdditive.GenericFeatureOuterBudget
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open GenericFeatureOldDescriptorFrame GenericFeatureOldDescriptorSemantics
open GenericFeatureOuterMeasure
open GaussListContext Wide96ContextListScheduler

def data (D j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) : GenericFeatureOldDescriptorTraversal.Data D :=
  ⟨j,ys,cs,qfuel,jUnary,carry,SourceListEncoding.fields (words cs),
    List.replicate cs.length true⟩

def timeCap (D M : Nat) := GenericFeatureGuardClockBound.coefficient D*(M+1)^5

def growth (D : Nat) := BitMachineStackGrowth.perStep (GenericFeatureGuardedDescriptor.program D)

def cycleCap (D M : Nat) := 50*(M+1)^3+(1+10*growth D)*timeCap D M+10*(M+1)^2+14

theorem callback_time_le (D : Nat) (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (hsplit : pre++word::suffix=words cs) :
    (GenericFeatureOldDescriptorTraversal.contract (data D j ys cs qfuel jUnary carry)).time pre word suffix≤
      timeCap D (measure D j ys cs qfuel jUnary carry) := by
  let d := data D j ys cs qfuel jUnary carry
  obtain ⟨c,hc,hw⟩ := GenericFeatureOldDescriptorTraversal.descriptor_from_split d pre word suffix hsplit
  have h := GenericFeatureOldDescriptorTraversal.time_le d pre word suffix hsplit
  have hword : d.wordClock pre word=GenericFeatureGuardedDescriptor.clock D j c ys
      (SourceListEncoding.fields (words cs)++joined (piece D j ys) pre) := by
    simp only [GenericFeatureOldDescriptorTraversal.Data.wordClock,hw,
      CylinderFeatureCodec.decodeFeature_encodeFeature,d,data,
      GenericFeatureOldDescriptorTraversal.Data.piece]
  rw [hword] at h
  have hsize := callback_size D j ys cs qfuel jUnary carry pre word suffix hsplit c hc hw
  have hg := GenericFeatureGuardClockBound.clock_le D j c ys
    (SourceListEncoding.fields (words cs)++joined (piece D j ys) pre)
  exact h.trans (hg.trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_left (Nat.add_le_add_right hsize 1) 5)))

theorem state_length_le (D : Nat) (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (hsplit : pre++word::suffix=words cs) (k : Fin 96) :
    ((GenericFeatureOldDescriptorTraversal.contract (data D j ys cs qfuel jUnary carry)).state pre word suffix k).length≤
      (measure D j ys cs qfuel jUnary carry+1)^2+
        growth D*timeCap D (measure D j ys cs qfuel jUnary carry) := by
  let d := data D j ys cs qfuel jUnary carry
  let C := GenericFeatureOldDescriptorTraversal.contract d
  let S := selected j ys qfuel jUnary carry pre word suffix
    (SourceListEncoding.fields (words cs)++joined (piece D j ys) pre)
    (context D (List.replicate cs.length true) ys pre)
  have hr := C.callback_run pre word suffix hsplit
  have hr' : ((advance (GenericFeatureGuardedDescriptor.program D))^[C.time pre word suffix])
      (⟨some (GenericFeatureGuardedDescriptor.start D),(GenericFeatureGuardedDescriptor.control D),S⟩ :
        TM2.Cfg (fun _ : Fin 96 => Bool) _ _) =
      ⟨none,C.control pre word suffix,C.state pre word suffix⟩ := by
    simpa only [S,selected,d,data,
      GenericFeatureOldDescriptorTraversal.Data.body,GenericFeatureOldDescriptorTraversal.Data.context,
      GenericFeatureOldDescriptorTraversal.Data.extra,GenericFeatureOldDescriptorTraversal.Data.original,
      GenericFeatureOldDescriptorTraversal.Data.piece,hsplit] using hr
  have hg := BitMachineStackGrowth.run_growth (GenericFeatureGuardedDescriptor.program D)
    (⟨some (GenericFeatureGuardedDescriptor.start D),(GenericFeatureGuardedDescriptor.control D),S⟩ :
      TM2.Cfg (fun _ : Fin 96 => Bool) _ _) (C.time pre word suffix) k
  rw [hr'] at hg
  exact hg.trans (Nat.add_le_add
    (selected_length D j ys cs qfuel jUnary carry pre word suffix hsplit k)
    (Nat.mul_le_mul_left (growth D) (callback_time_le D j ys cs qfuel jUnary carry pre word suffix hsplit)))

theorem cycle_arithmetic (G T H Z getter time cleanup : Nat)
    (hg : getter≤H) (ht : time≤T) (hc : cleanup≤10*(Z+G*T)) :
    getter+(time+1)+1+(cleanup+11)+1≤H+(1+10*G)*T+10*Z+14 := by nlinarith

theorem cycleBudget_le (D : Nat) (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (hsplit : pre++word::suffix=words cs) :
    MovingContextScheduler96.cycleBudget (GenericFeatureGuardedDescriptor.program D)
      (GenericFeatureGuardedDescriptor.start D) (GenericFeatureGuardedDescriptor.control D)
      (piece D j ys) (SourceListEncoding.fields (words cs))
      (context D (List.replicate cs.length true) ys) (words cs)
      (GenericFeatureOldDescriptorTraversal.contract (data D j ys cs qfuel jUnary carry))
      pre word suffix≤cycleCap D (measure D j ys cs qfuel jUnary carry) := by
  let M := measure D j ys cs qfuel jUnary carry
  have ht := callback_time_le D j ys cs qfuel jUnary carry pre word suffix hsplit
  have hg := StatefulListScheduler.getterBudget_cubic pre word suffix
  change getterBudget pre word suffix≤
    50*((SourceListEncoding.encode (pre++word::suffix)).length+1)^3 at hg
  rw [hsplit] at hg
  have hsource : (SourceListEncoding.encode (words cs)).length≤M := by dsimp [M,GenericFeatureOuterMeasure.measure]; omega
  have hget : getterBudget pre word suffix≤50*(M+1)^3 :=
    hg.trans (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (Nat.add_le_add_right hsource 1) 3))
  have hsum := Finset.sum_le_sum (s:=Finset.univ)
    (fun i _ => state_length_le D j ys cs qfuel jUnary carry pre word suffix hsplit (cleanBank i))
  have hs : (∑ i : Fin 10,
      ((GenericFeatureOldDescriptorTraversal.contract (data D j ys cs qfuel jUnary carry)).state pre word suffix (cleanBank i)).length)≤
      10*((M+1)^2+growth D*timeCap D M) := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] using hsum
  dsimp only [MovingContextScheduler96.cycleBudget,cycleCap]
  exact cycle_arithmetic (growth D) (timeCap D M) (50*(M+1)^3) ((M+1)^2)
    _ _ _ hget ht hs

end CurrentAdditive.GenericFeatureOuterBudget
