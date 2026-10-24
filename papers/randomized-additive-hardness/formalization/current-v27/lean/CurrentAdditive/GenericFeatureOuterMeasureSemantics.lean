import CurrentAdditive.GenericFeatureOldDescriptorSemantics
import CurrentAdditive.GenericFeatureOuterMeasure

/-! Computed byte and count measures for the actual outer descriptor scan.
The extension sum also pays the guarded clock on descriptors rejected by the
depth test. No output-size bound is assumed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace CurrentAdditive.GenericFeatureOuterMeasure
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open GenericFeatureOldDescriptorFrame GenericFeatureOldDescriptorSemantics
open GaussListContext Wide96ContextListScheduler

theorem context_length_le (D : Nat) (count : List Bool) (ys : List Nat) (pre : List (List Bool)) :
    (context D count ys pre).length≤count.length+ys.length*pre.length := by
  induction pre generalizing count with
  | nil => simp [context]
  | cons word pre ih =>
    have h := ih (countStep D ys count word)
    have hs : (countStep D ys count word).length≤ys.length+count.length := by
      unfold countStep
      split_ifs <;> simp <;> omega
    change (context D (countStep D ys count word) ys pre).length≤_
    simp only [List.length_cons]
    nlinarith

theorem split_bounds (cs : List (List (Nat × Nat))) (pre : List (List Bool))
    (word : List Bool) (suffix : List (List Bool)) (hsplit : pre++word::suffix=words cs) :
    let L := (SourceListEncoding.encode (words cs)).length
    pre.length≤L ∧ suffix.length≤L ∧ word.length≤L ∧
      (SourceListEncoding.fields suffix).length≤L ∧ pre.length≤cs.length := by
  dsimp only
  have hm := CylinderRawInputProjection.input_measure_le (words cs)
  unfold CylinderProductionProjectionClock.inputMeasure at hm
  have hcount : pre.length+1+suffix.length=cs.length := by
    simpa [words,List.length_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using congrArg List.length hsplit
  have ht : SourceListEncoding.totalLength (words cs)=
      SourceListEncoding.totalLength pre+word.length+SourceListEncoding.totalLength suffix := by
    rw [←hsplit]
    simp [SourceListEncoding.totalLength,List.sum_append,Nat.add_assoc]
  have hf : (SourceListEncoding.fields suffix).length≤
      (SourceListEncoding.encode (words cs)).length := by
    rw [←hsplit]
    simp only [SourceListEncoding.encode,FeatureAlphabetClockBounds64.fields_append,
      SourceListEncoding.fields,List.length_append]
    omega
  have hmap : (words cs).length=cs.length := by simp [words]
  omega

theorem accumulated_body (D : Nat) (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (pre : List (List Bool)) (word : List Bool) (suffix : List (List Bool))
    (hsplit : pre++word::suffix=words cs) :
    (SourceListEncoding.fields (words cs)++joined (piece D j ys) pre).length≤
      (SourceListEncoding.fields (words (next D j ys cs))).length := by
  have he := body_exact D j ys cs
  have hp : (joined (piece D j ys) pre).length≤(joined (piece D j ys) (words cs)).length := by
    rw [←hsplit]
    simp only [joined,List.flatMap_append,List.flatMap_cons,List.length_append]
    omega
  have hlen := congrArg List.length he
  simp only [List.length_append] at *
  omega

theorem callback_size (D : Nat) (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (hsplit : pre++word::suffix=words cs)
    (c : List (Nat × Nat)) (hc : c∈cs) (hw : word=CylinderFeatureCodec.encodeFeature c) :
    FeatureAlphabetClockBounds64.inputSize j c ys
      (SourceListEncoding.fields (words cs)++joined (piece D j ys) pre)≤
      measure D j ys cs qfuel jUnary carry := by
  obtain ⟨_,_,hword,_,_⟩ := split_bounds cs pre word suffix hsplit
  rw [hw] at hword
  have hbody := accumulated_body D j ys cs pre word suffix hsplit
  dsimp only [GenericFeatureOldDescriptorSemantics.next] at hbody
  have hext : (GenericFeatureEligibleDescriptor.extensions j c ys).length≤extensionBytes j ys cs := by
    apply List.le_sum_of_mem
    exact List.mem_map.mpr ⟨c,hc,rfl⟩
  dsimp only [measure,FeatureAlphabetClockBounds64.inputSize,
    FeatureAlphabetClockBounds64.extensions,GenericFeatureEligibleDescriptor.extensions,
    FeatureBoundedAlphabet64.original] at *
  omega

theorem selected_length_aux (j : Nat) (ys : List Nat) (qfuel jUnary carry : List Bool)
    (pre : List (List Bool)) (word : List Bool) (suffix : List (List Bool))
    (out count : List Bool) (N : Nat)
    (hs : (SourceListEncoding.encode (pre++word::suffix)).length≤N)
    (hf : (SourceListEncoding.fields suffix).length≤N) (hw : word.length≤N)
    (hp : pre.length≤N) (ht : suffix.length≤N) (ho : out.length≤N)
    (hc : count.length≤N) (hj : j.bits.length≤N) (hq : qfuel.length≤N)
    (hu : jUnary.length≤N) (hr : carry.length≤N)
    (ha : (SourceListEncoding.encode (FeatureInnerAlphabetRun64.labelWords ys)).length≤N)
    (hy : ys.length≤N) (k : Fin 96) :
    (selected j ys qfuel jUnary carry pre word suffix out count k).length≤N := by
  by_cases hk : ∃ i,Wide96ContextPreservingScan.locate i=k
  · obtain ⟨i,rfl⟩ := hk
    unfold selected
    rw [Wide96ContextPreservingScan.frame_bank]
    fin_cases i <;> simp [CylinderContextScanStep.selectedBank] <;> omega
  · unfold selected
    rw [Wide96ContextPreservingScan.frame_foreign _ _ k hk]
    simp only [foreignBank,extra,Function.update_apply]
    split_ifs <;> simp_all

theorem selected_length (D : Nat) (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (hsplit : pre++word::suffix=words cs) (k : Fin 96) :
    (selected j ys qfuel jUnary carry pre word suffix
      (SourceListEncoding.fields (words cs)++joined (piece D j ys) pre)
      (context D (List.replicate cs.length true) ys pre) k).length≤
      (measure D j ys cs qfuel jUnary carry+1)^2 := by
  let M := measure D j ys cs qfuel jUnary carry
  have hM : M≤(M+1)^2 := by nlinarith
  obtain ⟨hp,ht,hw,hf,hpc⟩ := split_bounds cs pre word suffix hsplit
  have ho := accumulated_body D j ys cs pre word suffix hsplit
  have hc := context_length_le D (List.replicate cs.length true) ys pre
  simp only [List.length_replicate] at hc
  have hcount : (context D (List.replicate cs.length true) ys pre).length≤(M+1)^2 := by
    have hys : ys.length≤M := by dsimp [M,measure]; omega
    have hcs : cs.length≤M := by dsimp [M,measure]; omega
    have hpM : pre.length≤M := hpc.trans hcs
    have hmul := Nat.mul_le_mul hys hpM
    nlinarith
  change (selected j ys qfuel jUnary carry pre word suffix
      (SourceListEncoding.fields (words cs)++joined (piece D j ys) pre)
      (context D (List.replicate cs.length true) ys pre) k).length≤(M+1)^2
  have hsM : (SourceListEncoding.encode (words cs)).length≤M := by dsimp [M,measure]; omega
  have hoM : (SourceListEncoding.fields (words (next D j ys cs))).length≤M := by
    dsimp [M,measure,GenericFeatureOldDescriptorSemantics.next]; omega
  apply selected_length_aux
  · rw [hsplit]; exact hsM.trans hM
  · exact hf.trans (hsM.trans hM)
  · exact hw.trans (hsM.trans hM)
  · exact hp.trans (hsM.trans hM)
  · exact ht.trans (hsM.trans hM)
  · exact ho.trans (hoM.trans hM)
  · exact hcount
  · exact (by dsimp [M,measure]; omega : j.bits.length≤M).trans hM
  · exact (by dsimp [M,measure]; omega : qfuel.length≤M).trans hM
  · exact (by dsimp [M,measure]; omega : jUnary.length≤M).trans hM
  · exact (by dsimp [M,measure]; omega : carry.length≤M).trans hM
  · exact (by dsimp [M,measure]; omega :
      (SourceListEncoding.encode (FeatureInnerAlphabetRun64.labelWords ys)).length≤M).trans hM
  · exact (by dsimp [M,measure]; omega : ys.length≤M).trans hM

#print axioms selected_length
end CurrentAdditive.GenericFeatureOuterMeasure
