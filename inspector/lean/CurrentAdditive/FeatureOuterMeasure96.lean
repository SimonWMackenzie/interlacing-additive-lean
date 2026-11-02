import CurrentAdditive.FeatureGuardClockBound96

/-! Computed byte and count measures for the actual outer descriptor scan.
The extension sum also pays the guarded clock on descriptors rejected by the
depth test. No output-size bound is assumed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace CurrentAdditive.FeatureOuterMeasure96
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open FeatureOldDescriptorFrame96 FeatureOldDescriptorSemantics96
open GaussListContext Wide96ContextListScheduler

def extensionBytes (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat))) : Nat :=
  (cs.map (fun c => (FeatureEligibleDescriptor96.extensions j c ys).length)).sum

def measure (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) : Nat :=
  (SourceListEncoding.encode (words cs)).length+
    (SourceListEncoding.fields (words (next j ys cs))).length+
    extensionBytes j ys cs+
    (SourceListEncoding.encode (FeatureInnerAlphabetRun64.labelWords ys)).length+
    j.bits.length+(j+1).bits.length+qfuel.length+jUnary.length+carry.length+cs.length+ys.length+1

theorem context_length_le (count : List Bool) (ys : List Nat) (pre : List (List Bool)) :
    (context count ys pre).length≤count.length+ys.length*pre.length := by
  induction pre generalizing count with
  | nil => simp [context]
  | cons word pre ih =>
    have h := ih (countStep ys count word)
    have hs : (countStep ys count word).length≤ys.length+count.length := by
      unfold countStep
      split_ifs <;> simp <;> omega
    change (context (countStep ys count word) ys pre).length≤_
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

theorem accumulated_body (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (pre : List (List Bool)) (word : List Bool) (suffix : List (List Bool))
    (hsplit : pre++word::suffix=words cs) :
    (SourceListEncoding.fields (words cs)++joined (piece j ys) pre).length≤
      (SourceListEncoding.fields (words (next j ys cs))).length := by
  have he := body_exact j ys cs
  have hp : (joined (piece j ys) pre).length≤(joined (piece j ys) (words cs)).length := by
    rw [←hsplit]
    simp only [joined,List.flatMap_append,List.flatMap_cons,List.length_append]
    omega
  have hlen := congrArg List.length he
  simp only [List.length_append] at *
  omega

theorem callback_size (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (hsplit : pre++word::suffix=words cs)
    (c : List (Nat × Nat)) (hc : c∈cs) (hw : word=CylinderFeatureCodec.encodeFeature c) :
    FeatureAlphabetClockBounds64.inputSize j c ys
      (SourceListEncoding.fields (words cs)++joined (piece j ys) pre)≤
      measure j ys cs qfuel jUnary carry := by
  obtain ⟨_,_,hword,_,_⟩ := split_bounds cs pre word suffix hsplit
  rw [hw] at hword
  have hbody := accumulated_body j ys cs pre word suffix hsplit
  have hext : (FeatureEligibleDescriptor96.extensions j c ys).length≤extensionBytes j ys cs := by
    apply List.le_sum_of_mem
    exact List.mem_map.mpr ⟨c,hc,rfl⟩
  dsimp only [measure,FeatureAlphabetClockBounds64.inputSize,
    FeatureAlphabetClockBounds64.extensions,FeatureEligibleDescriptor96.extensions,
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

theorem selected_length (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (hsplit : pre++word::suffix=words cs) (k : Fin 96) :
    (selected j ys qfuel jUnary carry pre word suffix
      (SourceListEncoding.fields (words cs)++joined (piece j ys) pre)
      (context (List.replicate cs.length true) ys pre) k).length≤
      (measure j ys cs qfuel jUnary carry+1)^2 := by
  let M := measure j ys cs qfuel jUnary carry
  have hM : M≤(M+1)^2 := by nlinarith
  obtain ⟨hp,ht,hw,hf,hpc⟩ := split_bounds cs pre word suffix hsplit
  have ho := accumulated_body j ys cs pre word suffix hsplit
  have hc := context_length_le (List.replicate cs.length true) ys pre
  simp only [List.length_replicate] at hc
  have hcount : (context (List.replicate cs.length true) ys pre).length≤(M+1)^2 := by
    have hys : ys.length≤M := by dsimp [M,measure]; omega
    have hcs : cs.length≤M := by dsimp [M,measure]; omega
    have hpM : pre.length≤M := hpc.trans hcs
    have hmul := Nat.mul_le_mul hys hpM
    nlinarith
  change (selected j ys qfuel jUnary carry pre word suffix
      (SourceListEncoding.fields (words cs)++joined (piece j ys) pre)
      (context (List.replicate cs.length true) ys pre) k).length≤(M+1)^2
  have hsM : (SourceListEncoding.encode (words cs)).length≤M := by dsimp [M,measure]; omega
  have hoM : (SourceListEncoding.fields (words (next j ys cs))).length≤M := by dsimp [M,measure]; omega
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
end CurrentAdditive.FeatureOuterMeasure96
