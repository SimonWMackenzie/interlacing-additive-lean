import CurrentAdditive.FeatureBoundedLift96
import CurrentAdditive.FeatureExtensionPolynomial64
import CurrentAdditive.CylinderRawInputProjection
import CurrentAdditive.StatefulFoldClock

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 100
noncomputable section
namespace CurrentAdditive.FeatureAlphabetClockBounds64
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CylinderFeatureCodec FeatureInnerAlphabetRun64 FeatureBoundedAlphabet64
open GaussListContext Wide64ContextListScheduler

def extensions (j : Nat) (c : List (Nat × Nat)) (ys : List Nat) :=
  SourceListEncoding.fields (ys.map fun y => encodeFeature ((j,y)::c))

def inputSize (j : Nat) (c : List (Nat × Nat)) (ys : List Nat) (body : List Bool) :=
  (SourceListEncoding.encode (original ys)).length+(encodeFeature c).length+
    j.bits.length+body.length+(extensions j c ys).length

theorem fields_append (xs ys : List (List Bool)) :
    SourceListEncoding.fields (xs++ys) =
      SourceListEncoding.fields xs++SourceListEncoding.fields ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [SourceListEncoding.fields,ih,List.append_assoc]

theorem split_bounds (ys : List Nat) (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (hsplit : pre++word::suffix=original ys) :
    let L := (SourceListEncoding.encode (original ys)).length
    pre.length ≤ L ∧ suffix.length ≤ L ∧ word.length ≤ L ∧
      (SourceListEncoding.fields suffix).length ≤ L ∧ (original ys).length ≤ L := by
  dsimp only
  have hm := CylinderRawInputProjection.input_measure_le (original ys)
  unfold CylinderProductionProjectionClock.inputMeasure at hm
  have hcount : pre.length+1+suffix.length=(original ys).length := by
    simpa [List.length_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using congrArg List.length hsplit
  have ht : SourceListEncoding.totalLength (original ys) =
      SourceListEncoding.totalLength pre+word.length+SourceListEncoding.totalLength suffix := by
    rw [←hsplit]
    simp [SourceListEncoding.totalLength,List.sum_append,Nat.add_assoc]
  have hf : (SourceListEncoding.fields suffix).length ≤
      (SourceListEncoding.encode (original ys)).length := by
    rw [←hsplit]
    simp only [SourceListEncoding.encode,fields_append,SourceListEncoding.fields,List.length_append]
    omega
  exact ⟨by omega,by omega,by omega,hf,by omega⟩

theorem extension_split_bounds (j : Nat) (c : List (Nat × Nat)) (ys : List Nat)
    (pre : List (List Bool)) (word : List Bool) (suffix : List (List Bool))
    (hsplit : pre++word::suffix=original ys) :
    (joined (piece j c) pre).length ≤ (extensions j c ys).length ∧
      (piece j c word).length ≤ (extensions j c ys).length := by
  have he : extensions j c ys = joined (piece j c) (pre++word::suffix) := by
    rw [hsplit]
    exact (joined_exact j c ys).symm
  rw [he]
  simp only [joined,List.flatMap_append,List.flatMap_cons,List.length_append]
  omega

theorem selected_length (j : Nat) (c : List (Nat × Nat))
    (pre : List (List Bool)) (word : List Bool) (suffix : List (List Bool))
    (out : List Bool) (M : Nat)
    (hs : (SourceListEncoding.encode (pre++word::suffix)).length ≤ M)
    (hf : (SourceListEncoding.fields suffix).length ≤ M) (hw : word.length ≤ M)
    (hp : pre.length ≤ M) (ht : suffix.length ≤ M) (ho : out.length ≤ M)
    (hj : j.bits.length ≤ M) (hc : (encodeFeature c).length ≤ M) (k : Fin 64) :
    (selected j c pre word suffix out k).length ≤ M := by
  by_cases hk : ∃ i,Wide64ContextPreservingScan.locate i=k
  · obtain ⟨i,rfl⟩ := hk
    unfold selected
    rw [Wide64ContextPreservingScan.frame_bank]
    fin_cases i <;> simp [CylinderContextScanStep.selectedBank] <;> omega
  · unfold selected
    rw [Wide64ContextPreservingScan.frame_foreign _ _ k hk]
    simp only [foreignBank,extra,Function.update_apply]
    split_ifs <;> simp_all

theorem selected_bankSize (j : Nat) (c : List (Nat × Nat)) (ys : List Nat)
    (body : List Bool) (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (hsplit : pre++word::suffix=original ys) :
    FeatureBoundedExtension64.bankSize
      (selected j c pre word suffix (body++joined (piece j c) pre)) ≤
        64*inputSize j c ys body := by
  obtain ⟨hp,ht,hw,hf,_⟩ := split_bounds ys pre word suffix hsplit
  obtain ⟨hpre,_⟩ := extension_split_bounds j c ys pre word suffix hsplit
  have hk (k : Fin 64) :
      (selected j c pre word suffix (body++joined (piece j c) pre) k).length ≤
        inputSize j c ys body := by
    apply selected_length
    all_goals dsimp only [inputSize]
    · rw [hsplit]; omega
    · omega
    · omega
    · omega
    · omega
    · simp only [List.length_append]; omega
    · omega
    · omega
  unfold FeatureBoundedExtension64.bankSize
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun k _ => hk k)
  simpa using h

#print axioms selected_bankSize
end CurrentAdditive.FeatureAlphabetClockBounds64
