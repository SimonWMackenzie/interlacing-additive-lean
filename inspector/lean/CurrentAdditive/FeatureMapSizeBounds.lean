import CurrentAdditive.ContextMapClockModel
import CurrentAdditive.FeatureMapInitialize
import CurrentAdditive.StatefulFoldClock
import EthInapproximability.CurrentPaper.EntryClockPolyFrame

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 100
noncomputable section
namespace CurrentAdditive.FeatureMapSizeBounds
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open GaussListContext FeatureMapPairLoader FeatureMapInvoke

def inputSize (context : List Bool) (xs : List (List Bool)) :=
  (packet context (SourceListEncoding.encode xs)).length

theorem basic_bounds (context : List Bool) (xs : List (List Bool)) :
    context.length ≤ inputSize context xs ∧
    (SourceListEncoding.encode xs).length ≤ inputSize context xs ∧
    xs.length ≤ inputSize context xs := by
  have hpacket := packet_length context (SourceListEncoding.encode xs)
  have hc := GaussSearchClock.rows_le_code xs
  dsimp only [inputSize]
  omega

theorem packet_item_le (context : List Bool) (xs : List (List Bool))
    (w : List Bool) (hw : w∈xs) : (packet context w).length ≤ inputSize context xs := by
  have hword := IndexedV2Clock.fields_item_length_le xs w hw
  unfold inputSize
  rw [packet_length,packet_length]
  have hfields : (SourceListEncoding.fields xs).length ≤ (SourceListEncoding.encode xs).length := by
    simp [SourceListEncoding.encode]
  omega

theorem word_le (context : List Bool) (xs : List (List Bool))
    (w : List Bool) (hw : w∈xs) : w.length ≤ inputSize context xs := by
  have hp := packet_item_le context xs w hw
  rw [packet_length] at hp
  omega

theorem fields_append (xs ys : List (List Bool)) :
    SourceListEncoding.fields (xs++ys)=SourceListEncoding.fields xs++SourceListEncoding.fields ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [SourceListEncoding.fields,ih,List.append_assoc]

theorem cut_bounds (context : List Bool) (xs pre : List (List Bool))
    (w : List Bool) (suf : List (List Bool)) (hs : pre++w::suf=xs) :
    pre.length ≤ inputSize context xs ∧
    (SourceListEncoding.fields suf).length ≤ inputSize context xs ∧
    (packet context w).length ≤ inputSize context xs ∧ w.length ≤ inputSize context xs := by
  obtain ⟨hc,hsource,hcount⟩ := basic_bounds context xs
  have hp : pre.length ≤ xs.length := by rw [←hs]; simp
  have hf : (SourceListEncoding.fields suf).length ≤ (SourceListEncoding.encode xs).length := by
    rw [←hs]
    simp only [SourceListEncoding.encode,fields_append,SourceListEncoding.fields,List.length_append]
    omega
  have hw : w∈xs := by rw [←hs]; simp
  exact ⟨hp.trans hcount,hf.trans hsource,packet_item_le context xs w hw,word_le context xs w hw⟩

theorem piece_length (framed : Bool) (word : List Bool) :
    (FeatureMapInvoke.piece framed word).length ≤ 3*word.length+1 := by
  have h := EncodedGraph.natField_length_upper word.length
  cases framed <;> simp only [FeatureMapInvoke.piece,Bool.false_eq_true,if_false,if_true,List.length_append]
  · omega
  · omega

theorem header_length (framed : Bool) (n : Nat) :
    (FeatureMapHeaders.output framed n).length ≤ 2*n+1 := by
  have h := EncodedGraph.natField_length_upper n
  cases framed <;> simp only [FeatureMapHeaders.output,Bool.false_eq_true,if_false,if_true,List.length_nil]
  · omega
  · exact h

theorem joined_length (framed : Bool) (f : List Bool → List Bool)
    (xs : List (List Bool)) (Q : Nat) (hQ : ∀ w∈xs,(f w).length ≤ Q) :
    (FeatureMapSourceScheduler.joined (FeatureMapContract.piece framed f) xs).length ≤
      xs.length*(3*Q+1) := by
  induction xs with
  | nil => simp [FeatureMapSourceScheduler.joined]
  | cons w xs ih =>
    have hw := (piece_length framed (f w)).trans (Nat.add_le_add_right (Nat.mul_le_mul_left 3 (hQ w (by simp))) 1)
    have ht := ih (fun v hv => hQ v (by simp [hv]))
    simp only [FeatureMapSourceScheduler.joined,List.flatMap_cons,List.length_append,List.length_cons]
    change (FeatureMapInvoke.piece framed (f w)).length+
      (FeatureMapSourceScheduler.joined (FeatureMapContract.piece framed f) xs).length ≤ _
    nlinarith

theorem prefix_output (framed : Bool) (context : List Bool) (xs pre : List (List Bool))
    (w : List Bool) (suf : List (List Bool)) (hs : pre++w::suf=xs)
    (f : List Bool → List Bool) (Q : Nat) (hQ : ∀ w∈xs,(f w).length ≤ Q) :
    (FeatureMapHeaders.output framed xs.length++
      FeatureMapSourceScheduler.joined (FeatureMapContract.piece framed f) pre).length ≤
      2*inputSize context xs+1+inputSize context xs*(3*Q+1) := by
  obtain ⟨hp,_,_,_⟩ := cut_bounds context xs pre w suf hs
  have hc := (basic_bounds context xs).2.2
  have hh := header_length framed xs.length
  have hj := joined_length framed f pre Q (fun v hv => hQ v (by rw [←hs]; simp [hv]))
  have hm := Nat.mul_le_mul_right (3*Q+1) hp
  simp only [List.length_append]
  omega

#print axioms prefix_output
end CurrentAdditive.FeatureMapSizeBounds
