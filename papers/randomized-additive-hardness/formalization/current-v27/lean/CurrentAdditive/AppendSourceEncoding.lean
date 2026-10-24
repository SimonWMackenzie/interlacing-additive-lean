import CurrentAdditive.AppendEntryCanonical

namespace CurrentAdditive.AppendSourceEncoding
open EthInapproximability.CurrentPaper
open CodeDSourceCodecV2 CodeDCanonicalSourceV2
noncomputable section

def pairResult (x y : List Bool) := AppendEntryPhysical.producer.result
  (BitMachineBankCodec.encode (![x,y] : Fin 2 → List Bool))

def orderedBody (xs ys : List (List Bool)) := xs.flatMap (fun x =>
  SourceListEncoding.fields (ys.map (pairResult x)))

def output (xs ys : List (List Bool)) :=
  EncodedCommunication.natField (xs.length*ys.length) ++ orderedBody xs ys

def sourceItems {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) :=
  (canonicalSource source).map encodeEntry

def alphabetItems (alphabet : Array (Nat × ℚ)) := alphabet.toList.map CodeDTargetV2.alphabetEntry

theorem pair_result {q : Nat} (x : (Fin q → Nat) × ℚ) (y : Nat × ℚ) :
    pairResult (encodeEntry (canonicalEntry x)) (CodeDTargetV2.alphabetEntry y) =
      encodeEntry (canonicalEntry (SequentialCode.appendWord x.1 y.1,x.2*y.2)) := by
  have h := AppendEntryPhysical.result_packet (canonicalEntry x) y (canonicalEntry_valid x)
  rw [AppendEntryCanonical.canonical_append] at h
  exact h

theorem body_semantics {q : Nat} (xs : List ((Fin q → Nat) × ℚ)) (ys : List (Nat × ℚ)) :
    orderedBody
      (xs.map (fun x => encodeEntry (canonicalEntry x))) (ys.map CodeDTargetV2.alphabetEntry) =
    SourceListEncoding.fields ((xs.flatMap (fun x =>
      ys.map (fun y => encodeEntry (canonicalEntry (SequentialCode.appendWord x.1 y.1,x.2*y.2)))))) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hr : (ys.map CodeDTargetV2.alphabetEntry).map
        (pairResult (encodeEntry (canonicalEntry x))) =
        ys.map (fun y => encodeEntry (canonicalEntry (SequentialCode.appendWord x.1 y.1,x.2*y.2))) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro y hy
      exact pair_result x y
    change SourceListEncoding.fields ((ys.map CodeDTargetV2.alphabetEntry).map
      (pairResult (encodeEntry (canonicalEntry x)))) ++
      orderedBody
        (xs.map (fun x => encodeEntry (canonicalEntry x))) (ys.map CodeDTargetV2.alphabetEntry) = _
    rw [hr,ih,List.flatMap_cons,AppendEntryPhysical.fields_append]

theorem flatMap_length {α β γ : Type*} (xs : List α) (ys : List β) (f : α → β → γ) :
    (xs.flatMap (fun x => ys.map (f x))).length = xs.length*ys.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih,Nat.succ_mul,Nat.add_comm]

theorem output_exact {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) (alphabet : Array (Nat × ℚ)) :
    output (sourceItems source) (alphabetItems alphabet) =
      encodedSource (SequentialCode.appendSource source alphabet) := by
  have hb := body_semantics source.toList alphabet.toList
  have hmap : ((CodeDAppendTargetV2.appendedList source alphabet).map canonicalEntry).map encodeEntry =
      source.toList.flatMap (fun x => alphabet.toList.map (fun y =>
        encodeEntry (canonicalEntry (SequentialCode.appendWord x.1 y.1,x.2*y.2)))) := by
    simp [CodeDAppendTargetV2.appendedList,List.map_flatMap,List.map_map,Function.comp_def]
  have hlen := flatMap_length source.toList alphabet.toList
    (fun x y => encodeEntry (canonicalEntry (SequentialCode.appendWord x.1 y.1,x.2*y.2)))
  simp only [Array.length_toList] at hlen
  rw [CodeDAppendTargetV2.appendSource_encoded_order]
  unfold output sourceItems alphabetItems
  rw [show canonicalSource source = source.toList.map canonicalEntry from rfl]
  simp only [List.map_map,Function.comp_def]
  rw [hb]
  unfold encodeSource CodeDCodecV2.encodeItems SourceListEncoding.encode
  rw [hmap,hlen]
  simp only [List.length_map,Array.length_toList]

#print axioms output_exact
end
end CurrentAdditive.AppendSourceEncoding
