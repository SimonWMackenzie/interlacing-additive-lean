import CurrentAdditive.RatioPairItem
import CurrentAdditive.IndexedV2Clock

namespace CurrentAdditive.RatioPairListSpec
open EthInapproximability.CurrentPaper CurrentAdditive.GaussListContext

def coefficient (coeff : List (List Bool)) (i : Nat) : List Bool :=
  (coeff[i]?).getD []
noncomputable def pairs (records coeff : List (List Bool)) : List (List Bool) :=
  records.mapIdx (fun i word => RatioPairItem.pairWord word (coefficient coeff i))
noncomputable def outputAt (count : Nat) (coeff : List (List Bool))
    (pre : List (List Bool)) : List Bool :=
  EncodedCommunication.natField count ++ SourceListEncoding.fields (pairs pre coeff)

theorem pairs_append (pre : List (List Bool)) (word : List Bool)
    (coeff : List (List Bool)) :
    pairs (pre ++ [word]) coeff = pairs pre coeff ++
      [RatioPairItem.pairWord word (coefficient coeff pre.length)] :=
  List.mapIdx_concat

theorem outputAt_append (count : Nat) (coeff : List (List Bool))
    (pre : List (List Bool)) (word : List Bool) :
    outputAt count coeff (pre ++ [word]) = outputAt count coeff pre ++
      V2FieldContext.field (RatioPairItem.pairWord word (coefficient coeff pre.length)) := by
  unfold outputAt
  rw [pairs_append,IndexedV2Clock.fields_append]
  simp only [SourceListEncoding.fields,List.append_nil,V2FieldContext.field,List.append_assoc]

theorem coefficient_split (coeff : List (List Bool)) (i : Nat) (hi : i < coeff.length) :
    coeff.take i ++ coefficient coeff i :: coeff.drop (i+1) = coeff := by
  have he : coefficient coeff i = coeff[i] := by
    simp [coefficient,List.getElem?_eq_getElem hi]
  rw [he,← List.drop_eq_getElem_cons hi,List.take_append_drop]

theorem coefficient_prefix_length (coeff : List (List Bool)) (i : Nat)
    (hi : i < coeff.length) : (coeff.take i).length = i := by
  simp [List.length_take,Nat.min_eq_left (Nat.le_of_lt hi)]

theorem outputAt_nil (count : Nat) (coeff : List (List Bool)) :
    outputAt count coeff [] = EncodedCommunication.natField count := by
  simp [outputAt,pairs,SourceListEncoding.fields]

theorem outputAt_all (records coeff : List (List Bool)) :
    outputAt records.length coeff records = SourceListEncoding.encode (pairs records coeff) := by
  simp only [outputAt,SourceListEncoding.encode,pairs,List.length_mapIdx]

end CurrentAdditive.RatioPairListSpec
