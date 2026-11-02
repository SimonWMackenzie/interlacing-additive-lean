import CurrentAdditive.RatioUpdateAppendItem
import CurrentAdditive.IndexedV2Clock

set_option maxHeartbeats 600000
namespace CurrentAdditive.RatioRequestListSpec
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.GaussListContext

noncomputable def coefficient (coeff : List (List Bool)) (i : Nat) : List Bool :=
  (coeff[i]?).getD []
noncomputable def requests (records coeff : List (List Bool)) (lambda : List Bool) :
    List (List Bool) :=
  records.mapIdx (fun i word => RatioRequestSerializer.bytes word lambda (coefficient coeff i))
noncomputable def outputAt (count : Nat) (coeff : List (List Bool)) (lambda : List Bool)
    (pre : List (List Bool)) : List Bool :=
  EncodedCommunication.natField count ++ SourceListEncoding.fields (requests pre coeff lambda)

theorem requests_append (pre : List (List Bool)) (word : List Bool)
    (coeff : List (List Bool)) (lambda : List Bool) :
    requests (pre ++ [word]) coeff lambda = requests pre coeff lambda ++
      [RatioRequestSerializer.bytes word lambda (coefficient coeff pre.length)] := by
  exact List.mapIdx_concat

theorem outputAt_append (count : Nat) (coeff : List (List Bool))
    (lambda : List Bool) (pre : List (List Bool)) (word : List Bool) :
    outputAt count coeff lambda (pre ++ [word]) = outputAt count coeff lambda pre ++
      V2FieldContext.field (RatioRequestSerializer.bytes word lambda
        (coefficient coeff pre.length)) := by
  unfold outputAt
  rw [requests_append,IndexedV2Clock.fields_append]
  simp only [SourceListEncoding.fields,List.append_nil,V2FieldContext.field,List.append_assoc]

theorem coefficient_split (coeff : List (List Bool)) (i : Nat) (hi : i < coeff.length) :
    coeff.take i ++ coefficient coeff i :: coeff.drop (i+1) = coeff := by
  have he : coefficient coeff i = coeff[i] := by
    simp [coefficient,List.getElem?_eq_getElem hi]
  rw [he,← List.drop_eq_getElem_cons hi,List.take_append_drop]

theorem coefficient_prefix_length (coeff : List (List Bool)) (i : Nat)
    (hi : i < coeff.length) : (coeff.take i).length = i := by
  simp [List.length_take,Nat.min_eq_left (Nat.le_of_lt hi)]

theorem request_length (records coeff : List (List Bool)) (lambda : List Bool) :
    (requests records coeff lambda).length = records.length := by
  simp [requests]

theorem outputAt_nil (count : Nat) (coeff : List (List Bool)) (lambda : List Bool) :
    outputAt count coeff lambda [] = EncodedCommunication.natField count := by
  simp [outputAt,requests,SourceListEncoding.fields]

theorem outputAt_all (records coeff : List (List Bool)) (lambda : List Bool) :
    outputAt records.length coeff lambda records =
      SourceListEncoding.encode (requests records coeff lambda) := by
  simp only [outputAt,SourceListEncoding.encode,request_length]

#print axioms coefficient_split
#print axioms outputAt_all
end CurrentAdditive.RatioRequestListSpec
