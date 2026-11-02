import EthInapproximability.CurrentPaper.GenericAtLeastLoop
import EthInapproximability.CurrentPaper.GenericPairVertexLoop

namespace EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.PrefixLoopSource

open SourceBooleanEncoding SourceClauseEncoding EncodedCNF
open SourceGenericPairEnumeration
open List
open scoped Classical

private theorem range_eq_ofFn (r : Nat) :
    List.range r = List.ofFn (fun i : Fin r => i.val) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

private theorem flatMap_eq_flatten_map {α β : Type*}
    (xs : List α) (f : α → List β) :
    xs.flatMap f = (xs.map f).flatten := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

private theorem fields_append (xs ys : List Clause) :
    clauseFields (xs ++ ys) = clauseFields xs ++ clauseFields ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [clauseFields,ih,List.append_assoc]

theorem fields_flatten (xs : List (List Clause)) :
    clauseFields xs.flatten = (xs.map clauseFields).flatten := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [fields_append,ih]

theorem atLeast_fields (n a q : Nat) :
    AtLeastLoop.prefixFields n a q n =
      clauseFields (SourceGenericPrefix.atLeastChains n a q) := by
  unfold SourceGenericPrefix.atLeastChains
  rw [fields_flatten]
  simp only [AtLeastLoop.prefixFields,range_eq_ofFn,
    flatMap_eq_flatten_map,List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext v
  have hv : v.val < n := v.isLt
  simp [AtLeastLoop.word,hv,SourceGenericPrefix.atLeastOrdinal]

theorem pair_fields (n a q : Nat) :
    PairVertexLoop.prefixFields n a q n =
      clauseFields (SourceGenericPrefix.pairChains n a q) := by
  unfold SourceGenericPrefix.pairChains
  rw [fields_flatten]
  simp only [PairVertexLoop.prefixFields,range_eq_ofFn,
    flatMap_eq_flatten_map,List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext v
  have hv : v.val < n := v.isLt
  simp [PairVertexLoop.word,hv,vertexChains_eq_source]

#print axioms atLeast_fields
#print axioms pair_fields

end EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.PrefixLoopSource
