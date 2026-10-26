import EthInapproximability.CurrentPaper.GenericPrefixAtLeastCircuit

namespace EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.AtLeastSource

open SourceBooleanEncoding SourceClauseEncoding EncodedCNF
open SourceBooleanPrefix SourceGenericPrefix AtLeastCircuit

theorem gateFold_eq_reverse {n a q : Nat} (v : Fin n)
    (ss : List (Fin a)) (saved : List Bool) :
    gateFold (q := q) v ss saved =
      (ss.flatMap (gatePayload (q := q) v)).reverse ++ saved := by
  induction ss generalizing saved with
  | nil => simp [gateFold]
  | cons s ss ih =>
      rw [gateFold,ih]
      simp [List.reverse_append,List.append_assoc]

theorem opening_eq {n a q : Nat} (v : Fin n) (saved : List Bool) :
    UnitHandoff.nextSaved n a v.val (width a q + 1) 0
      false saved =
      (encodeClause (unit (SourceClauseEncoding.negative
        (SourceGenericPrefix.base n a q v.val)))).reverse ++ saved := by
  simp [UnitHandoff.nextSaved,
    SourceClauseUnitMachine.unitClause,SourceGenericPrefix.base]
  simp [SourceClauseEncoding.negative]
  ring

theorem closing_eq {n a q : Nat} (v : Fin n) (saved : List Bool) :
    UnitHandoff.nextSaved n a v.val (width a q + 1) a
      true saved =
      (encodeClause (unit (SourceClauseEncoding.positive
        (SourceGenericPrefix.base n a q v.val + a)))).reverse ++ saved := by
  simp [UnitHandoff.nextSaved,
    SourceClauseUnitMachine.unitClause,SourceGenericPrefix.base]
  simp [SourceClauseEncoding.positive]
  ring

private theorem zipIdx_ofFn {α : Type*} (xs : List α) :
    xs.zipIdx = List.ofFn (fun j : Fin xs.length => (xs.get j,j.val)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_zipIdx,List.getElem_ofFn,Nat.zero_add,
      List.get_eq_getElem]

private theorem clauseFields_append (xs ys : List Clause) :
    clauseFields (xs ++ ys) = clauseFields xs ++ clauseFields ys := by
  induction xs with
  | nil => rfl
  | cons c cs ih =>
      simp only [List.cons_append,clauseFields,ih,List.append_assoc]

private theorem clauseFields_flatMap {α : Type*} (ds : List α)
    (f : α → List Clause) :
    clauseFields (ds.flatMap f) =
      ds.flatMap (fun d => clauseFields (f d)) := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
      simp only [List.flatMap_cons,clauseFields_append,ih]

theorem saved_eq_source {n a q : Nat} (v : Fin n)
    (saved : List Bool) :
    let w := width a q + 1
    let opening := UnitHandoff.nextSaved
      n a v.val w 0 false saved
    let middle := gateFold (q := q) v
      (List.ofFn (fun s : Fin a => s)) opening
    UnitHandoff.nextSaved n a v.val w a true middle =
      (clauseFields (chain
        (SourceGenericPrefix.base n a q v.val)
        (SourceGenericPrefix.atLeastPayload (a := a) v))).reverse ++
        saved := by
  dsimp
  rw [opening_eq,closing_eq,gateFold_eq_reverse]
  unfold chain
  simp only [clauseFields_append,clauseFields_flatMap,
    List.reverse_append,List.append_assoc]
  have hz := zipIdx_ofFn
    (SourceGenericPrefix.atLeastPayload (a := a) v)
  simp only [SourceGenericPrefix.atLeast_length] at hz
  rw [hz]
  simp [SourceGenericPrefix.atLeastPayload,List.flatMap,
    List.map_ofFn,Function.comp_def,gatePayload,clauseFields,
    List.reverse_flatMap]

theorem source_run {n a q : Nat} (v : Fin n)
    (saved output count : List Bool) :
    SourceClauseCallback.Circuit.Run (AtLeastCircuit.atLeastCircuit a q)
      (PrefixGateReady.blank n v.val saved output count)
      (PrefixGateReady.blank n v.val
        ((clauseFields (chain
          (SourceGenericPrefix.base n a q
            (SourceGenericPrefix.atLeastOrdinal v))
          (SourceGenericPrefix.atLeastPayload (a := a) v))).reverse ++
          saved)
        output (List.replicate (3*a+2) true ++ count)) := by
  have h := AtLeastCircuit.callback_run (a := a) (q := q) v saved output count
  dsimp at h
  rw [saved_eq_source (q := q) v saved] at h
  simpa only [SourceGenericPrefix.atLeastOrdinal] using h

#print axioms saved_eq_source
#print axioms source_run

end EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.AtLeastSource
