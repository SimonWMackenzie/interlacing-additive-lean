import CurrentAdditive.StoredSourceQueries

namespace CurrentAdditive.StoredSourceQueries
open EthInapproximability.CurrentPaper StoredQuery StoredCellQueries
noncomputable section
attribute [local instance] Classical.propDecidable

theorem conjunction_all (e : Bool) (xs : List Bool) :
    CylinderConjunctionMachine.conjunction e xs=(e && xs.all id) := by
  induction xs generalizing e with
  | nil => simp [CylinderConjunctionMachine.conjunction]
  | cons b xs ih =>
    simpa only [CylinderConjunctionMachine.conjunction,List.foldl_cons,List.all_cons,
      id_eq,Bool.and_assoc] using ih (e && b)

theorem ordinaryDiagonal_result {s m n : Nat} (x : List Bool)
    (a : Fin m) (f : Fin s → Fin m × Fin n)
    (ha : firstCoordinate.result x=some a.val.bits)
    (ht : (companion 1).result x=some
      (SourceListEncoding.encode (StoredCellBytes.productCompanions m n)))
    (hw : ordinaryOuterWord.result x=some (StoredCellBytes.tuple
      (fun p => (finProdFinEquiv (f p)).val))) :
    ordinaryDiagonal.result x=some [decide (∀p,(f p).1=a)] := by
  let ctx := BitMachineBankCodec.encode ![a.val.bits,
    SourceListEncoding.encode (StoredCellBytes.productCompanions m n)]
  let xs := List.ofFn (fun p => (finProdFinEquiv (f p)).val.bits)
  have hv : validItems compareHead ctx xs := by
    intro word hword
    obtain ⟨p,hp⟩ := List.mem_ofFn.mp hword
    subst word
    rw [compareHead_packet]
    rfl
  have hans (p : Fin s) : answers compareHead ctx (finProdFinEquiv (f p)).val.bits=
      [decide ((f p).1=a)] := by
    simp only [answers,ctx,compareHead_packet,Option.getD_some]
  have hp := pair_result firstCoordinate (companion 1) x _ _ ha ht
  have hpacket := pair_result (pair firstCoordinate (companion 1)) ordinaryOuterWord x _ _ hp hw
  have hmap := mapResult_packet compareHead false ctx xs hv
  have hc : ordinaryComparisons.result x=some
      (List.ofFn (fun p => decide ((f p).1=a))) := by
    have h := compose_result ordinaryComparisonPacket (mapItems compareHead false) x _ _ hpacket hmap
    have he : xs.flatMap (answers compareHead ctx)=
        List.ofFn (fun p => decide ((f p).1=a)) := by
      have hxs : xs=(List.ofFn (id : Fin s → Fin s)).map
          (fun p => (finProdFinEquiv (f p)).val.bits) := by simp [xs,List.map_ofFn]
      rw [hxs,List.flatMap_map]
      simp only [Function.comp_def,hans]
      rw [← List.map_eq_flatMap,List.map_ofFn]
      rfl
    simpa only [ordinaryComparisons,mapItems,FeatureContextMap.result,Bool.false_eq_true,
      ↓reduceIte,he] using h
  have hconj : CylinderConjunctionMachine.conjunction true
      (List.ofFn (fun p => decide ((f p).1=a)))=decide (∀p,(f p).1=a) := by
    rw [conjunction_all,Bool.true_and]
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true,decide_eq_true_eq,id_eq]
    constructor
    · intro h p; simpa only [decide_eq_true_eq] using h _ (List.mem_ofFn.mpr ⟨p,rfl⟩)
    · intro h y hy
      obtain ⟨p,rfl⟩ := List.mem_ofFn.mp hy
      simpa only [decide_eq_true_eq] using h p
  exact compose_result ordinaryComparisons (total StoredCellPrimitives.conjunction) x _ _ hc
    (by simp [total,StoredCellPrimitives.conjunction,hconj])

end
end CurrentAdditive.StoredSourceQueries

#print axioms CurrentAdditive.StoredSourceQueries.ordinaryDiagonal_result
