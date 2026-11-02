import CurrentAdditive.StoredQueryMap

namespace CurrentAdditive.StoredQuery
open EthInapproximability.CurrentPaper
noncomputable section

theorem flat_equal (xs : List (List Bool)) (f g : List Bool → List Bool)
    (h : ∀w∈xs,f w=g w) : xs.flatMap f=xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons w xs ih =>
    simp only [List.flatMap_cons]
    rw [h w (by simp),ih (fun v hv => h v (by simp [hv]))]

theorem map_result (A : Query) (framed : Bool) (context : List Bool)
    (xs : List (List Bool)) (f : List Bool → List Bool)
    (h : ∀w∈xs,A.result (FeatureMapPairLoader.packet context w)=some (f w)) :
    (mapItems A framed).result
      (FeatureMapPairLoader.packet context (SourceListEncoding.encode xs))=
      some (FeatureContextMap.result framed xs f) := by
  have hv : validItems A context xs := by
    intro w hw
    simp [h w hw]
  have hh := mapResult_packet A framed context xs hv
  have hf : ∀w∈xs,answers A context w=f w := by
    intro w hw
    simp [answers,h w hw]
  have hm : xs.map (answers A context)=xs.map f := List.map_congr_left hf
  have hflat := flat_equal xs (answers A context) f hf
  cases framed <;> simpa only [mapItems,FeatureContextMap.result,
    Bool.false_eq_true,if_false,if_true,hm,hflat] using hh

end
end CurrentAdditive.StoredQuery

#print axioms CurrentAdditive.StoredQuery.map_result
