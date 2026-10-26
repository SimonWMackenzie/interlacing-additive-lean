import CurrentAdditive.StoredQueryMap

namespace CurrentAdditive.StoredQuery
open EthInapproximability.CurrentPaper
noncomputable section

theorem map_ofFn_result (A : Query) (framed : Bool) (context : List Bool)
    {n : Nat} (input output : Fin n → List Bool)
    (h : ∀i,A.result (FeatureMapPairLoader.packet context (input i))=some (output i)) :
    (mapItems A framed).result
      (FeatureMapPairLoader.packet context (SourceListEncoding.encode (List.ofFn input)))=
      some (if framed then SourceListEncoding.encode (List.ofFn output) else (List.ofFn output).flatten) := by
  have hv : validItems A context (List.ofFn input) := by
    intro w hw
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    simp [h i]
  have hm : (List.ofFn input).map (answers A context)=List.ofFn output := by
    simp only [List.map_ofFn]
    congr 1
    funext i
    simp [answers,h i]
  have hh := mapResult_packet A framed context (List.ofFn input) hv
  simpa only [mapItems,FeatureContextMap.result,List.flatMap_def,hm] using hh

end
end CurrentAdditive.StoredQuery

#print axioms CurrentAdditive.StoredQuery.map_ofFn_result
