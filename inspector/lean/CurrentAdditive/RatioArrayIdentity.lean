import CurrentAdditive.RatioEncodedBounds

namespace CurrentAdditive.RatioEncodedBounds

theorem actual_array_words_eq_pairs (weights coeff : Array ℚ) :
    ratioWords (arrayItems weights coeff) =
      (MinimumRatioFoldSemanticJoin.pairs weights coeff).map
        (fun p => CodeDPairProductTargetV2.pairBytes p.1 p.2) := by
  simp [ratioWords, arrayItems, ratioWord,
    MinimumRatioFoldSemanticJoin.pairs, MinimumRatioFoldSemanticJoin.pairAt,
    CodeDCanonicalSourceV2.rawOfRat, GaussPhysical.rawOfRat, List.map_map,
    Function.comp_def]

theorem actual_array_fold_eq_minimumRatio (weights coeff : Array ℚ) :
    (ratioWords (arrayItems weights coeff)).foldl MinimumRatioStepSpec.step [] =
      MinimumRatioStepSpec.bestPacket (SequentialCode.minimumRatio weights coeff) := by
  have hfold : (arrayItems weights coeff).foldl
      (fun prev p => MinimumRatioStepSpec.semanticStep prev p.1 p.2) none =
      MinimumRatioFoldSemanticJoin.semanticFold
        (MinimumRatioFoldSemanticJoin.pairs weights coeff) := by
    simp [arrayItems, MinimumRatioFoldSemanticJoin.semanticFold,
      MinimumRatioFoldSemanticJoin.pairs, MinimumRatioFoldSemanticJoin.pairAt,
      List.foldl_map, GaussPhysical.rawOfRat_value]
  have hp := ratioWords_fold (arrayItems weights coeff) none
  rw [hfold, MinimumRatioFoldSemanticJoin.semanticFold_eq_minimumRatio] at hp
  exact hp

#print axioms actual_array_words_eq_pairs
#print axioms actual_array_fold_eq_minimumRatio

end CurrentAdditive.RatioEncodedBounds
