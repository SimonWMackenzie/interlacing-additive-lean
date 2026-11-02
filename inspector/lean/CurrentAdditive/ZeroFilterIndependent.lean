import CurrentAdditive.ZeroFilterNormalized

namespace CurrentAdditive.LabelTrace

open SequentialCode SequentialSourceCode IndependentSupport

/-- The normalized arbitrary-law wrapper still stops at genuine linear
independence of the literal generated feature columns. -/
theorem sequentialPreprocessed_columns_independent {Y : Type*}
    [DecidableEq Y] (D : Nat) (alphabet : Array (Y × ℚ))
    (q : Nat) (out : Array ((Fin (q + 1) → Y) × ℚ))
    (hout : sequentialPreprocessed D alphabet (q + 1) = some out) :
    ColumnIndependent (featureRows
      (generatedFeatures (q + 1) D ((positiveLaw alphabet).map Prod.fst)).size
      (fun v j => generatedFeatureValue v
        (generatedFeatures (q + 1) D ((positiveLaw alphabet).map Prod.fst))[j])
      out) :=
  sequentialIndependent_columns_independent D (positiveLaw alphabet) q out hout

#print axioms sequentialPreprocessed_columns_independent

end CurrentAdditive.LabelTrace
