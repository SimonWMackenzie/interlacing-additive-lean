import CurrentAdditive.SequentialDimensionPolynomialProduction
import CurrentAdditive.SequentialFiniteLaw
import CurrentAdditive.DeterministicIndexedMatrix

/-! The literal sequential array supplies the paper's indexed source carrier. -/

namespace CurrentAdditive.ExecutableCodeSource

open SequentialCode SequentialSourceCode SequentialFeatureCoverage
  SequentialFiniteLaw SequentialSourceResource SequentialAppendMoments
  SequentialDimensionPolynomialProduction Paper2
  CurrentAdditive.DeterministicIndexedMatrix

/-- This branch is a match on the actual executable result. The impossible
`none` branch is eliminated using the proved totality for positive arrays. -/
def fromAlphabet {Y : Type} [Fintype Y] [DecidableEq Y]
    (D q : Nat) (μ : PositiveRationalLaw Y)
    (alphabet : Array (Y × ℚ))
    (hpositive : SourcePositive alphabet)
    (halphabet : sourceMass alphabet = 1)
    (hcover : ∀ y : Y, y ∈ (alphabet.map Prod.fst).toList)
    (hpoint : ∀ y, alphabetPointMass alphabet y = μ.weight y) :
    CodeSource D q Y μ :=
  let hsome : (sequentialMaterialized D alphabet q).isSome := by
    obtain ⟨out, hout, _⟩ := sequentialMaterialized_total D alphabet hpositive q
    simp [hout]
  let out := (sequentialMaterialized D alphabet q).get hsome
  let hout : sequentialMaterialized D alphabet q = some out := by
    cases h : sequentialMaterialized D alphabet q with
    | none => simp [h] at hsome
    | some result => simp [out, h]
  let houtpositive : SourcePositive out := by
    obtain ⟨out', hout', hp⟩ := sequentialMaterialized_total D alphabet hpositive q
    rw [hout] at hout'
    cases hout'
    exact hp
  let houtmass : sourceMass out = 1 :=
    sequentialMaterialized_mass D alphabet halphabet q out hout
  {
    Label := Fin out.size
    finite := inferInstance
    decEq := inferInstance
    law := indexedLaw out houtpositive houtmass
    decode := fun j => out[j].1
    exactLaw := sequential_indexed_dwise D alphabet halphabet hcover μ hpoint
      q out hout houtpositive houtmass
  }

theorem fromAlphabet_label_bound {Y : Type} [Fintype Y] [DecidableEq Y]
    (D q : Nat) (μ : PositiveRationalLaw Y)
    (alphabet : Array (Y × ℚ))
    (hpositive : SourcePositive alphabet)
    (halphabet : sourceMass alphabet = 1)
    (hcover : ∀ y : Y, y ∈ (alphabet.map Prod.fst).toList)
    (hpoint : ∀ y, alphabetPointMass alphabet y = μ.weight y) :
    Fintype.card (fromAlphabet D q μ alphabet hpositive halphabet hcover hpoint).Label ≤
      (1 + q * alphabet.size) ^ D := by
  unfold fromAlphabet
  dsimp
  let hsome : (sequentialMaterialized D alphabet q).isSome := by
    obtain ⟨out, hout, _⟩ := sequentialMaterialized_total D alphabet hpositive q
    simp [hout]
  let out := (sequentialMaterialized D alphabet q).get hsome
  have hout : sequentialMaterialized D alphabet q = some out := by
    cases h : sequentialMaterialized D alphabet q with
    | none => simp [h] at hsome
    | some result => simp [out, h]
  have hsize := sequentialMaterialized_size_le_features_all D alphabet q out hout
  simpa [out] using hsize.trans
    (generatedFeatures_size_le_polynomial q D (alphabet.map Prod.fst))

#print axioms fromAlphabet
#print axioms fromAlphabet_label_bound

end CurrentAdditive.ExecutableCodeSource
