import CurrentAdditive.SmallBiasFieldMatrix

/-!
# Indexed small-bias matrix over an arbitrary binary extension field

Source: v27 Appendix G, `yao:finite-field-list`, and Section 7,
`yao:lift`. This isolates the algebraic interface needed by an executable
quotient-field constructor: cardinality `2^d` and a binary basis. It does not
claim that an executable bit-list is extensionally this abstract matrix.
-/

namespace CurrentAdditive.SmallBias

open Paper2.Yao Paper2.YaoLookup Workspace.Types.Protocol
open CurrentAdditive.FiniteFieldAdapter

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]
  [Algebra (ZMod 2) F]

/-- Number all vector/field seeds by natural labels, retaining duplicate
decoded words as distinct labels. -/
noncomputable def genericIndexedVectorSeeds (d : ℕ)
    (basis : Module.Basis (Fin d) (ZMod 2) F)
    (hcard : Fintype.card F = 2 ^ d) :
    VectorSeed d F ≃ Fin ((2 ^ d) ^ 2) :=
  (Fintype.equivFin (VectorSeed d F)).trans
    (finCongr (by rw [vectorSeed_card_eq_square basis, hcard]))

/-- The quotient field's abstract indexed array, once its basis and
cardinality have been verified. -/
noncomputable def genericIndexedFieldWord (b t d : ℕ)
    (basis : Module.Basis (Fin d) (ZMod 2) F)
    (hcard : Fintype.card F = 2 ^ d) :
    Fin ((2 ^ d) ^ 2) →
      Fin (2 ^ b) × Fin (2 ^ t * 2 ^ t + 1) → Bool :=
  fun ℓ j => vectorWord basis ((genericIndexedVectorSeeds d basis hcard).symm ℓ)
    (finProdFinEquiv j)

/-- The exact uniform labelled law is small-biased for any binary field
with the requisite cardinality and basis. -/
theorem genericIndexedFieldWord_isSmallBiased (b t d : ℕ)
    (basis : Module.Basis (Fin d) (ZMod 2) F)
    (hcard : Fintype.card F = 2 ^ d)
    (hR : ((2 ^ b * (2 ^ t * 2 ^ t + 1) : ℕ) : ℚ) / sourceBiasQ b t ≤
      (2 ^ d : ℚ)) :
    IsSmallBiased
      (Paper2.FiniteLaw.uniform (Fin ((2 ^ d) ^ 2)))
      (genericIndexedFieldWord b t d basis hcard)
      ((1 / 2 : ℝ) ^
        (2 ^ sourceSuffixDepth b t + t + sourceCutIndex b t + 2)) := by
  have hn : 1 ≤ 2 ^ b * (2 ^ t * 2 ^ t + 1) := by
    have hp : 0 < 2 ^ b * (2 ^ t * 2 ^ t + 1) := by positivity
    omega
  have hε : 0 < sourceBiasQ b t := by
    unfold sourceBiasQ
    positivity
  have hR' : ((2 ^ b * (2 ^ t * 2 ^ t + 1) : ℕ) : ℚ) /
      sourceBiasQ b t ≤ (Fintype.card F : ℚ) := by
    rw [hcard]
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hR
  have hvector := vectorSeedLaw_isSmallBiased basis hn
    (sourceBiasQ b t) hε hR'
  have hcoord : IsSmallBiased (vectorSeedLaw (F := F) d)
      (fun seed (j : Fin (2 ^ b) × Fin (2 ^ t * 2 ^ t + 1)) =>
        vectorWord basis seed (finProdFinEquiv j))
      (sourceBiasQ b t : ℝ) :=
    smallBias_comp_injective _ _ _ hvector finProdFinEquiv
      finProdFinEquiv.injective
  haveI : Nonempty (Fin ((2 ^ d) ^ 2)) := ⟨⟨0, by positivity⟩⟩
  have hindexed := uniformSmallBias_relabel
    (genericIndexedVectorSeeds d basis hcard)
    (fun seed (j : Fin (2 ^ b) × Fin (2 ^ t * 2 ^ t + 1)) =>
      vectorWord basis seed (finProdFinEquiv j)) _ hcoord
  simpa only [genericIndexedFieldWord, sourceBiasQ, Rat.cast_pow, Rat.cast_div,
    Rat.cast_one, Rat.cast_ofNat] using hindexed

/-- The full-selector matrix gap with an arbitrary binary extension field.
The only field-specific inputs are its exact order and binary basis. -/
theorem lower_bound_generic_indexed_field_matrix
    {V E : Type*} [Fintype V]
    (b t d : ℕ) (ht : 4 ≤ t)
    (basis : Module.Basis (Fin d) (ZMod 2) F)
    (hcard : Fintype.card F = 2 ^ d)
    (hR : ((2 ^ b * (2 ^ t * 2 ^ t + 1) : ℕ) : ℚ) / sourceBiasQ b t ≤
      (2 ^ d : ℚ))
    (edges : E → Fin (2 ^ t * 2 ^ t) ↪ V)
    (index : E ↪ Fin (2 ^ b))
    (hno : ∀ colour : V → Fin (2 ^ (2 ^ t - 1)),
      ∃ e c, ∀ i, colour (edges e i) = c) :
    (2 * b + 4 * t + 2) + 2 * t - 6 ≤
      Dalt .alice (matrix (placeEdges edges index)
        (fullSelector (2 ^ (t - 1)) (2 ^ b))
        (genericIndexedFieldWord b t d basis hcard)) := by
  exact lower_bound_fullSelector_small_biased ht edges index hno
    (genericIndexedFieldWord b t d basis hcard)
    (Paper2.FiniteLaw.uniform (Fin ((2 ^ d) ^ 2)))
    (genericIndexedFieldWord_isSmallBiased b t d basis hcard hR)

#print axioms CurrentAdditive.SmallBias.genericIndexedFieldWord_isSmallBiased
#print axioms CurrentAdditive.SmallBias.lower_bound_generic_indexed_field_matrix

end CurrentAdditive.SmallBias
