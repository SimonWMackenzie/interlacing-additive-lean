import CurrentAdditive.SmallBiasYes

/-!
# Explicit pair labels for the finite-field word list

Source: v27 Appendix G, `yao:finite-field-list`. The physical printer
enumerates `(x,y)` in row-major order, with both ranging over `[2^d]`.
This algebraic interface uses supplied decoding equivalences for those
literal labels; proving equality with printed bit lists remains separate.
-/

namespace CurrentAdditive.SmallBias

open Paper2.Yao Paper2.YaoLookup Workspace.Types.Protocol
open CurrentAdditive.FiniteFieldAdapter

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]
  [Algebra (ZMod 2) F]

/-- Decode the printer's two `Fin(2^d)` labels as a binary vector and a
field element, then flatten the pair in the same row-major order. -/
noncomputable def explicitPairVectorSeeds (d : ℕ)
    (xDecode : Fin (2 ^ d) ≃ (Fin d → ZMod 2))
    (yDecode : Fin (2 ^ d) ≃ F) :
    VectorSeed d F ≃ Fin ((2 ^ d) ^ 2) :=
  ((xDecode.symm.prodCongr yDecode.symm).trans finProdFinEquiv).trans
    (finCongr (by rw [pow_two]))

/-- The indexed word using the printer's explicit `(x,y)` decoding.
This definition preserves distinct labels even when words coincide. -/
noncomputable def explicitPairFieldWord (b t d : ℕ)
    (basis : Module.Basis (Fin d) (ZMod 2) F)
    (xDecode : Fin (2 ^ d) ≃ (Fin d → ZMod 2))
    (yDecode : Fin (2 ^ d) ≃ F) :
    Fin ((2 ^ d) ^ 2) →
      Fin (2 ^ b) × Fin (2 ^ t * 2 ^ t + 1) → Bool :=
  fun ℓ j => vectorWord basis
    ((explicitPairVectorSeeds d xDecode yDecode).symm ℓ)
    (finProdFinEquiv j)

/-- The literal pair-labelled law is small-biased after any verified
bijective decodings of the vector and field residue labels. -/
theorem explicitPairFieldWord_isSmallBiased (b t d : ℕ)
    (basis : Module.Basis (Fin d) (ZMod 2) F)
    (hcard : Fintype.card F = 2 ^ d)
    (xDecode : Fin (2 ^ d) ≃ (Fin d → ZMod 2))
    (yDecode : Fin (2 ^ d) ≃ F)
    (hR : ((2 ^ b * (2 ^ t * 2 ^ t + 1) : ℕ) : ℚ) / sourceBiasQ b t ≤
      (2 ^ d : ℚ)) :
    IsSmallBiased
      (Paper2.FiniteLaw.uniform (Fin ((2 ^ d) ^ 2)))
      (explicitPairFieldWord b t d basis xDecode yDecode)
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
    (explicitPairVectorSeeds d xDecode yDecode)
    (fun seed (j : Fin (2 ^ b) × Fin (2 ^ t * 2 ^ t + 1)) =>
      vectorWord basis seed (finProdFinEquiv j)) _ hcoord
  simpa only [explicitPairFieldWord, sourceBiasQ, Rat.cast_pow, Rat.cast_div,
    Rat.cast_one, Rat.cast_ofNat] using hindexed

/-- The full-selector NO gap for a field list in physical pair-label order.
The constructor need only show its bits equal this word at each label and
coordinate; no Galois-field isomorphism is needed. -/
theorem lower_bound_explicit_pair_field_matrix
    {V E : Type*} [Fintype V]
    (b t d : ℕ) (ht : 4 ≤ t)
    (basis : Module.Basis (Fin d) (ZMod 2) F)
    (hcard : Fintype.card F = 2 ^ d)
    (xDecode : Fin (2 ^ d) ≃ (Fin d → ZMod 2))
    (yDecode : Fin (2 ^ d) ≃ F)
    (hR : ((2 ^ b * (2 ^ t * 2 ^ t + 1) : ℕ) : ℚ) / sourceBiasQ b t ≤
      (2 ^ d : ℚ))
    (edges : E → Fin (2 ^ t * 2 ^ t) ↪ V)
    (index : E ↪ Fin (2 ^ b))
    (hno : ∀ colour : V → Fin (2 ^ (2 ^ t - 1)),
      ∃ e c, ∀ i, colour (edges e i) = c) :
    (2 * b + 4 * t + 2) + 2 * t - 6 ≤
      Dalt .alice (matrix (placeEdges edges index)
        (fullSelector (2 ^ (t - 1)) (2 ^ b))
        (explicitPairFieldWord b t d basis xDecode yDecode)) := by
  exact lower_bound_fullSelector_small_biased ht edges index hno
    (explicitPairFieldWord b t d basis xDecode yDecode)
    (Paper2.FiniteLaw.uniform (Fin ((2 ^ d) ^ 2)))
    (explicitPairFieldWord_isSmallBiased b t d basis hcard
      xDecode yDecode hR)

#print axioms CurrentAdditive.SmallBias.explicitPairFieldWord_isSmallBiased
#print axioms CurrentAdditive.SmallBias.lower_bound_explicit_pair_field_matrix

end CurrentAdditive.SmallBias
