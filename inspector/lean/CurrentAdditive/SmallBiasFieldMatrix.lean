import CurrentAdditive.SmallBiasFullSelector
import CurrentAdditive.FiniteFieldVectorSeed
import CurrentAdditive.FiniteFieldSeedExistence

/-!
# Abstract finite-field labels as actual columns of the lifted matrix

Source: v27 `sections/07a-small-bias.tex`, `yao:trace-list` and
`yao:array-list`, followed by `sections/07-yao.tex`, `yao:lift`.
This is a finite mathematical construction: the abstract Galois field,
basis, and `Fintype.equivFin` are not executable field-search certificates.
-/

namespace CurrentAdditive.SmallBias

open Paper2.Yao Paper2.YaoLookup Workspace.Types.Protocol
open CurrentAdditive.FiniteFieldAdapter CurrentAdditive.FiniteFieldConstructor

variable {A B Ω : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]

/-- Uniform small bias is invariant under a bijective relabelling of seeds.
In particular, duplicate decoded words remain distinct labels. -/
theorem uniformSmallBias_relabel (e : A ≃ B) (w : A → Ω → Bool)
    (ε : ℝ) (h : IsSmallBiased (Paper2.FiniteLaw.uniform A) w ε) :
    IsSmallBiased (Paper2.FiniteLaw.uniform B)
      (fun b x => w (e.symm b) x) ε := by
  classical
  intro I hI
  have hcard : Fintype.card A = Fintype.card B := Fintype.card_congr e
  have hcorr : parityCorr (Paper2.FiniteLaw.uniform B)
      (fun b x => w (e.symm b) x) I =
      parityCorr (Paper2.FiniteLaw.uniform A) w I := by
    unfold parityCorr Paper2.FiniteLaw.uniform
    simp only
    rw [← e.sum_comp]
    simp [hcard]
  rw [hcorr]
  exact h I hI

/-- A basis gives all `R²` vector/field seeds distinct natural-number
labels, where `R=2^d`. This equivalence chooses an ordering only for proof. -/
noncomputable def indexedVectorSeeds (d : ℕ) (hd : 0 < d)
    (basis : Module.Basis (Fin d) (ZMod 2) (BinaryField d)) :
    VectorSeed d (BinaryField d) ≃ Fin ((2 ^ d) ^ 2) :=
  (Fintype.equivFin (VectorSeed d (BinaryField d))).trans
    (finCongr (by rw [vectorSeed_card_eq_square basis, binaryField_card d hd]))

variable {b t d : ℕ}

/-- The actual Bool array for each of the `R²` indexed field seeds. The
coordinate bijection only numbers the source's `(address, edge slot)` pairs. -/
noncomputable def indexedFieldWord (b t d : ℕ) (hd : 0 < d)
    (basis : Module.Basis (Fin d) (ZMod 2) (BinaryField d)) :
    Fin ((2 ^ d) ^ 2) →
      Fin (2 ^ b) × Fin (2 ^ t * 2 ^ t + 1) → Bool :=
  fun ℓ j => vectorWord basis ((indexedVectorSeeds d hd basis).symm ℓ)
    (finProdFinEquiv j)

/-- The exact rational form of the source dyadic bias. -/
def sourceBiasQ (b t : ℕ) : ℚ :=
  (1 / 2 : ℚ) ^
    (2 ^ sourceSuffixDepth b t + t + sourceCutIndex b t + 2)

/-- The uniform `Fin(R²)` law of the indexed field seeds is small-biased on
the actual payload-position type. The field-size premise is precisely
`R ≥ n₀/ε`; there is no hidden protocol or covering assumption. -/
theorem indexedFieldWord_isSmallBiased (b t d : ℕ) (hd : 0 < d)
    (basis : Module.Basis (Fin d) (ZMod 2) (BinaryField d))
    (hR : ((2 ^ b * (2 ^ t * 2 ^ t + 1) : ℕ) : ℚ) / sourceBiasQ b t ≤
      (2 ^ d : ℚ)) :
    IsSmallBiased
      (Paper2.FiniteLaw.uniform (Fin ((2 ^ d) ^ 2)))
      (indexedFieldWord b t d hd basis)
      ((1 / 2 : ℝ) ^
        (2 ^ sourceSuffixDepth b t + t + sourceCutIndex b t + 2)) := by
  have hn : 1 ≤ 2 ^ b * (2 ^ t * 2 ^ t + 1) := by
    have hp : 0 < 2 ^ b * (2 ^ t * 2 ^ t + 1) := by positivity
    omega
  have hε : 0 < sourceBiasQ b t := by
    unfold sourceBiasQ
    positivity
  have hR' : ((2 ^ b * (2 ^ t * 2 ^ t + 1) : ℕ) : ℚ) /
      sourceBiasQ b t ≤ (Fintype.card (BinaryField d) : ℚ) := by
    rw [binaryField_card d hd]
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hR
  have hvector := vectorSeedLaw_isSmallBiased basis hn (sourceBiasQ b t) hε hR'
  have hcoord : IsSmallBiased (vectorSeedLaw (F := BinaryField d) d)
      (fun seed (j : Fin (2 ^ b) × Fin (2 ^ t * 2 ^ t + 1)) =>
        vectorWord basis seed (finProdFinEquiv j))
      (sourceBiasQ b t : ℝ) :=
    smallBias_comp_injective _ _ _ hvector finProdFinEquiv
      finProdFinEquiv.injective
  haveI : Nonempty (Fin ((2 ^ d) ^ 2)) := ⟨⟨0, by positivity⟩⟩
  have hindexed := uniformSmallBias_relabel (indexedVectorSeeds d hd basis)
    (fun seed (j : Fin (2 ^ b) × Fin (2 ^ t * 2 ^ t + 1)) =>
      vectorWord basis seed (finProdFinEquiv j)) _ hcoord
  simpa only [indexedFieldWord, sourceBiasQ, Rat.cast_pow, Rat.cast_div,
    Rat.cast_one, Rat.cast_ofNat] using hindexed

/-- An abstract binary basis exists because the Galois field has dimension
`d`; its selection is intentionally separate from the executable quotient
and polynomial-basis printer in Appendix G. -/
noncomputable def binaryBasis (d : ℕ) (hd : 0 < d) :
    Module.Basis (Fin d) (ZMod 2) (BinaryField d) :=
  Module.finBasisOfFinrankEq (ZMod 2) (BinaryField d)
    (GaloisField.finrank 2 (Nat.ne_of_gt hd))

/-- Finite mathematical v27 lift with all `R²` indexed field seeds and all
`H^q` selector tuples. The field-size inequality is the source's choice of
`R≥n₀/ε`; proving a physical printer for this same matrix remains separate. -/
theorem lower_bound_indexed_field_matrix
    {V E : Type*} [Fintype V]
    (b t d : ℕ) (ht : 4 ≤ t) (hd : 0 < d)
    (hR : ((2 ^ b * (2 ^ t * 2 ^ t + 1) : ℕ) : ℚ) / sourceBiasQ b t ≤
      (2 ^ d : ℚ))
    (edges : E → Fin (2 ^ t * 2 ^ t) ↪ V)
    (index : E ↪ Fin (2 ^ b))
    (hno : ∀ colour : V → Fin (2 ^ (2 ^ t - 1)),
      ∃ e c, ∀ i, colour (edges e i) = c) :
    (2 * b + 4 * t + 2) + 2 * t - 6 ≤
      Dalt .alice (matrix (placeEdges edges index)
        (fullSelector (2 ^ (t - 1)) (2 ^ b))
        (indexedFieldWord b t d hd (binaryBasis d hd))) := by
  exact lower_bound_fullSelector_small_biased ht edges index hno
    (indexedFieldWord b t d hd (binaryBasis d hd))
    (Paper2.FiniteLaw.uniform (Fin ((2 ^ d) ^ 2)))
    (indexedFieldWord_isSmallBiased b t d hd (binaryBasis d hd) hR)

#print axioms CurrentAdditive.SmallBias.uniformSmallBias_relabel
#print axioms CurrentAdditive.SmallBias.indexedFieldWord_isSmallBiased
#print axioms CurrentAdditive.SmallBias.lower_bound_indexed_field_matrix

end CurrentAdditive.SmallBias
