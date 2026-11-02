import CurrentAdditive.V38Lift
import CurrentAdditive.PrintedFieldWordChecked
import CurrentAdditive.SmallBiasStreamingIndex

/-!
# The selected v38 finite-field array on `H × K`

Source: `papers/randomized-additive-hardness/versions/v38/source/appendices/arrays.tex`,
`yao:finite-field-list` and proof of `yao:array-list`. The seed set remains
the labelled `R²` pairs and the output bit formula is the existing checked
polynomial-root construction, now with exactly `n=H*K` positions.
-/

namespace CurrentAdditive.SmallBias

open Paper2.Yao Paper2.YaoLookup Workspace.Types.Protocol
open CurrentAdditive.FiniteFieldAdapter
open CurrentAdditive.FiniteFieldConstructor
open CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge

def v38ArrayBiasQ (b t : ℕ) : ℚ :=
  (1 / 2 : ℚ) ^ (4 * (b + 3 * t))

/-- The selected finite-field array formula under the row-major pair
labelling of seed coordinates. -/
noncomputable def v38PairFieldWord
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    [Algebra (ZMod 2) F]
    (b t d : ℕ)
    (basis : Module.Basis (Fin d) (ZMod 2) F)
    (xDecode : Fin (2 ^ d) ≃ (Fin d → ZMod 2))
    (yDecode : Fin (2 ^ d) ≃ F) :
    Fin ((2 ^ d) ^ 2) →
      Fin (2 ^ b) × Fin (2 ^ t * 2 ^ t) → Bool :=
  fun ℓ j => vectorWord basis
    ((explicitPairVectorSeeds d xDecode yDecode).symm ℓ)
    (finProdFinEquiv j)

/-- The source's stronger error `2^(-4(b+3t))` implies the lookup error
`2^(-4(b+3t-3))`. -/
theorem v38_bias_le_lookup (b t : ℕ) :
    ((1 / 2 : ℝ) ^ (4 * (b + 3 * t))) ≤
      ((1 / 2 : ℝ) ^ (4 * (b + 3 * t - 3))) :=
  pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

/-- The exact v38 finite-field list has the original-law pattern bound on
`H×K`, with no fictitious neutral coordinate. -/
theorem v38PairFieldWord_hasPattern
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    [Algebra (ZMod 2) F]
    (b t d : ℕ)
    (basis : Module.Basis (Fin d) (ZMod 2) F)
    (hcard : Fintype.card F = 2 ^ d)
    (xDecode : Fin (2 ^ d) ≃ (Fin d → ZMod 2))
    (yDecode : Fin (2 ^ d) ≃ F)
    (hR : ((2 ^ b * (2 ^ t * 2 ^ t) : ℕ) : ℚ) /
      v38ArrayBiasQ b t ≤ (2 ^ d : ℚ)) :
    HasPatternBound
      (Paper2.FiniteLaw.uniform (Fin ((2 ^ d) ^ 2)))
      (v38PairFieldWord b t d basis xDecode yDecode)
      ((1 / 2 : ℝ) ^ (4 * (b + 3 * t))) := by
  have hn : 1 ≤ 2 ^ b * (2 ^ t * 2 ^ t) := by
    have hp : 0 < 2 ^ b * (2 ^ t * 2 ^ t) := by positivity
    omega
  have hε : 0 < v38ArrayBiasQ b t := by unfold v38ArrayBiasQ; positivity
  have hR' : ((2 ^ b * (2 ^ t * 2 ^ t) : ℕ) : ℚ) /
      v38ArrayBiasQ b t ≤ (Fintype.card F : ℚ) := by
    rw [hcard]
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hR
  have hvector := vectorSeedLaw_isSmallBiased basis hn
    (v38ArrayBiasQ b t) hε hR'
  have hcoord : IsSmallBiased (vectorSeedLaw (F := F) d)
      (fun seed (j : Fin (2 ^ b) × Fin (2 ^ t * 2 ^ t)) =>
        vectorWord basis seed (finProdFinEquiv j))
      (v38ArrayBiasQ b t : ℝ) :=
    smallBias_comp_injective _ _ _ hvector finProdFinEquiv
      finProdFinEquiv.injective
  haveI : Nonempty (Fin ((2 ^ d) ^ 2)) := ⟨⟨0, by positivity⟩⟩
  have hindexed := uniformSmallBias_relabel
    (explicitPairVectorSeeds d xDecode yDecode)
    (fun seed (j : Fin (2 ^ b) × Fin (2 ^ t * 2 ^ t)) =>
      vectorWord basis seed (finProdFinEquiv j)) _ hcoord
  have hsmall : IsSmallBiased
      (Paper2.FiniteLaw.uniform (Fin ((2 ^ d) ^ 2)))
      (v38PairFieldWord b t d basis xDecode yDecode)
      ((1 / 2 : ℝ) ^ (4 * (b + 3 * t))) := by
    simpa only [v38PairFieldWord, v38ArrayBiasQ, Rat.cast_pow,
      Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hindexed
  exact HasPatternBound.ofSmallBias _ _ _ (by positivity) hsmall

/-- The real bit table selected by the explicit quotient-field printer. -/
def v38PrintedPairWord (b t d modulus : ℕ) :
    Fin ((2 ^ d) ^ 2) →
      Fin (2 ^ b) × Fin (2 ^ t * 2 ^ t) → Bool :=
  fun ℓ j =>
    let xy := (printerPairLabel d).symm ℓ
    BitPrinter.bit d modulus xy.1.val xy.2.val (finProdFinEquiv j).val

theorem v38PrintedPairWord_eq_fieldWord
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    [Algebra (ZMod 2) F]
    (b t d modulus : ℕ)
    (basis : Module.Basis (Fin d) (ZMod 2) F)
    (xDecode : Fin (2 ^ d) ≃ (Fin d → ZMod 2))
    (yDecode : Fin (2 ^ d) ≃ F)
    (hbit : ∀ x y j,
      BitPrinter.bit d modulus (x : Fin (2 ^ d)).val
          (y : Fin (2 ^ d)).val
          (j : Fin (2 ^ b * (2 ^ t * 2 ^ t))).val =
        vectorWord basis (xDecode x, yDecode y) j) :
    v38PrintedPairWord b t d modulus =
      v38PairFieldWord b t d basis xDecode yDecode := by
  funext ℓ j
  let xy := (printerPairLabel d).symm ℓ
  have hseed :
      (explicitPairVectorSeeds d xDecode yDecode).symm ℓ =
      (xDecode xy.1, yDecode xy.2) := by
    simp [explicitPairVectorSeeds, printerPairLabel, xy]
  change BitPrinter.bit d modulus xy.1.val xy.2.val
      (finProdFinEquiv j).val =
    vectorWord basis
      ((explicitPairVectorSeeds d xDecode yDecode).symm ℓ)
      (finProdFinEquiv j)
  rw [hseed]
  exact hbit xy.1 xy.2 (finProdFinEquiv j)

/-- Source-faithful YES and NO costs on the one v38 physical bit table.
The physical seed modulus is certified by quotient-field algebra, and the
array law is proved from its actual pair labels. -/
theorem v38_concrete_matrix_yes_no
    {V E : Type*} [Fintype V]
    (b t d modulus : ℕ) (ht : 4 ≤ t) (hd : 0 < d)
    (hmodulus : modulus < 2 ^ (d + 1))
    (htop : modulus.testBit d = true)
    (hmonic : (polynomial (d + 1) modulus).Monic)
    (hdegree : (polynomial (d + 1) modulus).natDegree = d)
    [Fact (Irreducible (polynomial (d + 1) modulus))]
    (hR : ((2 ^ b * (2 ^ t * 2 ^ t) : ℕ) : ℚ) /
      v38ArrayBiasQ b t ≤ (2 ^ d : ℚ))
    (edges : E → Fin (2 ^ t * 2 ^ t) ↪ V)
    (index : E ↪ Fin (2 ^ b)) :
    let W := v38PrintedPairWord b t d modulus
    let M := matrixV38 (placeEdges edges index)
      (fullSelector (2 ^ (t - 1)) (2 ^ b)) W
    (∀ colour : V → Fin (2 ^ t),
      (∀ e c, 2 ^ t - 1 ≤
        colourFiberCard (fun i => colour (edges e i)) c) →
      Dalt .alice M ≤ 2 * b + 4 * t + 2) ∧
    ((∀ colour : V → Fin (2 ^ (2 ^ t)),
      ∃ e c, ∀ i, colour (edges e i) = c) →
      (2 * b + 4 * t + 2) + 2 * t - 8 ≤ Dalt .alice M) := by
  letI : Fintype (QuotientField d modulus) :=
    quotientFintype d modulus hmonic hdegree
  letI : CharP (QuotientField d modulus) 2 :=
    quotientCharP d modulus (Fact.out)
  have hbit (x y : Fin (2 ^ d))
      (j : Fin (2 ^ b * (2 ^ t * 2 ^ t))) :
      BitPrinter.bit d modulus x.val y.val j.val =
        vectorWord (fieldBasis d modulus hmonic hdegree)
          (xDecode d x, quotientCodeEquiv d modulus hmonic hdegree y) j :=
    printed_bit_eq_vectorWord d modulus _ hd hmodulus htop hmonic hdegree x y j
  have heq := v38PrintedPairWord_eq_fieldWord b t d modulus
    (fieldBasis d modulus hmonic hdegree)
    (xDecode d) (quotientCodeEquiv d modulus hmonic hdegree) hbit
  have hsource := v38PairFieldWord_hasPattern b t d
    (fieldBasis d modulus hmonic hdegree)
    (quotient_card d modulus hmonic hdegree)
    (xDecode d) (quotientCodeEquiv d modulus hmonic hdegree) hR
  have hlookup : HasPatternBound
      (Paper2.FiniteLaw.uniform (Fin ((2 ^ d) ^ 2)))
      (v38PrintedPairWord b t d modulus)
      ((1 / 2 : ℝ) ^ (4 * (b + 3 * t - 3))) := by
    rw [heq]
    intro I z
    have hp := hsource I z
    have hb := v38_bias_le_lookup b t
    linarith
  have hm : 0 < Fintype.card
      (Fin (2 ^ (t - 1)) → Fin (2 ^ b)) := by
    rw [fullSelector_size]
    positivity
  have hs : 0 < 2 ^ (2 ^ t - 1) := by positivity
  exact matrixV38_yes_no ht hm edges index
    (fullSelector (2 ^ (t - 1)) (2 ^ b))
    (fullSelector_good _ _ _ hs)
    (v38PrintedPairWord b t d modulus)
    (Paper2.FiniteLaw.uniform (Fin ((2 ^ d) ^ 2))) hlookup

#print axioms CurrentAdditive.SmallBias.v38PairFieldWord_hasPattern
#print axioms CurrentAdditive.SmallBias.v38_concrete_matrix_yes_no

end CurrentAdditive.SmallBias
