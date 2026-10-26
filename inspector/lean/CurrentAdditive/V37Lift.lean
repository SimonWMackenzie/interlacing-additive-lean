import CurrentAdditive.V37Lookup
import Paper2.YaoLowerBound
import CurrentAdditive.SmallBiasPrintedEndpoint

/-!
# The selected v37 alternating hypergraph lift

Source: `papers/randomized-additive-hardness/versions/v37/source/sections/alternation.tex`,
`yao:lift` (lines 282--344). This private file reuses the existing checked
hypergraph, projection, restriction, and complete-strategy objects, but keeps
the v37 forbidden cost `2*(b+3*t-3)-1` exactly.
-/

namespace CurrentAdditive.SmallBias

open Paper2.Yao Paper2.YaoLookup Paper2.YaoLowerBound Workspace.Types.Protocol
open CurrentAdditive.FiniteFieldAdapter
open CurrentAdditive.FiniteFieldConstructor

private theorem two_mul_le_two_pow (s : ℕ) (hs : 2 ≤ s) :
    2 * s ≤ 2 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih =>
      rw [pow_succ]
      omega

theorem v37_log_guard (b t : ℕ) (ht : 4 ≤ t) :
    Nat.clog 2 (b + 3 * t - 3) ≤ (b + 3 * t - 3) - t := by
  let m := b + 3 * t - 3
  let s := m - t
  have hs : 2 ≤ s := by dsimp [s, m]; omega
  have hm : m ≤ 2 * s := by dsimp [s, m]; omega
  have hpow : m ≤ 2 ^ s := hm.trans (two_mul_le_two_pow s hs)
  exact (Nat.clog_le_iff_le_pow (by decide)).2 hpow

theorem v37_payload_minimum (b t : ℕ) (ht : 4 ≤ t) :
    2 ^ ((b + 3 * t - 3) - t + 1) ≤ payloadMinimum b t := by
  have he : (b + 3 * t - 3) - t + 1 = b + 2 * t - 2 := by omega
  rw [he]
  unfold payloadMinimum
  omega

/-- Restrict an original labelled pattern law along an injective coordinate
map. In particular, repeated *column labels* stay separate under the law;
only the retained lookup positions are reindexed. -/
theorem HasPatternBound.comp_injective
    {Ω Λ Ω' : Type*} [Fintype Λ]
    (μ : Paper2.FiniteLaw Λ) (word : Λ → Ω → Bool) (ε : ℝ)
    (hpattern : HasPatternBound μ word ε)
    (f : Ω' → Ω) (hf : Function.Injective f) :
    HasPatternBound μ (fun ℓ x => word ℓ (f x)) ε := by
  classical
  intro I z
  let z' : Ω → Bool := fun x =>
    if h : ∃ y, f y = x then z (Classical.choose h) else false
  have hz (y : Ω') : z' (f y) = z y := by
    have h : ∃ w, f w = f y := ⟨y, rfl⟩
    simp only [z', dif_pos h]
    exact congrArg z (hf (Classical.choose_spec h))
  have hevent :
      (fun ℓ => ∀ j ∈ I, word ℓ (f j) = z j) =
      (fun ℓ => ∀ j ∈ I.image f, word ℓ j = z' j) := by
    funext ℓ
    apply propext
    constructor
    · intro h j hj
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hj
      rw [hz]
      exact h y hy
    · intro h j hj
      rw [← hz]
      exact h (f j) (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
  rw [hevent]
  have hcard : (I.image f).card = I.card := Finset.card_image_iff.mpr hf.injOn
  rw [← hcard]
  exact hpattern (I.image f) z'

/-- A v37-cost protocol on the actual hypergraph table yields the actual
retained lookup protocol, with no cost weakening. The old projection theorem
supplies a strictly stronger cardinality threshold than v37 needs. -/
theorem short_protocol_payload_failure_v37
    {V E : Type*} {b t labels samples : ℕ}
    (ht : 4 ≤ t) (hlabels : 0 < labels)
    (edges : E → Fin (2 ^ t * 2 ^ t) ↪ V)
    (index : E ↪ Fin (2 ^ b))
    (hno : ∀ colour : V → Fin (2 ^ (2 ^ t - 1)),
      ∃ e c, ∀ i, colour (edges e i) = c)
    (C : Fin labels → Fin (2 ^ (t - 1)) → Fin (2 ^ b))
    (hC : selectorGood (2 ^ (t - 1)) (2 ^ b) (2 ^ (2 ^ t - 1)) labels C)
    (W : Fin samples → Fin (2 ^ b) × Fin (2 ^ t * 2 ^ t + 1) → Bool)
    (P : StrictProtocol (V × Fin labels)
      (Fin (2 ^ (t - 1)) × Fin (2 ^ b) × Fin samples) .alice)
    (hP : P.Computes (matrix (placeEdges edges index) C W))
    (hcost : P.cost ≤ 2 * (b + 3 * t - 3) - 1) :
    payloadShortProtocolFailure ((b + 3 * t - 3) - 1) t
      (payloadMinimum b t) samples W := by
  obtain ⟨e, σ, _, hσ, hsize⟩ :=
    LowerBound.exists_monochromatic_dominantClasses t P.toProtocol edges hno
  let Z : Fin (2 ^ t * 2 ^ t) → Finset (Fin labels) :=
    fun i => LowerBound.dominantClass t P.toProtocol (edges e i)
  have hp (i : Fin (2 ^ t * 2 ^ t)) :
      (3 : ℝ) / (4 * (2 : ℝ) ^ (2 ^ t - 1)) ≤
        ∏ g, ((Restriction.addresses C g Z i).card : ℝ) / (2 : ℝ) ^ b := by
    simpa only [Restriction.addresses, Nat.cast_pow, Nat.cast_ofNat] using
      retained_projection_product (2 ^ (2 ^ t - 1)) (pow_pos (by decide) _)
        hlabels C hC (Z i) (hsize i)
  obtain ⟨g, hg⟩ := exists_large_projection t b ht
    (fun i g => (Restriction.addresses C g Z i).card) hp
  have hcost' : P.cost ≤ 2 * ((b + 3 * t - 3) - 1) + 1 := by omega
  exact payload_failure_of_large_projection ((b + 3 * t - 3) - 1) t
    (payloadMinimum b t) (placeEdges edges index) C W (index e) (edges e)
    (placeEdges_real edges index e) g Z P hP hcost' σ hσ hg

/-- The lookup obstruction rules out the exact restricted-protocol failure
produced above, using the original full-array law. -/
theorem no_payloadShortProtocolFailure_v37
    {X : Type*} [Fintype X] [DecidableEq X]
    (b t samples : ℕ) (ht : 4 ≤ t)
    (μ : Paper2.FiniteLaw (Fin samples))
    (W : Fin samples → X → Bool)
    (hpattern : HasPatternBound μ W
      ((1 / 2 : ℝ) ^ (4 * (b + 3 * t - 3)))) :
    ¬ payloadShortProtocolFailure ((b + 3 * t - 3) - 1) t
      (payloadMinimum b t) samples W := by
  classical
  intro hfail
  obtain ⟨J, hJ, P, hcost, ha, ⟨σ, hσ⟩, hlookup⟩ := hfail
  let depth := b + 3 * t - 3
  have hdepth : t < depth := by dsimp [depth]; omega
  have hJ' : 2 ^ (depth - t + 1) ≤ (Finset.univ : Finset J).card := by
    simpa only [Finset.card_univ, Fintype.card_coe] using
      (v37_payload_minimum b t ht).trans hJ
  have hpatternJ : HasPatternBound μ (fun ℓ (x : J) => W ℓ x.val)
      ((1 / 2 : ℝ) ^ (4 * depth)) :=
    HasPatternBound.comp_injective μ W _ hpattern Subtype.val Subtype.val_injective
  have hc : P.cost ≤ 2 * depth - 1 := by dsimp [depth] at *; omega
  exact no_short_lookup_v37 μ (fun ℓ (x : J) => W ℓ x.val)
    depth t (by omega) hdepth (v37_log_guard b t ht)
    Finset.univ hJ' _ (le_refl _) hpatternJ P hc ha σ
    (by intro x _; exact hσ x)
    (by intro x _ ℓ; exact hlookup x ℓ)

/-- The v37 NO-side bound on the actual labelled hypergraph matrix. The
selector is the complete address list in applications, and the array law is
checked for the same payload `W`. -/
theorem lower_bound_of_good_events_v37
    {V E : Type*} [Fintype V] {b t labels samples : ℕ}
    (ht : 4 ≤ t) (hlabels : 0 < labels)
    (edges : E → Fin (2 ^ t * 2 ^ t) ↪ V)
    (index : E ↪ Fin (2 ^ b))
    (hno : ∀ colour : V → Fin (2 ^ (2 ^ t - 1)),
      ∃ e c, ∀ i, colour (edges e i) = c)
    (C : Fin labels → Fin (2 ^ (t - 1)) → Fin (2 ^ b))
    (hC : selectorGood (2 ^ (t - 1)) (2 ^ b) (2 ^ (2 ^ t - 1)) labels C)
    (W : Fin samples → Fin (2 ^ b) × Fin (2 ^ t * 2 ^ t + 1) → Bool)
    (μ : Paper2.FiniteLaw (Fin samples))
    (hpattern : HasPatternBound μ W
      ((1 / 2 : ℝ) ^ (4 * (b + 3 * t - 3)))) :
    (2 * b + 4 * t + 2) + 2 * t - 8 ≤
      Dalt .alice (matrix (placeEdges edges index) C W) := by
  obtain ⟨P, hcost, hP⟩ := exists_optimal .alice
    (matrix (placeEdges edges index) C W)
  by_contra h
  have hp : P.cost ≤ 2 * (b + 3 * t - 3) - 1 := by omega
  exact (no_payloadShortProtocolFailure_v37 b t samples ht μ W hpattern)
    (short_protocol_payload_failure_v37 ht hlabels edges index hno C hC
      W P hP hp)

/-- The selected v37 fixed-gap choice, `t = ceil(k/2)+4`. The formula is
valid for every natural `k`; the paper uses `k >= 1`. -/
def v37GapParameter (k : ℕ) : ℕ := (k + 1) / 2 + 4

theorem v37GapParameter_ge_four (k : ℕ) : 4 ≤ v37GapParameter k := by
  unfold v37GapParameter
  omega

theorem v37GapParameter_gap (k : ℕ) :
    k ≤ 2 * v37GapParameter k - 8 := by
  unfold v37GapParameter
  omega

/-- On the same concrete matrix and original array law, the NO promise
gives any requested fixed additive gap when `t` is selected as above. -/
theorem lower_bound_fixed_gap_v37
    {V E : Type*} [Fintype V] {b labels samples : ℕ}
    (k : ℕ) (hlabels : 0 < labels)
    (edges : E → Fin (2 ^ (v37GapParameter k) *
      2 ^ (v37GapParameter k)) ↪ V)
    (index : E ↪ Fin (2 ^ b))
    (hno : ∀ colour : V → Fin (2 ^ (2 ^ (v37GapParameter k) - 1)),
      ∃ e c, ∀ i, colour (edges e i) = c)
    (C : Fin labels → Fin (2 ^ (v37GapParameter k - 1)) → Fin (2 ^ b))
    (hC : selectorGood (2 ^ (v37GapParameter k - 1)) (2 ^ b)
      (2 ^ (2 ^ (v37GapParameter k) - 1)) labels C)
    (W : Fin samples → Fin (2 ^ b) ×
      Fin (2 ^ (v37GapParameter k) * 2 ^ (v37GapParameter k) + 1) → Bool)
    (μ : Paper2.FiniteLaw (Fin samples))
    (hpattern : HasPatternBound μ W
      ((1 / 2 : ℝ) ^ (4 * (b + 3 * v37GapParameter k - 3)))) :
    (2 * b + 4 * v37GapParameter k + 2) + k ≤
      Dalt .alice (matrix (placeEdges edges index) C W) := by
  have hbase := lower_bound_of_good_events_v37
    (v37GapParameter_ge_four k) hlabels edges index hno C hC W μ hpattern
  have hgap := v37GapParameter_gap k
  have hfour := v37GapParameter_ge_four k
  omega

/-- The v37 array-list error requested by `yao:array-list`. -/
def v37BiasQ (b t : ℕ) : ℚ :=
  (1 / 2 : ℚ) ^ (4 * (b + 3 * t - 3))

/-- The old vector-seed construction is uniform in its rational bias target.
This specializes it to the v37 target while preserving the physical pair
labels, including duplicate decoded words. -/
theorem explicitPairFieldWord_hasPattern_v37
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    [Algebra (ZMod 2) F]
    (b t d : ℕ)
    (basis : Module.Basis (Fin d) (ZMod 2) F)
    (hcard : Fintype.card F = 2 ^ d)
    (xDecode : Fin (2 ^ d) ≃ (Fin d → ZMod 2))
    (yDecode : Fin (2 ^ d) ≃ F)
    (hR : ((2 ^ b * (2 ^ t * 2 ^ t + 1) : ℕ) : ℚ) /
      v37BiasQ b t ≤ (2 ^ d : ℚ)) :
    HasPatternBound
      (Paper2.FiniteLaw.uniform (Fin ((2 ^ d) ^ 2)))
      (explicitPairFieldWord b t d basis xDecode yDecode)
      ((1 / 2 : ℝ) ^ (4 * (b + 3 * t - 3))) := by
  have hn : 1 ≤ 2 ^ b * (2 ^ t * 2 ^ t + 1) := by
    have hp : 0 < 2 ^ b * (2 ^ t * 2 ^ t + 1) := by positivity
    omega
  have hε : 0 < v37BiasQ b t := by unfold v37BiasQ; positivity
  have hR' : ((2 ^ b * (2 ^ t * 2 ^ t + 1) : ℕ) : ℚ) /
      v37BiasQ b t ≤ (Fintype.card F : ℚ) := by
    rw [hcard]
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hR
  have hvector := vectorSeedLaw_isSmallBiased basis hn
    (v37BiasQ b t) hε hR'
  have hcoord : IsSmallBiased (vectorSeedLaw (F := F) d)
      (fun seed (j : Fin (2 ^ b) × Fin (2 ^ t * 2 ^ t + 1)) =>
        vectorWord basis seed (finProdFinEquiv j))
      (v37BiasQ b t : ℝ) :=
    smallBias_comp_injective _ _ _ hvector finProdFinEquiv
      finProdFinEquiv.injective
  haveI : Nonempty (Fin ((2 ^ d) ^ 2)) := ⟨⟨0, by positivity⟩⟩
  have hindexed := uniformSmallBias_relabel
    (explicitPairVectorSeeds d xDecode yDecode)
    (fun seed (j : Fin (2 ^ b) × Fin (2 ^ t * 2 ^ t + 1)) =>
      vectorWord basis seed (finProdFinEquiv j)) _ hcoord
  have hsmall : IsSmallBiased
      (Paper2.FiniteLaw.uniform (Fin ((2 ^ d) ^ 2)))
      (explicitPairFieldWord b t d basis xDecode yDecode)
      ((1 / 2 : ℝ) ^ (4 * (b + 3 * t - 3))) := by
    simpa only [explicitPairFieldWord, v37BiasQ, Rat.cast_pow,
      Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hindexed
  exact HasPatternBound.ofSmallBias _ _ _ (by positivity) hsmall

/-- The same pair-labelled matrix from the actual physical printer has the
v37 NO gap once each printed bit is identified with the checked field word.
The bit-equality premise is discharged by the quotient-field constructor
below, rather than by an assumed communication lower bound. -/
theorem lower_bound_printed_pair_field_matrix_v37
    {F : Type*} [Field F] [Fintype F] [CharP F 2]
    [Algebra (ZMod 2) F]
    {V E : Type*} [Fintype V]
    (b t d modulus : ℕ) (ht : 4 ≤ t)
    (basis : Module.Basis (Fin d) (ZMod 2) F)
    (hcard : Fintype.card F = 2 ^ d)
    (xDecode : Fin (2 ^ d) ≃ (Fin d → ZMod 2))
    (yDecode : Fin (2 ^ d) ≃ F)
    (hR : ((2 ^ b * (2 ^ t * 2 ^ t + 1) : ℕ) : ℚ) /
      v37BiasQ b t ≤ (2 ^ d : ℚ))
    (hbit : ∀ x y j,
      BitPrinter.bit d modulus (x : Fin (2 ^ d)).val
          (y : Fin (2 ^ d)).val (j : Fin (2 ^ b *
            (2 ^ t * 2 ^ t + 1))).val =
        vectorWord basis (xDecode x, yDecode y) j)
    (edges : E → Fin (2 ^ t * 2 ^ t) ↪ V)
    (index : E ↪ Fin (2 ^ b))
    (hno : ∀ colour : V → Fin (2 ^ (2 ^ t - 1)),
      ∃ e c, ∀ i, colour (edges e i) = c) :
    (2 * b + 4 * t + 2) + 2 * t - 8 ≤
      Dalt .alice (matrix (placeEdges edges index)
        (fullSelector (2 ^ (t - 1)) (2 ^ b))
        (printedPairFieldWord b t d modulus)) := by
  rw [printedPairFieldWord_eq_explicitPairFieldWord
    b t d modulus basis xDecode yDecode hbit]
  let q := 2 ^ (t - 1)
  let H := 2 ^ b
  let S := 2 ^ (2 ^ t - 1)
  have hm : 0 < Fintype.card (Fin q → Fin H) := by
    rw [fullSelector_size]
    positivity
  have hS : 0 < S := by dsimp [S]; positivity
  exact lower_bound_of_good_events_v37 ht hm edges index hno
    (fullSelector q H) (fullSelector_good q H S hS)
    (explicitPairFieldWord b t d basis xDecode yDecode)
    (Paper2.FiniteLaw.uniform (Fin ((2 ^ d) ^ 2)))
    (explicitPairFieldWord_hasPattern_v37 b t d basis hcard xDecode yDecode hR)

#print axioms CurrentAdditive.SmallBias.HasPatternBound.comp_injective
#print axioms CurrentAdditive.SmallBias.lower_bound_of_good_events_v37
#print axioms CurrentAdditive.SmallBias.lower_bound_fixed_gap_v37
#print axioms CurrentAdditive.SmallBias.explicitPairFieldWord_hasPattern_v37
#print axioms CurrentAdditive.SmallBias.lower_bound_printed_pair_field_matrix_v37

end CurrentAdditive.SmallBias
