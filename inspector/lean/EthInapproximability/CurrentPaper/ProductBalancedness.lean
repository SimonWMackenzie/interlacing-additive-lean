import NPCC.Relaxed
import EthInapproximability.CurrentPaper.ProductFibreCount
import EthInapproximability.CurrentPaper.ProductErrorBound
import EthInapproximability.CurrentPaper.ProductErrorSmall

/-!
# Independent products of indexed balanced families

Source: v8 `A-stage4-details.tex`, `lem:paper-product-extraction`(3),
and the product-family calls in `F-parameter-choices.tex`.

The label of a product column is a tuple of independent family labels.
Equal represented columns are not identified. Coordinate subsets may meet
arbitrary factors; no assumption that all queried coordinates lie in one
factor is made.
-/

namespace EthInapproximability.CurrentPaper.ProductBalancedness

open scoped BigOperators

/-- Product labels enumerate every tuple of original labels, including repeats. -/
def productFamily (v : ℕ) {Y : Type*} {q L : ℕ}
    (S : Fin L → Fin q → Y) : Fin (L ^ v) → Fin (v * q) → Y :=
  fun j i => S (finFunctionFinEquiv.symm j (finProdFinEquiv.symm i).1)
    (finProdFinEquiv.symm i).2

theorem productFamily_block (v : ℕ) {Y : Type*} {q L : ℕ}
    (S : Fin L → Fin q → Y) (j : Fin (L ^ v)) (r : Fin v) (i : Fin q) :
    productFamily v S j (finProdFinEquiv (r, i)) =
      S (finFunctionFinEquiv.symm j r) i := by
  simp [productFamily]

/-- Reindexing labels preserves their counts, even if represented columns repeat. -/
theorem card_filter_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (p : B → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun a => p (e a))).card =
      (Finset.univ.filter p).card := by
  classical
  exact Finset.card_equiv e (by simp)

/-- Label reindexing does not change balancedness. -/
theorem balanced_reindex {Y : Type*} [Fintype Y] [DecidableEq Y]
    {q L M t : ℕ} {S : Fin L → Fin q → Y} {ε : ℝ}
    (hS : NPCC.IsBalancedFamily t S ε) (e : Fin M ≃ Fin L) :
    NPCC.IsBalancedFamily t (fun j i => S (e j) i) ε := by
  have hML : M = L := by
    simpa using Fintype.card_congr e
  refine ⟨by simpa [hML] using hS.1, ?_⟩
  intro J hJ a
  rw [card_filter_equiv e (fun j => ∀ i ∈ J, S j i = a i), hML]
  exact hS.2 J hJ a

/-- Independent pairs as literal pairs of labels. -/
def pairedFamily {Y : Type*} {q L : ℕ} (S : Fin L → Fin q → Y) :
    (Fin L × Fin L) → Fin (2 * q) → Y :=
  fun j i => S ((finTwoArrowEquiv (Fin L)).symm j (finProdFinEquiv.symm i).1)
    (finProdFinEquiv.symm i).2

/-- The pair-indexed representation, on the finite index carrier expected by
`NPCC.IsBalancedFamily`. -/
def pairFamily {Y : Type*} {q L : ℕ} (S : Fin L → Fin q → Y) :
    Fin (L * L) → Fin (2 * q) → Y :=
  fun j => pairedFamily S (finProdFinEquiv.symm j)

theorem pairedFamily_left {Y : Type*} {q L : ℕ}
    (S : Fin L → Fin q → Y) (j : Fin L × Fin L) (i : Fin q) :
    pairedFamily S j (finProdFinEquiv (0, i)) = S j.1 i := by
  simp [pairedFamily, finTwoArrowEquiv]

theorem pairedFamily_right {Y : Type*} {q L : ℕ}
    (S : Fin L → Fin q → Y) (j : Fin L × Fin L) (i : Fin q) :
    pairedFamily S j (finProdFinEquiv (1, i)) = S j.2 i := by
  simp [pairedFamily, finTwoArrowEquiv]

def pairLabelEquiv (L : ℕ) : Fin (L * L) ≃ Fin (L ^ 2) :=
  finProdFinEquiv.symm.trans
    ((finTwoArrowEquiv (Fin L)).symm.trans finFunctionFinEquiv)

theorem pairFamily_eq_product {Y : Type*} {q L : ℕ}
    (S : Fin L → Fin q → Y) :
    pairFamily S = fun j => productFamily 2 S (pairLabelEquiv L j) := by
  funext j i
  simp [pairFamily, pairedFamily, productFamily, pairLabelEquiv]

open ProductFibreCount

/-- Exact normalized product counts and the uniform baseline factorization. -/
theorem product_probabilities {Y : Type*} [DecidableEq Y]
    {v q L : ℕ} (S : Fin L → Fin q → Y)
    (J : Finset (Fin v × Fin q)) (a : Fin v × Fin q → Y) :
    ((globalMatches (fun _ => S) J a).card : ℝ) / (L : ℝ) ^ v =
      ∏ i, ((localMatches (fun _ => S) J a i).card : ℝ) / L := by
  rw [card_globalMatches, Nat.cast_prod, Finset.prod_div_distrib]
  simp

theorem product_baselines {Y : Type*} [Fintype Y]
    {v q : ℕ} (J : Finset (Fin v × Fin q)) :
    (∏ i, (1 : ℝ) / (Fintype.card Y : ℝ) ^ (slice J i).card) =
      1 / (Fintype.card Y : ℝ) ^ J.card := by
  rw [Finset.prod_div_distrib, Finset.prod_const_one,
    Finset.prod_pow_eq_pow_sum, ← card_eq_sum_slice]

/-- The full independent product has the stated relative error on every
coordinate pattern. This includes patterns split across arbitrary factors. -/
theorem independent_pattern_bound {Y : Type*} [Fintype Y] [DecidableEq Y]
    {v q L t : ℕ} {S : Fin L → Fin q → Y} {ε : ℝ}
    (hS : NPCC.IsBalancedFamily t S ε) (hε : 0 ≤ ε)
    (J : Finset (Fin v × Fin q)) (hJ : J.card ≤ t)
    (a : Fin v × Fin q → Y) :
    |((globalMatches (fun _ => S) J a).card : ℝ) / (L : ℝ) ^ v -
      1 / (Fintype.card Y : ℝ) ^ J.card| ≤
      ((1 + ε) ^ v - 1) / (Fintype.card Y : ℝ) ^ J.card := by
  let p : Fin v → ℝ := fun i => ((localMatches (fun _ => S) J a i).card : ℝ) / L
  let b : Fin v → ℝ := fun i => 1 / (Fintype.card Y : ℝ) ^ (slice J i).card
  have herr : ∀ i, |p i - b i| ≤ ε * b i := by
    intro i
    simpa [p, b, localMatches, div_eq_mul_inv] using
      hS.2 (slice J i) ((card_slice_le J i).trans hJ) (fun j => a (i, j))
  have h := ProductErrorBound.abs_prod_sub_prod_le_univ p b hε
    (fun _ => by dsimp [p]; positivity) (fun _ => by dsimp [b]; positivity) herr
  simpa only [p, b, Fintype.card_fin, ← product_probabilities S J a,
    product_baselines J, mul_one_div] using h

/-- Coordinate relabeling of the independent-product matching event. -/
theorem product_pattern_count {Y : Type*} [DecidableEq Y]
    {v q L : ℕ} (S : Fin L → Fin q → Y)
    (J : Finset (Fin (v * q))) (a : Fin (v * q) → Y) :
    (Finset.univ.filter (fun j => ∀ i ∈ J, productFamily v S j i = a i)).card =
      (globalMatches (fun _ => S) (J.map finProdFinEquiv.symm.toEmbedding)
        (fun p => a (finProdFinEquiv p))).card := by
  classical
  apply Finset.card_equiv finFunctionFinEquiv.symm
  intro j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_globalMatches,
    Finset.forall_mem_map, Equiv.toEmbedding_apply]
  simp only [productFamily, Equiv.apply_symm_apply]

/-- Independent product balancedness, with a factor-count error bound. -/
theorem product_balanced {Y : Type*} [Fintype Y] [DecidableEq Y]
    {q L t : ℕ} {S : Fin L → Fin q → Y} {ε : ℝ}
    (v : ℕ) (hS : NPCC.IsBalancedFamily t S ε) (hε : 0 ≤ ε) :
    NPCC.IsBalancedFamily t (productFamily v S) ((1 + ε) ^ v - 1) := by
  classical
  refine ⟨pow_pos hS.1 _, ?_⟩
  intro J hJ a
  rw [product_pattern_count]
  have h := independent_pattern_bound hS hε
    (J.map finProdFinEquiv.symm.toEmbedding) (by simpa using hJ)
    (fun p => a (finProdFinEquiv p))
  simpa using h

/-- Two genuinely independent labels give the exact pair error `2ε+ε²`. -/
theorem pair_balanced {Y : Type*} [Fintype Y] [DecidableEq Y]
    {q L t : ℕ} {S : Fin L → Fin q → Y} {ε : ℝ}
    (hS : NPCC.IsBalancedFamily t S ε) (hε : 0 ≤ ε) :
    NPCC.IsBalancedFamily t (pairFamily S) (2 * ε + ε ^ 2) := by
  have h := balanced_reindex (product_balanced 2 hS hε) (pairLabelEquiv L)
  rw [← pairFamily_eq_product] at h
  convert h using 1
  ring

/-- The number of factors contributing error is at most the number of
queried coordinates, independently of the ambient product length. -/
theorem independent_pattern_bound_order {Y : Type*} [Fintype Y] [DecidableEq Y]
    {v q L t : ℕ} {S : Fin L → Fin q → Y} {ε : ℝ}
    (hS : NPCC.IsBalancedFamily t S ε) (hε : 0 ≤ ε)
    (J : Finset (Fin v × Fin q)) (hJ : J.card ≤ t)
    (a : Fin v × Fin q → Y) :
    |((globalMatches (fun _ => S) J a).card : ℝ) / (L : ℝ) ^ v -
      1 / (Fintype.card Y : ℝ) ^ J.card| ≤
      ((1 + ε) ^ t - 1) / (Fintype.card Y : ℝ) ^ J.card := by
  classical
  let p : Fin v → ℝ := fun i => ((localMatches (fun _ => S) J a i).card : ℝ) / L
  let b : Fin v → ℝ := fun i => 1 / (Fintype.card Y : ℝ) ^ (slice J i).card
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hS.1
  have hp : (∏ i ∈ activeSlices J, p i) = ∏ i, p i := by
    apply Finset.prod_subset (Finset.subset_univ _)
    intro i _ hi
    have hempty : slice J i = ∅ := by
      simpa only [mem_activeSlices, Finset.not_nonempty_iff_eq_empty] using hi
    simp [p, localMatches_of_slice_empty _ _ _ _ hempty, hL]
  have hb : (∏ i ∈ activeSlices J, b i) = ∏ i, b i := by
    apply Finset.prod_subset (Finset.subset_univ _)
    intro i _ hi
    have hempty : slice J i = ∅ := by
      simpa only [mem_activeSlices, Finset.not_nonempty_iff_eq_empty] using hi
    simp [b, hempty]
  have herr : ∀ i ∈ activeSlices J, |p i - b i| ≤ ε * b i := by
    intro i _
    simpa [p, b, localMatches, div_eq_mul_inv] using
      hS.2 (slice J i) ((card_slice_le J i).trans hJ) (fun j => a (i, j))
  have h := ProductErrorBound.abs_prod_sub_prod_le_of_card_le (activeSlices J) p b
    hε ((card_activeSlices_le J).trans hJ) (fun _ _ => by dsimp [p]; positivity)
    (fun _ _ => by dsimp [b]; positivity) herr
  rw [hp, hb] at h
  simpa only [p, b, ← product_probabilities S J a,
    product_baselines J, mul_one_div] using h

/-- The paper's product-balancedness theorem. Its error depends on the
query order, not the number of independent factors. -/
theorem product_balanced_order {Y : Type*} [Fintype Y] [DecidableEq Y]
    {q L t : ℕ} {S : Fin L → Fin q → Y} {ε : ℝ}
    (v : ℕ) (hS : NPCC.IsBalancedFamily t S ε) (hε : 0 ≤ ε) :
    NPCC.IsBalancedFamily t (productFamily v S) ((1 + ε) ^ t - 1) := by
  classical
  refine ⟨pow_pos hS.1 _, ?_⟩
  intro J hJ a
  rw [product_pattern_count]
  have h := independent_pattern_bound_order hS hε
    (J.map finProdFinEquiv.symm.toEmbedding) (by simpa using hJ)
    (fun p => a (finProdFinEquiv p))
  simpa using h

/-- Increasing the allowed error preserves the same finite family. -/
theorem balanced_mono_error {Y : Type*} [Fintype Y] [DecidableEq Y]
    {q L t : ℕ} {S : Fin L → Fin q → Y} {ε δ : ℝ}
    (hS : NPCC.IsBalancedFamily t S ε) (hεδ : ε ≤ δ) :
    NPCC.IsBalancedFamily t S δ := by
  refine ⟨hS.1, ?_⟩
  intro J hJ a
  exact (hS.2 J hJ a).trans (div_le_div_of_nonneg_right hεδ (by positivity))

/-- The displayed maximum in the paper follows from the stronger symmetric
upper-error bound; no new product-balancedness hypothesis is introduced. -/
theorem product_balanced_paper {Y : Type*} [Fintype Y] [DecidableEq Y]
    {q L t : ℕ} {S : Fin L → Fin q → Y} {ε : ℝ}
    (v : ℕ) (hS : NPCC.IsBalancedFamily t S ε) (hε : 0 ≤ ε) :
    NPCC.IsBalancedFamily t (productFamily v S)
      (max ((1 + ε) ^ t - 1) (1 - (1 - ε) ^ t)) :=
  balanced_mono_error (product_balanced_order v hS hε) (le_max_left _ _)

/-- Two equal represented base columns are still two separate choices in
each factor: their pair pattern therefore has four, not one, labels. -/
theorem pair_duplicate_labels_regression :
    (Finset.univ.filter (fun j : Fin (3 * 3) =>
      ∀ i : Fin (2 * 1),
        pairFamily (fun (c : Fin 3) (_ : Fin 1) => decide (c.val = 2)) j i = false)).card
      = 4 := by
  decide

/-- The complete product-balancedness conclusion at the paper's chosen
base error, with the strict numerical error bound proved rather than assumed. -/
theorem product_balanced_small {Y : Type*} [Fintype Y] [DecidableEq Y]
    {q L t : ℕ} {S : Fin L → Fin q → Y} {ε : ℝ}
    (v : ℕ) (hS : NPCC.IsBalancedFamily t S ε) (ht : 0 < t)
    (hε : 0 ≤ ε) (hsmall : ε ≤ 1 / (100 * (t : ℝ))) :
    NPCC.IsBalancedFamily t (productFamily v S)
        (max ((1 + ε) ^ t - 1) (1 - (1 - ε) ^ t)) ∧
      max ((1 + ε) ^ t - 1) (1 - (1 - ε) ^ t) < 1 / 50 :=
  ⟨product_balanced_paper v hS hε,
    ProductErrorSmall.max_error_lt_one_fiftieth ht hε hsmall⟩

end EthInapproximability.CurrentPaper.ProductBalancedness
