import EthInapproximability.CurrentPaper.CertifiedStopping
import EthInapproximability.CurrentPaper.ExactConstruction
import EthInapproximability.ParameterizedNP.SeedSpanLeg

/-!
# Binary indexing after deletion of column labels

Current replacement paper v8, `E-exact-details.tex`,
`lem:exact-index-rank` and `lem:exact-residual-indexing`.
The stopping-point input is proved by Boolean-cube rank, rather than by the
hard-seed theorem (whose hypothesis excludes the one-bit base matrix).
Numerical gates are explicit; no communication lower bound is an assumption.
-/

namespace EthInapproximability.CurrentPaper.ExactResidualIndexing

open NPCC Workspace.Types.CommComplexity Workspace.Types.Interlace
open EthInapproximability.ParameterizedNP.OneLevelCompletion
open EthInapproximability.ParameterizedNP.SeedSpanLeg

/-- Distinct Boolean columns cannot outnumber the Boolean vectors in their
real column span. The list-label multiplicities have already been removed at
this classical stopping point, and nowhere before it. -/
theorem indexing_rank_card {ι : Type*} [Fintype ι] (S : Finset (ι → Bool)) :
    S.card ≤ 2 ^ (indR (fun i (x : ↥S) => x.val i) true).rank := by
  classical
  let A := indR (fun i (x : ↥S) => x.val i) true
  have hmem : ∀ f ∈ S, boolVec f ∈ Submodule.span ℝ (Set.range A.col) := by
    intro f hf
    refine Submodule.subset_span ⟨⟨f, hf⟩, ?_⟩
    funext i
    simp [A, indR, Matrix.col, boolVec]
  have hc := card_boolVec_le_two_pow_finrank
    (Submodule.span ℝ (Set.range A.col)) S hmem
  rwa [← Matrix.rank_eq_finrank_span_cols] at hc

/-- Integer threshold form of v8 `lem:exact-index-rank`, sufficient for every
stopping-point invocation. The extra answer bit comes from fixed-output rank. -/
theorem indexing_lower_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset (ι → Bool)) (m : ℕ) (hm : 1 ≤ m)
    (hS : 2 ^ (2 ^ (m - 1)) < S.card) :
    m + 1 ≤ D (fun i (x : ↥S) => x.val i) := by
  classical
  have hr : 2 ^ (m - 1) < (indR (fun i (x : ↥S) => x.val i) true).rank := by
    by_contra hn
    have hle := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) (Nat.le_of_not_gt hn)
    have hc := indexing_rank_card S
    omega
  apply fixedOutputRank _ true m hm ?_ hr
  rintro ⟨c, hc⟩
  have hr1 := indR_rank_le_one_of_const hc true
  have hp : 1 ≤ (2 : ℕ) ^ (m - 1) := Nat.one_le_pow _ _ (by omega)
  omega

/-- The one-row bit matrix used by the first sampled interlace. -/
def bit : Unit → Bool → Bool := fun _ b => b

/-- Positive density keeps the unique row in each selected bit block. -/
theorem bit_bracket_rows_full {p : ℕ} {x z : ℝ}
    {R : Finset (Fin p × Unit)} {C : Finset (Fin p → Bool)}
    (hx : 0 < x) (hRC : (R,C) ∈ bracketGE Unit Bool p x z) :
    R = Finset.univ := by
  classical
  apply Finset.eq_univ_iff_forall.mpr
  intro a
  have hrow := hRC.1 a.1 (Finset.mem_univ _)
  have hceil : 0 < ⌈(Fintype.card Unit : ℝ) * x⌉₊ := by
    simpa using (Nat.ceil_pos.mpr hx)
  have hnonempty : (R.filter (fun b => b.1 = a.1)).Nonempty :=
    Finset.card_pos.mp (lt_of_lt_of_le hceil hrow)
  obtain ⟨b,hb⟩ := hnonempty
  have hab : b = a := Prod.ext (Finset.mem_filter.mp hb).2 (Subsingleton.elim _ _)
  simpa [hab] using (Finset.mem_filter.mp hb).1

/-- More than half of the two classical columns keeps both bit values. -/
theorem bit_nonconstant_family {x y : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1) (hy : 1/2 < y) (hy1 : y ≤ 1) :
    1 ≤ Dfamily (interlaceFun bit 1) (bracketGE Unit Bool 1 x y) := by
  classical
  apply le_csInf
  · obtain ⟨RC,hRC⟩ := bracketGE.nonempty (X := Unit) (Y := Bool)
      1 x y hx1 hy1 (by simp)
    exact ⟨_, RC, hRC, rfl⟩
  · rintro n ⟨⟨R,C⟩,hRC,rfl⟩
    have hR := bit_bracket_rows_full hx hRC
    have hCcard : 2 ≤ C.card := by
      have hc := (Nat.ceil_le.mp hRC.2)
      norm_num at hc
      by_contra hn
      have : (C.card : ℝ) ≤ 1 := by exact_mod_cast (show C.card ≤ 1 by omega)
      linarith
    have hC : C = Finset.univ := Finset.eq_univ_of_card _ (by
      apply le_antisymm (Finset.card_le_univ _)
      simpa using hCcard)
    apply SanityChecks.one_le_D_of_two_values_local _
      (a₁ := ⟨(0,()), by simp [hR]⟩) (a₂ := ⟨(0,()), by simp [hR]⟩)
      (b₁ := ⟨fun _ => false, by simp [hC]⟩)
      (b₂ := ⟨fun _ => true, by simp [hC]⟩)
    simp [subgame, interlaceFun, bit]

/-- The actual classical bracket bound needed at the stopping point. -/
theorem bit_seed_family {p m : ℕ} {x z : ℝ}
    (hm : 1 ≤ m) (hx : 0 < x) (hx1 : x ≤ 1) (hz1 : z ≤ 1)
    (hgate : 2 ^ (2 ^ (m - 1)) < ⌈(2 : ℝ) ^ p * z⌉₊) :
    m + 1 ≤ Dfamily (interlaceFun bit p) (bracketGE Unit Bool p x z) := by
  classical
  apply le_csInf
  · obtain ⟨RC,hRC⟩ := bracketGE.nonempty (X := Unit) (Y := Bool)
      p x z hx1 hz1 (by simp)
    exact ⟨_, RC, hRC, rfl⟩
  · rintro n ⟨⟨R,C⟩,hRC,rfl⟩
    have hR := bit_bracket_rows_full hx hRC
    have hc : 2 ^ (2 ^ (m - 1)) < C.card := hgate.trans_le (by
      simpa using hRC.2)
    have hrank := indexing_lower_bound C m hm hc
    have hmap := D_mapNodes_le (subgame (interlaceFun bit p) R C)
      (fun i : Fin p => (⟨(i,()), by simp [hR]⟩ : ↥R))
      (fun c : ↥C => c)
    exact hrank.trans hmap

/-- Scalar stopping for binary indexing, retaining the original sampled
column labels. All premises after balancedness are scalar numerical gates or
cardinalities of the actual retained inputs; no protocol bound is supplied. -/
theorem residual_indexing {t R m p L : ℕ} {x y h z ε : ℝ}
    (S : Fin L → Fin (2 ^ R * t) → Bool)
    (hS : IsBalancedFamily t S ε) (ht : 0 < t) (hm : 1 ≤ m)
    (hx : 0 < x) (hx1 : x ≤ 1) (hy : 1/2 < y) (hy1 : y ≤ 1)
    (hh : 0 < h) (hε : 0 ≤ ε) (hz1 : z ≤ 1)
    (hp1 : t ≤ 2 * p) (hp2 : p ≤ t)
    (hgateRank : 2 ^ (2 ^ (m - 1)) < ⌈(2 : ℝ) ^ p * z⌉₊)
    (hgateOne : y ≤ yLoss ε t h (R + (m + 1)))
    (hgateSeed : z ≤ h * (2 : ℝ) ^ (-((m + 1 : ℕ) : ℝ)) / (1 + ε))
    (R' : ℕ) (hR' : R' ≤ R)
    (I : Finset (Fin (2 ^ R * t))) (C : Finset (Fin L))
    (hI : 2 ^ R' * p ≤ I.card)
    (hrow : (2 : ℝ) ^ R' * x ≤ 1)
    (hC : h * L ≤ (C.card : ℝ)) :
    m + 1 + R' ≤ D (subgame (fun i ℓ => S ℓ i) I C) := by
  classical
  let rows := I.image (fun i => (i, ()))
  obtain ⟨J,hJI,hJcard⟩ := Finset.exists_subset_card_eq hI
  have hrows : ∃ Qs : Finset (Fin (2 ^ R * t)), Qs.card = 2 ^ R' * p ∧
      IsEquipartitionedGE rows Qs
        ⌈(2 : ℝ) ^ R' * x * (Fintype.card Unit : ℝ)⌉₊ := by
    refine ⟨J,hJcard,?_⟩
    intro q hq
    have hceil : ⌈(2 : ℝ) ^ R' * x * (Fintype.card Unit : ℝ)⌉₊ ≤ 1 := by
      apply Nat.ceil_le.mpr
      simpa using hrow
    have hmem : (q,()) ∈ rows.filter (fun b => b.1 = q) := by
      simp only [Finset.mem_filter, rows, Finset.mem_image]
      exact ⟨⟨q,hJI hq,rfl⟩,trivial⟩
    exact hceil.trans (Finset.card_pos.mpr ⟨_,hmem⟩)
  have hstop := CertifiedStopping.scalar_stopping bit hε t R (m + 1) ht S hS p
    hx (le_refl x) hx1 hh hp1 hp2 (bit_nonconstant_family hx hx1 hy hy1)
    hgateOne (bit_seed_family hm hx hx1 hz1 hgateRank) hgateSeed
    0 R' (by omega) hR' rows C hrows (by simpa using hC)
  have hmap := D_mapNodes_le (subgame (fun i ℓ => S ℓ i) I C)
    (fun a : ↥rows => (⟨a.val.1, by
      obtain ⟨i,hi,heq⟩ := Finset.mem_image.mp a.property
      simpa [← heq] using hi⟩ : ↥I))
    (fun c : ↥C => c)
  exact hstop.trans hmap

/-- The same bound with an explicitly checked ambient width. -/
theorem residual_indexing_of_width {q t R m p L : ℕ} {x y h z ε : ℝ}
    (S : Fin L → Fin q → Bool) (hwidth : q = 2 ^ R * t)
    (hS : IsBalancedFamily t S ε) (ht : 0 < t) (hm : 1 ≤ m)
    (hx : 0 < x) (hx1 : x ≤ 1) (hy : 1/2 < y) (hy1 : y ≤ 1)
    (hh : 0 < h) (hε : 0 ≤ ε) (hz1 : z ≤ 1)
    (hp1 : t ≤ 2 * p) (hp2 : p ≤ t)
    (hgateRank : 2 ^ (2 ^ (m - 1)) < ⌈(2 : ℝ) ^ p * z⌉₊)
    (hgateOne : y ≤ yLoss ε t h (R + (m + 1)))
    (hgateSeed : z ≤ h * (2 : ℝ) ^ (-((m + 1 : ℕ) : ℝ)) / (1 + ε))
    (R' : ℕ) (hR' : R' ≤ R) (I : Finset (Fin q)) (C : Finset (Fin L))
    (hI : 2 ^ R' * p ≤ I.card) (hrow : (2 : ℝ) ^ R' * x ≤ 1)
    (hC : h * L ≤ (C.card : ℝ)) :
    m + 1 + R' ≤ D (subgame (fun i ℓ => S ℓ i) I C) := by
  subst q
  exact residual_indexing S hS ht hm hx hx1 hy hy1 hh hε hz1 hp1 hp2
    hgateRank hgateOne hgateSeed R' hR' I C hI hrow hC

open ExactConstruction

/-- The first `2^a` coordinates of the `2^a+1` coordinate first family. -/
def widthCoordinate (a : ℕ) (ha : 2 ≤ a) (i : Fin (width a)) :
    Fin (prefixLength a + 3) :=
  ⟨i.val, by
    have h := Construction.qOne_add_two a (by omega : 1 ≤ a)
    change prefixLength a + 2 = width a at h
    omega⟩

theorem widthCoordinate_injective (a : ℕ) (ha : 2 ≤ a) :
    Function.Injective (widthCoordinate a ha) := by
  intro i j hij
  exact Fin.ext (congrArg (fun x : Fin (prefixLength a + 3) => x.val) hij)

@[simp] theorem widthCoordinate_originalLabel (a : ℕ) (ha : 2 ≤ a)
    (i : Fin (prefixLength a)) :
    widthCoordinate a ha (originalLabel a ha i) = prefixCoordinate a i := by
  apply Fin.ext
  rfl

def widthFamily {a N : ℕ} (ha : 2 ≤ a) (C : FirstFamily a N) :
    Fin N → Fin (width a) → Bool :=
  fun j i => C j (widthCoordinate a ha i)

theorem widthFamily_balanced {a N t : ℕ} (ha : 2 ≤ a)
    {C : FirstFamily a N} {ε : ℝ} (hC : IsBalancedFamily t C ε) :
    IsBalancedFamily t (widthFamily ha C) ε :=
  hC.projection (widthCoordinate a ha) (widthCoordinate_injective a ha)

@[simp] theorem widthFamily_originalLabel {a N : ℕ} (ha : 2 ≤ a)
    (C : FirstFamily a N) (i : Fin (prefixLength a)) (j : Fin N) :
    widthFamily ha C j (originalLabel a ha i) = firstMatrix C i j := by
  simp [widthFamily, firstMatrix]

def widthRows {a : ℕ} (ha : 2 ≤ a) (R : Finset (Fin (prefixLength a))) :
    Finset (Fin (width a)) := R.image (originalLabel a ha)

theorem originalLabel_injective (a : ℕ) (ha : 2 ≤ a) :
    Function.Injective (originalLabel a ha) := by
  intro i j hij
  exact Fin.ext (congrArg (fun x : Fin (width a) => x.val) hij)

@[simp] theorem widthRows_card {a : ℕ} (ha : 2 ≤ a)
    (R : Finset (Fin (prefixLength a))) : (widthRows ha R).card = R.card :=
  Finset.card_image_of_injective _ (originalLabel_injective a ha)

/-- The ambient-width extension leaves the actual retained first matrix
unchanged, including each retained column label. -/
theorem D_widthFamily_restriction_eq {a N : ℕ} (ha : 2 ≤ a)
    (C : FirstFamily a N) (R : Finset (Fin (prefixLength a)))
    (K : Finset (Fin N)) :
    D (subgame (fun i j => widthFamily ha C j i) (widthRows ha R) K) =
      D (subgame (firstMatrix C) R K) := by
  classical
  apply le_antisymm
  · let ρ : {i // i ∈ widthRows ha R} → {i // i ∈ R} := fun i =>
      ⟨(Finset.mem_image.mp i.property).choose,
        (Finset.mem_image.mp i.property).choose_spec.1⟩
    have hρ (i : {i // i ∈ widthRows ha R}) :
        originalLabel a ha (ρ i).val = i.val :=
      (Finset.mem_image.mp i.property).choose_spec.2
    have heq : subgame (fun i j => widthFamily ha C j i) (widthRows ha R) K =
        (fun i j => subgame (firstMatrix C) R K (ρ i) j) := by
      funext i j
      change widthFamily ha C j.val i.val = firstMatrix C (ρ i).val j.val
      rw [← hρ i, widthFamily_originalLabel]
    rw [heq]
    exact D_mapNodes_le _ ρ id
  · let σ : {i // i ∈ R} → {i // i ∈ widthRows ha R} := fun i =>
      ⟨originalLabel a ha i.val, Finset.mem_image_of_mem _ i.property⟩
    have heq : subgame (firstMatrix C) R K =
        (fun i j => subgame (fun i j => widthFamily ha C j i)
          (widthRows ha R) K (σ i) j) := by
      funext i j
      change firstMatrix C i.val j.val =
        widthFamily ha C j.val (originalLabel a ha i.val)
      rw [widthFamily_originalLabel]
    rw [heq]
    exact D_mapNodes_le _ σ id

/-- The residual bound for the literal first matrix of the exact reduction. -/
theorem firstMatrix_residual {a t R m p N : ℕ} {x y h z ε : ℝ}
    (ha : 2 ≤ a) (C₁ : FirstFamily a N) (hwidth : width a = 2 ^ R * t)
    (hS : IsBalancedFamily t C₁ ε) (ht : 0 < t) (hm : 1 ≤ m)
    (hx : 0 < x) (hx1 : x ≤ 1) (hy : 1/2 < y) (hy1 : y ≤ 1)
    (hh : 0 < h) (hε : 0 ≤ ε) (hz1 : z ≤ 1)
    (hp1 : t ≤ 2 * p) (hp2 : p ≤ t)
    (hgateRank : 2 ^ (2 ^ (m - 1)) < ⌈(2 : ℝ) ^ p * z⌉₊)
    (hgateOne : y ≤ yLoss ε t h (R + (m + 1)))
    (hgateSeed : z ≤ h * (2 : ℝ) ^ (-((m + 1 : ℕ) : ℝ)) / (1 + ε))
    (R' : ℕ) (hR' : R' ≤ R)
    (I : Finset (Fin (prefixLength a))) (C : Finset (Fin N))
    (hI : 2 ^ R' * p ≤ I.card) (hrow : (2 : ℝ) ^ R' * x ≤ 1)
    (hC : h * N ≤ (C.card : ℝ)) :
    m + 1 + R' ≤ D (subgame (firstMatrix C₁) I C) := by
  have hresult := residual_indexing_of_width (widthFamily ha C₁) hwidth
    (widthFamily_balanced ha hS) ht hm hx hx1 hy hy1 hh hε hz1 hp1 hp2
    hgateRank hgateOne hgateSeed R' hR' (widthRows ha I) C
    (by simpa using hI) hrow hC
  simpa only [D_widthFamily_restriction_eq] using hresult

/-- Only the two added row labels can be lost when identifying row types. -/
theorem duplicate_image_card_loss (a : ℕ) (ha : 2 ≤ a)
    (I : Finset (Fin (width a))) :
    I.card ≤ (I.image (duplicateLabel a ha)).card + 2 := by
  classical
  have horig : (I.filter (fun i => i.val < prefixLength a)).card ≤
      (I.image (duplicateLabel a ha)).card := by
    apply Finset.card_le_card_of_injOn (duplicateLabel a ha)
    · intro i hi
      exact Finset.mem_image_of_mem _ (Finset.mem_filter.mp hi).1
    · intro i hi j hj hij
      have hi' := (Finset.mem_filter.mp hi).2
      have hj' := (Finset.mem_filter.mp hj).2
      simp only [duplicateLabel, dif_pos hi', dif_pos hj'] at hij
      exact Fin.ext (congrArg (fun x : Fin (prefixLength a) => x.val) hij)
  have hextra : (I.filter (fun i => ¬ i.val < prefixLength a)).card ≤ 2 := by
    have heq : prefixLength a + 2 = width a := Construction.qOne_add_two a (by omega)
    have hh : (I.filter (fun i => ¬ i.val < prefixLength a)).card ≤
        (Finset.range 2).card := by
      apply Finset.card_le_card_of_injOn (fun i : Fin (width a) => i.val - prefixLength a)
      · intro i hi
        have hi' := (Finset.mem_filter.mp hi).2
        have := i.isLt
        apply Finset.mem_range.mpr
        change i.val - prefixLength a < 2
        omega
      · intro i hi j hj hij
        have hi' := (Finset.mem_filter.mp hi).2
        have hj' := (Finset.mem_filter.mp hj).2
        change i.val - prefixLength a = j.val - prefixLength a at hij
        apply Fin.ext
        omega
    simpa using hh
  have hp := I.card_filter_add_card_filter_not (fun i => i.val < prefixLength a)
  omega

/-- Identifying duplicate row labels preserves the exact restricted cost. -/
theorem D_duplicate_subgame {a N : ℕ} (ha : 2 ≤ a)
    (C₁ : FirstFamily a N) (I : Finset (Fin (width a)))
    (C : Finset (Fin N)) :
    D (subgame (duplicatedFirstMatrix ha C₁) I C) =
      D (subgame (firstMatrix C₁) (I.image (duplicateLabel a ha)) C) := by
  classical
  let F : ↥I → ↥(I.image (duplicateLabel a ha)) :=
    fun i => ⟨duplicateLabel a ha i.val, Finset.mem_image_of_mem _ i.property⟩
  have hF : Function.Surjective F := by
    rintro ⟨j, hj⟩
    obtain ⟨i, hi, hij⟩ := Finset.mem_image.mp hj
    exact ⟨⟨i, hi⟩, Subtype.ext hij⟩
  let G := Function.surjInv hF
  have hFG : ∀ j, F (G j) = j := Function.rightInverse_surjInv hF
  exact EthInapproximability.ParameterizedNP.DenseStageFourOpening.D_forget_eq
    (subgame (firstMatrix C₁) (I.image (duplicateLabel a ha)) C)
    F id G id hFG (fun _ => rfl)

open Classical in
/-- Projection of a one-fold interlace to the underlying plain submatrix. -/
theorem D_plain_subgame_le_oneCopy {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) (R : Finset (Fin 1 × X)) (C : Finset (Fin 1 → Y)) :
    D (subgame f (R.image Prod.snd) (C.image (fun c => c 0))) ≤
      D (subgame (interlaceFun f 1) R C) := by
  classical
  let ρ : {x // x ∈ R.image Prod.snd} → {r // r ∈ R} := fun x =>
    ⟨(Finset.mem_image.mp x.property).choose,
      (Finset.mem_image.mp x.property).choose_spec.1⟩
  let σ : {y // y ∈ C.image (fun c => c 0)} → {c // c ∈ C} := fun y =>
    ⟨(Finset.mem_image.mp y.property).choose,
      (Finset.mem_image.mp y.property).choose_spec.1⟩
  have hρ (x : {x // x ∈ R.image Prod.snd}) : (ρ x).val.2 = x.val :=
    (Finset.mem_image.mp x.property).choose_spec.2
  have hσ (y : {y // y ∈ C.image (fun c => c 0)}) : (σ y).val 0 = y.val :=
    (Finset.mem_image.mp y.property).choose_spec.2
  have heq : subgame f (R.image Prod.snd) (C.image (fun c => c 0)) =
      (fun x y => subgame (interlaceFun f 1) R C (ρ x) (σ y)) := by
    funext x y
    change f x.val y.val = f (ρ x).val.2 ((σ y).val (ρ x).val.1)
    rw [hρ, show (ρ x).val.1 = (0 : Fin 1) from Subsingleton.elim _ _, hσ]
  rw [heq]
  exact D_mapNodes_le _ ρ σ

/-- Every one-copy bracket member is a plain submatrix with the same
retained densities; this wrapper introduces no additional lower bound. -/
theorem oneCopy_family_lower_of_subgame {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] (f : X → Y → Bool) {x y : ℝ} {K : ℕ}
    (hx : x ≤ 1) (hy : y ≤ 1)
    (hplain : ∀ (R : Finset X) (C : Finset Y),
      (Fintype.card X : ℝ) * x ≤ R.card →
      (Fintype.card Y : ℝ) * y ≤ C.card → K ≤ D (subgame f R C)) :
    K ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x y) := by
  classical
  apply le_csInf
  · obtain ⟨RC, hRC⟩ := bracketGE.nonempty (X := X) (Y := Y)
      1 x y hx hy (by exact Fintype.card_pos)
    exact ⟨_, RC, hRC, rfl⟩
  · rintro n ⟨⟨R, C⟩, ⟨hR, hC⟩, rfl⟩
    have hrow := hR 0 (Finset.mem_univ 0)
    have hfilter : R.filter (fun p => p.1 = (0 : Fin 1)) = R := by
      apply Finset.filter_eq_self.mpr
      intro p _
      exact Subsingleton.elim _ _
    rw [hfilter] at hrow
    have hinjR : Function.Injective (Prod.snd : Fin 1 × X → X) := by
      intro a b hab
      exact Prod.ext (Subsingleton.elim _ _) hab
    have hinjC : Function.Injective (fun c : Fin 1 → Y => c 0) := by
      intro a b hab
      funext i
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      simpa [hi] using hab
    have hRcard : (R.image Prod.snd).card = R.card :=
      Finset.card_image_of_injective _ hinjR
    have hCcard : (C.image (fun c => c 0)).card = C.card :=
      Finset.card_image_of_injective _ hinjC
    have hplainCost := hplain (R.image Prod.snd) (C.image (fun c => c 0))
      (by rw [hRcard]; exact Nat.ceil_le.mp hrow)
      (by rw [hCcard]; simpa only [pow_one] using Nat.ceil_le.mp hC)
    exact hplainCost.trans (D_plain_subgame_le_oneCopy f R C)

end EthInapproximability.CurrentPaper.ExactResidualIndexing
