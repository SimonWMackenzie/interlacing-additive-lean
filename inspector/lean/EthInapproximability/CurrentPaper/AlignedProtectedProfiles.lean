import EthInapproximability.CurrentPaper.ExactCoordinateControl
import EthInapproximability.CurrentPaper.ExactResidualIndexing
import EthInapproximability.CurrentPaper.Restoration
import EthInapproximability.CurrentPaper.JointTransfer
import EthInapproximability.CurrentPaper.ParameterGates

/-!
# Reference-row bounds after the internal interlace

Source: frozen v8 `A-stage4-details.tex`, final restriction proof of
`thm:parameterized-one-bit`, paragraphs "The reference bounds" and
"The total row count". The input reference matrix is literally a row
restriction of `N`, with all its columns. We retain original joint column
sets throughout. The full-product family is proved exactly balanced here.

The moderate bounds are derived from the two reference-matrix profiles and
explicit scalar stopping/counting gates. The near-full bound is NOT a
consequence of these two profiles: it still requires the global routing
and additional-row argument. The final transpose/cost composition below
keeps that genuine missing premise visible.
-/

noncomputable section

namespace EthInapproximability.CurrentPaper.AlignedProtectedProfiles

open NPCC Workspace.Types.CommComplexity Workspace.Types.Interlace
open ProtocolSeparation ExactCoordinateControl ExactResidualIndexing
open EthInapproximability.ParameterizedNP

variable {X Y Ref : Type*}

/-- The reference carrier of the actual two-support construction has the
precise `91/92` fraction required below, including the uniform duplicates. -/
theorem physical_reference_proportion [Fintype Y] (a s q : ℕ) :
    (Fintype.card ↥(JointTransfer.referenceRows (Y := Y) a s q) : ℝ) =
      (91 / 92 : ℝ) * Fintype.card (Construction.ProtectedColumns a s q Y) := by
  classical
  have hc : (JointTransfer.referenceRows (Y := Y) a s q).card =
      Fintype.card (WeightedDuplication.Group
        (WeightedDuplication.columnSupport (Construction.RawColumns a s q Y)
          (Construction.SecondRows a s q Y)) WeightedDuplication.columnWeight 0) *
        Construction.uniformCopies (Y := Y) a s q := by
    rw [JointTransfer.referenceRows, Finset.card_image_of_injective _
      (JointTransfer.referenceEmbedding a s q).injective, Finset.card_univ]
    conv_rhs =>
      rw [← Fintype.card_fin (Construction.uniformCopies (Y := Y) a s q),
        ← Fintype.card_prod]
    exact Fintype.card_congr
      { toFun := fun z => (((z.2.1, z.1), z.2.2.1), z.2.2.2)
        invFun := fun z => (z.1.1.2, (z.1.1.1, (z.1.2, z.2)))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  simp only [Fintype.card_coe, hc]
  rw [WeightedDuplication.card_group, WeightedDuplication.card_columns]
  norm_num [WeightedDuplication.columnWeight, WeightedDuplication.card_columnSupport,
    Fin.prod_univ_succ]
  ring

/-- An embedded reference row keeps its outer selector. -/
def referenceRowEmbedding (e : Ref ↪ X) (q : ℕ) : (Fin q × Ref) ↪ (Fin q × X) :=
  Function.Embedding.prodMap (Function.Embedding.refl _) e

/-- The reference rows actually retained by a parent restriction. -/
def referencePullback [Fintype Ref] {q : ℕ} (e : Ref ↪ X)
    (A : Finset (Fin q × X)) : Finset (Fin q × Ref) := by
  classical
  exact Finset.univ.filter (fun r => referenceRowEmbedding e q r ∈ A)

@[simp] theorem mem_referencePullback [Fintype Ref] {q : ℕ} (e : Ref ↪ X)
    (A : Finset (Fin q × X)) (r : Fin q × Ref) :
    r ∈ referencePullback e A ↔ (r.1, e r.2) ∈ A := by
  classical
  cases r
  simp [referencePullback, referenceRowEmbedding, Function.Embedding.prodMap]

/-- Discarding nonreference rows loses at most their entire ambient count.
The inequality is on actual finite row sets, before division or ceilings. -/
theorem reference_retained_count [Fintype X] [Fintype Ref] {q : ℕ}
    (e : Ref ↪ X) (A : Finset (Fin q × X)) :
    A.card + q * Fintype.card Ref ≤
      (referencePullback e A).card + q * Fintype.card X := by
  classical
  let B := (Finset.univ : Finset (Fin q × Ref)).map (referenceRowEmbedding e q)
  have hB : B.card = q * Fintype.card Ref := by simp [B]
  have hinter : A ∩ B = (referencePullback e A).map (referenceRowEmbedding e q) := by
    ext r
    simp only [Finset.mem_inter, B, Finset.mem_map, Finset.mem_univ, true_and,
      referencePullback, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hr, z, rfl⟩
      exact ⟨z, hr, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hz, z, rfl⟩
  have hunion : (A ∪ B).card ≤ q * Fintype.card X := by
    simpa using Finset.card_le_univ (A ∪ B)
  have hsum := Finset.card_union_add_card_inter A B
  rw [hinter, Finset.card_map, hB] at hsum
  omega

/-- The paper's exact reference density `(beta-(1-g))/g`.
Here `g` is the fraction of the ambient rows occupied by the reference
embedding, not a hypothesis about their retained density. -/
theorem reference_retained_density [Fintype X] [Fintype Ref] {q : ℕ}
    (e : Ref ↪ X) (A : Finset (Fin q × X)) {g β : ℝ}
    (hg : 0 < g) (hprop : (Fintype.card Ref : ℝ) = g * Fintype.card X)
    (hA : β * ((q : ℝ) * Fintype.card X) ≤ A.card) :
    ((β - (1 - g)) / g) * ((q : ℝ) * Fintype.card Ref) ≤
      (referencePullback e A).card := by
  have hc : (A.card : ℝ) + (q : ℝ) * Fintype.card Ref ≤
      ((referencePullback e A).card : ℝ) + (q : ℝ) * Fintype.card X := by
    exact_mod_cast reference_retained_count e A
  rw [hprop] at hc ⊢
  have heq : (β - (1 - g)) / g * ((q : ℝ) * (g * Fintype.card X)) =
      (β - (1 - g)) * ((q : ℝ) * Fintype.card X) := by
    field_simp
  rw [heq]
  nlinarith

/-- A reference-row restriction and its actual parent have the SAME joint
column set. No product of separate coordinate projections is substituted. -/
theorem reference_restriction_le [Fintype Ref] {q : ℕ}
    (N : X → Y → Bool) (e : Ref ↪ X)
    (A : Finset (Fin q × X)) (S : Finset (Fin q → Y)) :
    D (subgame (interlaceFun (fun r y => N (e r) y) q)
      (referencePullback e A) S) ≤ D (subgame (interlaceFun N q) A S) := by
  classical
  let row : ↥(referencePullback e A) → ↥A := fun r =>
    ⟨(r.val.1, e r.val.2), (mem_referencePullback e A r.val).mp r.property⟩
  exact D_mapNodes_le (subgame (interlaceFun N q) A S) row id

/-- Generic finite count used by exact full-product balance. -/
private def agreementEquiv [DecidableEq Y] {q : ℕ}
    (J : Finset (Fin q)) (a : Fin q → Y) :
    {s : Fin q → Y // ∀ i ∈ J, s i = a i} ≃ ({i : Fin q // i ∉ J} → Y) where
  toFun s := fun i => s.val i.val
  invFun f := ⟨fun i => if h : i ∈ J then a i else f ⟨i, h⟩,
    by intro i hi; simp [hi]⟩
  left_inv s := by
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ J
    · simp [hi, s.property i hi]
    · simp [hi]
  right_inv f := by funext i; simp [i.property]

/-- Every exact enumeration of all tuples has zero balancing error.
The elementary agreement-count proof is reconstructed from the generic
counting argument in legacy `TerminalTwoStream`, not its protected theorem. -/
theorem fullProduct_balanced [Fintype Y] [DecidableEq Y] [Nonempty Y]
    {q L : ℕ} (t : ℕ) (S : Fin L ≃ (Fin q → Y)) :
    IsBalancedFamily t S 0 := by
  classical
  have hL : L = Fintype.card Y ^ q := by
    simpa using Fintype.card_congr S
  refine ⟨by rw [hL]; positivity, ?_⟩
  intro J _ a
  have hcount : (Finset.univ.filter (fun j : Fin L => ∀ i ∈ J, S j i = a i)).card =
      Fintype.card Y ^ (q - J.card) := by
    rw [← Fintype.card_subtype]
    calc
      _ = Fintype.card {s : Fin q → Y // ∀ i ∈ J, s i = a i} :=
        Fintype.card_congr (Equiv.subtypeEquiv S (fun _ => Iff.rfl))
      _ = _ := by
        rw [Fintype.card_congr (agreementEquiv J a), Fintype.card_fun,
          Fintype.card_subtype_compl]
        simp
  have hJ : J.card ≤ q := by simpa using Finset.card_le_univ J
  have hsplit : (Fintype.card Y : ℝ) ^ q =
      (Fintype.card Y : ℝ) ^ (q - J.card) * (Fintype.card Y : ℝ) ^ J.card := by
    rw [← pow_add, Nat.sub_add_cancel hJ]
  have hY : (0 : ℝ) < Fintype.card Y := by exact_mod_cast Fintype.card_pos (α := Y)
  rw [hcount, hL]
  push_cast
  rw [hsplit]
  field_simp
  simp

/-- Localized stopping on literal full-product columns. Its only matrix
premises are the TWO reference profiles; balance is proved, not assumed. -/
theorem fullProduct_blockLowerBound [Fintype Ref] [Fintype Y]
    [DecidableEq Y] [Nonempty Ref] [Nonempty Y]
    (M : Ref → Y → Bool) {H m R q : ℕ} {x h : ℝ}
    (hwidth : q = 2 ^ R * 2 ^ m) (hH : 2 ≤ H) (hm : 2 ^ 20 ≤ m)
    (hx : 0 < x) (hrow : (2 : ℝ) ^ m * x ≤ 1) (hh : 0 < h)
    (h1 : H ≤ Dfamily (interlaceFun M 1) (bracketGE Ref Y 1 x (3 / 5)))
    (h2 : H - 1 ≤ Dfamily (interlaceFun M 1) (bracketGE Ref Y 1 x (3 / 10)))
    (hgateOne : (3 / 5 : ℝ) ≤ yLoss 0 (2 ^ m) h (H + (R + m)))
    (hgateSeed : HardSeed.columnDensity ((2 : ℝ) ^ m) ≤
      h * (2 : ℝ) ^ (-((H + m : ℕ) : ℝ)))
    (R' : ℕ) (hR' : R' ≤ R) :
    BlockLowerBound (interlaceFun M q) Prod.fst Finset.univ
      (2 ^ R' * HardSeed.copyCount m)
      ⌈(2 : ℝ) ^ (R' + m) * x * (Fintype.card Ref : ℝ)⌉₊ h
      (H + (R' + m)) := by
  classical
  let S : Fin (Fintype.card (Fin q → Y)) ≃ (Fin q → Y) :=
    (Fintype.equivFin _).symm
  have hbound := coordinateBlockLowerBound_of_width (z := h) M hwidth hH hm hx hrow
    (by norm_num : (0 : ℝ) ≤ 0) hh h1 h2 ((by omega : 1 ≤ H).trans h1)
    S (fullProduct_balanced (2 ^ m) S) hgateOne
    (by simpa using hgateSeed) 0 R' (2 ^ R' * HardSeed.copyCount m)
    ⌈(2 : ℝ) ^ (R' + m) * x * (Fintype.card Ref : ℝ)⌉₊
    (by omega) hR' (le_refl _) (le_refl _) (by simp)
  intro A C Q _ hC hQ hA
  let C' := C.image S.symm
  have hcard : C'.card = C.card := Finset.card_image_of_injective _ S.symm.injective
  have hlower := hbound A C' Q (Finset.subset_univ _)
    (by simpa only [C', hcard, Finset.card_univ, Fintype.card_fin] using hC) hQ hA
  let col : ↥C' → ↥C := fun j => ⟨S j.val, by
    obtain ⟨c, hc, heq⟩ := Finset.mem_image.mp j.property
    simpa only [← heq, S.apply_symm_apply] using hc⟩
  exact hlower.trans (D_mapNodes_le (subgame (interlaceFun M q) A C) id col)

/-- Reference deletion, actual block selection, and localized stopping
combined into a lower bound for an arbitrary restriction of `Int_q N`. -/
theorem interlace_moderate_lower [Fintype X] [Fintype Ref] [Fintype Y]
    [DecidableEq Y] [Nonempty Ref] [Nonempty Y]
    (N : X → Y → Bool) (e : Ref ↪ X)
    {H m R q : ℕ} {x h g β : ℝ}
    (hwidth : q = 2 ^ R * 2 ^ m) (hH : 2 ≤ H) (hm : 2 ^ 20 ≤ m)
    (hx : 0 < x) (hrow : (2 : ℝ) ^ m * x ≤ 1) (hh : 0 < h)
    (hg : 0 < g) (hprop : (Fintype.card Ref : ℝ) = g * Fintype.card X)
    (h1 : H ≤ Dfamily (interlaceFun (fun r y => N (e r) y) 1)
      (bracketGE Ref Y 1 x (3 / 5)))
    (h2 : H - 1 ≤ Dfamily (interlaceFun (fun r y => N (e r) y) 1)
      (bracketGE Ref Y 1 x (3 / 10)))
    (hgateOne : (3 / 5 : ℝ) ≤ yLoss 0 (2 ^ m) h (H + (R + m)))
    (hgateSeed : HardSeed.columnDensity ((2 : ℝ) ^ m) ≤
      h * (2 : ℝ) ^ (-((H + m : ℕ) : ℝ)))
    (R' : ℕ) (hR' : R' ≤ R)
    (hsmall : (2 : ℝ) ^ (R' + m) * x < 1)
    (hcount : 2 ^ R' * HardSeed.copyCount m ≤
      ⌈(q : ℝ) * (((β - (1 - g)) / g) - (2 : ℝ) ^ (R' + m) * x) /
        (1 - (2 : ℝ) ^ (R' + m) * x)⌉₊)
    (A : Finset (Fin q × X)) (S : Finset (Fin q → Y))
    (hA : β * ((q : ℝ) * Fintype.card X) ≤ A.card)
    (hS : h * (Fintype.card (Fin q → Y) : ℝ) ≤ S.card) :
    H + (R' + m) ≤ D (subgame (interlaceFun N q) A S) := by
  have hq : 0 < q := by rw [hwidth]; positivity
  have hv : 1 ≤ 2 ^ R' * HardSeed.copyCount m := by
    have hp := (HardSeed.copyCount_bounds (show 5 ≤ m by omega)).1
    have : 1 ≤ (2 : ℕ) ^ R' := one_le_pow₀ (by omega)
    nlinarith
  have hb := fullProduct_blockLowerBound (fun r y => N (e r) y) hwidth hH hm
    hx hrow hh h1 h2 hgateOne hgateSeed R' hR'
  have hlower := lowerBound_of_denseRows (interlaceFun (fun r y => N (e r) y) q)
    Finset.univ hq (by positivity : 0 < (2 : ℝ) ^ (R' + m) * x) hsmall hv
    (by rw [mul_comm (Fintype.card Ref : ℝ)])
    hcount hb (referencePullback e A) S (reference_retained_density e A hg hprop hA)
    (Finset.subset_univ _) (by simpa using hS)
  exact hlower.trans (reference_restriction_le N e A S)

/-- The numeric comparison used at the two moderate densities. The retained
reference proportion is exactly `91/92`; the constants are not relaxed. -/
theorem reference_count_comparison {q k x : ℝ} (hq : 0 < q) (hk : 0 < k)
    (d : ℕ) (hd : d = 1 ∨ d = 2)
    (hwidth : q = d * k) (hsmall : q * x ≤ 4 / 25025) :
    k * x < 1 ∧ (9 : ℝ) * k / 16 ≤
      q * (((3 / (5 * d) - (1 - 91 / 92)) / (91 / 92)) - k * x) / (1 - k * x) := by
  have hkx : k * x < 1 := by
    rcases hd with rfl | rfl <;> norm_num at hwidth ⊢ <;> nlinarith
  refine ⟨hkx, ?_⟩
  rw [le_div_iff₀ (by linarith : 0 < 1 - k * x), hwidth]
  have hcoeff : (9 / 16 : ℝ) * (1 - k * x) ≤
      (d : ℝ) * (((3 / (5 * d) - (1 - 91 / 92)) / (91 / 92)) - k * x) := by
    rcases hd with rfl | rfl <;> norm_num at hwidth ⊢ <;> nlinarith
  have hmult := mul_le_mul_of_nonneg_left hcoeff hk.le
  nlinarith

/-- `copyCount` is the exact integral `9/16` fraction at both residual
dyadic widths; the large source cutoff makes the divisibility automatic. -/
theorem residual_copyCount_cast (m R' : ℕ) (hm : 5 ≤ m) :
    ((2 ^ R' * HardSeed.copyCount m : ℕ) : ℝ) =
      9 * (2 : ℝ) ^ (R' + m) / 16 := by
  have hp : (2 : ℕ) ^ m = 32 * 2 ^ (m - 5) := by
    calc
      (2 : ℕ) ^ m = 2 ^ ((m - 5) + 5) := by rw [Nat.sub_add_cancel hm]
      _ = 32 * 2 ^ (m - 5) := by rw [pow_add]; ring
  have heq : 16 * HardSeed.copyCount m = 9 * 2 ^ m := by
    rw [hp]
    unfold HardSeed.copyCount
    ring
  have heqR : (16 : ℝ) * (HardSeed.copyCount m : ℝ) = 9 * (2 : ℝ) ^ m := by
    exact_mod_cast heq
  push_cast
  rw [pow_add]
  have hh := congrArg (fun z : ℝ => (2 : ℝ) ^ R' * z) heqR
  nlinarith

/-- The two ceiling-sensitive block-count gates are derived from the
paper's single smallness condition `q*x <= 4/25025`. -/
theorem moderate_count_gates {q m R : ℕ} {x : ℝ}
    (hwidth : q = 2 ^ R * 2 ^ m) (hR : 1 ≤ R) (hm : 5 ≤ m)
    (hsmall : (q : ℝ) * x ≤ 4 / 25025) :
    ((2 : ℝ) ^ (R + m) * x < 1 ∧
      2 ^ R * HardSeed.copyCount m ≤
        ⌈(q : ℝ) * (((3 / 5 - (1 - 91 / 92)) / (91 / 92)) -
          (2 : ℝ) ^ (R + m) * x) / (1 - (2 : ℝ) ^ (R + m) * x)⌉₊) ∧
    ((2 : ℝ) ^ (R - 1 + m) * x < 1 ∧
      2 ^ (R - 1) * HardSeed.copyCount m ≤
        ⌈(q : ℝ) * (((3 / 10 - (1 - 91 / 92)) / (91 / 92)) -
          (2 : ℝ) ^ (R - 1 + m) * x) / (1 - (2 : ℝ) ^ (R - 1 + m) * x)⌉₊) := by
  have hq : 0 < q := by rw [hwidth]; positivity
  have hfull : (q : ℝ) = 1 * (2 : ℝ) ^ (R + m) := by
    rw [hwidth]; push_cast; simp [pow_add]
  have hhalf : (q : ℝ) = 2 * (2 : ℝ) ^ (R - 1 + m) := by
    rw [hfull, one_mul]
    calc
      (2 : ℝ) ^ (R + m) = 2 ^ ((R - 1 + m) + 1) := by congr 1; omega
      _ = _ := by rw [pow_succ]; ring
  have hf := reference_count_comparison (q := (q : ℝ)) (k := (2 : ℝ) ^ (R + m))
    (x := x) (by exact_mod_cast hq)
    (by positivity) 1 (Or.inl rfl) (by simpa using hfull) hsmall
  have hh := reference_count_comparison (q := (q : ℝ)) (k := (2 : ℝ) ^ (R - 1 + m))
    (x := x) (by exact_mod_cast hq)
    (by positivity) 2 (Or.inr rfl) (by simpa using hhalf) hsmall
  norm_num at hf hh ⊢
  refine ⟨⟨hf.1, ?_⟩, ⟨hh.1, ?_⟩⟩
  · apply (Nat.cast_le (α := ℝ)).mp
    rw [residual_copyCount_cast m R hm]
    exact hf.2.trans (Nat.le_ceil _)
  · apply (Nat.cast_le (α := ℝ)).mp
    rw [residual_copyCount_cast m (R - 1) hm]
    exact hh.2.trans (Nat.le_ceil _)

section Profiles

variable [Fintype X] [Fintype Ref] [Fintype Y] [DecidableEq Y]
    [Nonempty X] [Nonempty Ref] [Nonempty Y]
    (N : X → Y → Bool) (e : Ref ↪ X)
    {H m R q : ℕ} {x h : ℝ}
    (hwidth : q = 2 ^ R * 2 ^ m) (hH : 2 ≤ H) (hm : 2 ^ 20 ≤ m)
    (hx : 0 < x) (hrow : (2 : ℝ) ^ m * x ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (hprop : (Fintype.card Ref : ℝ) = (91 / 92 : ℝ) * Fintype.card X)
    (h1 : H ≤ Dfamily (interlaceFun (fun r y => N (e r) y) 1)
      (bracketGE Ref Y 1 x (3 / 5)))
    (h2 : H - 1 ≤ Dfamily (interlaceFun (fun r y => N (e r) y) 1)
      (bracketGE Ref Y 1 x (3 / 10)))
    (hgateOne : (3 / 5 : ℝ) ≤ yLoss 0 (2 ^ m) h (H + (R + m)))
    (hgateSeed : HardSeed.columnDensity ((2 : ℝ) ^ m) ≤
      h * (2 : ℝ) ^ (-((H + m : ℕ) : ℝ)))

include hwidth hH hm hx hrow hh hh1 hprop h1 h2 hgateOne hgateSeed

/-- One-copy profile of the literal transpose of the first interlace.
The row/column fractions are exchanged, with no second interlace yet. -/
theorem aligned_oneCopy_lower {β : ℝ} (hβ : β ≤ 1)
    (R' : ℕ) (hR' : R' ≤ R)
    (hsmall : (2 : ℝ) ^ (R' + m) * x < 1)
    (hcount : 2 ^ R' * HardSeed.copyCount m ≤
      ⌈(q : ℝ) * (((β - (1 - 91 / 92)) / (91 / 92)) -
        (2 : ℝ) ^ (R' + m) * x) / (1 - (2 : ℝ) ^ (R' + m) * x)⌉₊) :
    H + (R' + m) ≤ Dfamily
      (interlaceFun (fun γ r => interlaceFun N q r γ) 1)
      (bracketGE (Fin q → Y) (Fin q × X) 1 h β) := by
  apply oneCopy_family_lower_of_subgame (fun γ r => interlaceFun N q r γ) hh1 hβ
  intro S A hS hA
  have hlower := interlace_moderate_lower N e hwidth hH hm hx hrow hh
    (by norm_num : (0 : ℝ) < 91 / 92) hprop h1 h2 hgateOne hgateSeed R' hR'
    hsmall hcount A S
    (by simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul,
      mul_comm, mul_left_comm, mul_assoc] using hA) (by simpa [mul_comm] using hS)
  have heq : D (subgame (fun γ r => interlaceFun N q r γ) S A) =
      D (subgame (interlaceFun N q) A S) := comp_transpose _
  rwa [heq]

/-- Both moderate profiles, with their block-count premises discharged.
At the manuscript instantiation `H=C-1`, these are the `C+r_q-1` and
`C+r_q-2` rungs consumed by restoration. -/
theorem aligned_moderate_profiles (hR : 1 ≤ R)
    (hsmall : (q : ℝ) * x ≤ 4 / 25025) :
    (H + (R + m) ≤ Dfamily
      (interlaceFun (fun γ r => interlaceFun N q r γ) 1)
      (bracketGE (Fin q → Y) (Fin q × X) 1 h (3 / 5))) ∧
    (H + (R + m) - 1 ≤ Dfamily
      (interlaceFun (fun γ r => interlaceFun N q r γ) 1)
      (bracketGE (Fin q → Y) (Fin q × X) 1 h (3 / 10))) := by
  obtain ⟨hfull, hhalf⟩ := moderate_count_gates hwidth hR (by omega) hsmall
  constructor
  · exact aligned_oneCopy_lower N e hwidth hH hm hx hrow hh hh1 hprop
      h1 h2 hgateOne hgateSeed (by norm_num) R (le_refl _) hfull.1 hfull.2
  · have hh := aligned_oneCopy_lower N e hwidth hH hm hx hrow hh hh1 hprop
      h1 h2 hgateOne hgateSeed (by norm_num : (3 / 10 : ℝ) ≤ 1)
      (R - 1) (Nat.sub_le R 1) hhalf.1 hhalf.2
    convert hh using 1 <;> omega

/-- Exact-cost and all three aligned profiles from the reference argument
and the still-separate full-cost global row-count theorem. `hnear` is stated
on arbitrary actual restrictions of `Int_q N`; this theorem does not pretend
to prove it from the protected `N` profiles alone. -/
theorem aligned_profiles_of_near_lower (hR : 1 ≤ R)
    (hsmall : (q : ℝ) * x ≤ 4 / 25025)
    (hupper : D N ≤ H + 1) {δ : ℝ} (hδ : 0 ≤ δ)
    (hnear : ∀ (A : Finset (Fin q × X)) (S : Finset (Fin q → Y)),
      (1 - δ) * ((q : ℝ) * Fintype.card X) ≤ A.card →
      h * (Fintype.card (Fin q → Y) : ℝ) ≤ S.card →
      H + 1 + (R + m) ≤ D (subgame (interlaceFun N q) A S)) :
    let W := fun γ r => interlaceFun N q r γ
    let C := H + 1 + (R + m)
    D W = C ∧
    C ≤ Dfamily (interlaceFun W 1)
      (bracketGE (Fin q → Y) (Fin q × X) 1 h (1 - δ)) ∧
    C - 1 ≤ Dfamily (interlaceFun W 1)
      (bracketGE (Fin q → Y) (Fin q × X) 1 h (3 / 5)) ∧
    C - 2 ≤ Dfamily (interlaceFun W 1)
      (bracketGE (Fin q → Y) (Fin q × X) 1 h (3 / 10)) := by
  classical
  let W := fun γ r => interlaceFun N q r γ
  have hn : H + 1 + (R + m) ≤ Dfamily (interlaceFun W 1)
      (bracketGE (Fin q → Y) (Fin q × X) 1 h (1 - δ)) := by
    apply oneCopy_family_lower_of_subgame W hh1 (by linarith)
    intro S A hS hA
    have ht : D (subgame W S A) = D (subgame (interlaceFun N q) A S) :=
      comp_transpose _
    rw [ht]
    exact hnear A S
      (by simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul,
        mul_comm, mul_left_comm, mul_assoc] using hA) (by simpa [mul_comm] using hS)
  obtain ⟨hmiddle, hhalf⟩ := aligned_moderate_profiles N e hwidth hH hm hx hrow
    hh hh1 hprop h1 h2 hgateOne hgateSeed hR hsmall
  have hup : D W ≤ H + 1 + (R + m) := by
    have hq : q = 2 ^ (R + m) := by simpa only [pow_add] using hwidth
    dsimp [W]
    rw [comp_transpose, hq]
    exact (powerOfTwoInterlace_upper N (R + m)).trans (Nat.add_le_add_right hupper _)
  have hlo : H + 1 + (R + m) ≤ D W := by
    have hall := hnear Finset.univ Finset.univ
      (by
        simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
        exact mul_le_of_le_one_left (by positivity) (by linarith))
      (by
        simpa using mul_le_of_le_one_left
          (Nat.cast_nonneg (Fintype.card (Fin q → Y))) hh1)
    have hsub := D_mapNodes_le (interlaceFun N q)
      (fun r : ↥(Finset.univ : Finset (Fin q × X)) => r.val)
      (fun γ : ↥(Finset.univ : Finset (Fin q → Y)) => γ.val)
    have ht : D W = D (interlaceFun N q) := comp_transpose _
    rw [ht]
    exact hall.trans hsub
  change D W = _ ∧ _
  refine ⟨le_antisymm hup hlo, hn, ?_, ?_⟩ <;> dsimp only [W] at * <;> omega

end Profiles

/-- The actual parameter formulas discharge all scalar reference-alignment
gates. Only the two upstream profiles of the embedded reference matrix and
its physical row proportion remain as matrix premises. -/
theorem aligned_moderate_profiles_parameters [Fintype X] [Fintype Ref] [Fintype Y]
    [DecidableEq Y] [Nonempty X] [Nonempty Ref] [Nonempty Y]
    (N : X → Y → Bool) (e : Ref ↪ X) (i : Parameters.Input)
    (hprop : (Fintype.card Ref : ℝ) = (91 / 92 : ℝ) * Fintype.card X)
    (h1 : Parameters.certificateCost i - 1 ≤
      Dfamily (interlaceFun (fun r y => N (e r) y) 1)
        (bracketGE Ref Y 1 ((2 : ℝ) ^ (-(Parameters.tailDepth i : ℝ))) (3 / 5)))
    (h2 : Parameters.certificateCost i - 2 ≤
      Dfamily (interlaceFun (fun r y => N (e r) y) 1)
        (bracketGE Ref Y 1 ((2 : ℝ) ^ (-(Parameters.tailDepth i : ℝ))) (3 / 10))) :
    let W := fun γ r => interlaceFun N (Parameters.outerWidth i) r γ
    let θ : ℝ := Parameters.retainedFraction i
    (Parameters.certificateCost i + Parameters.outerExponent i - 1 ≤
      Dfamily (interlaceFun W 1)
        (bracketGE (Fin (Parameters.outerWidth i) → Y)
          (Fin (Parameters.outerWidth i) × X) 1 θ (3 / 5))) ∧
    (Parameters.certificateCost i + Parameters.outerExponent i - 2 ≤
      Dfamily (interlaceFun W 1)
        (bracketGE (Fin (Parameters.outerWidth i) → Y)
          (Fin (Parameters.outerWidth i) × X) 1 θ (3 / 10))) := by
  have hscale : 1 ≤ Parameters.scale i := (by norm_num : 1 ≤ (2 : ℕ) ^ 24).trans
    (Parameters.scale_floor i)
  have hscaleSq : 1 ≤ Parameters.scale i ^ 2 := one_le_pow₀ hscale
  have hexp : Parameters.referenceExponent i + 1 ≤ Parameters.outerExponent i := by
    unfold Parameters.referenceExponent Parameters.outerExponent
    nlinarith
  have hC : 3 ≤ Parameters.certificateCost i := by
    unfold Parameters.certificateCost Parameters.firstExponent
    omega
  have hwidth : Parameters.outerWidth i =
      2 ^ (Parameters.outerExponent i - Parameters.referenceExponent i) *
        2 ^ Parameters.referenceExponent i := by
    rw [← pow_add, Nat.sub_add_cancel (by omega)]
    rfl
  have hs := ParameterGates.reference_stopping_gates i
  have hθ0 : (0 : ℝ) < (Parameters.retainedFraction i : ℚ) := by
    exact_mod_cast Parameters.retainedFraction_pos i
  have hθ1 : ((Parameters.retainedFraction i : ℚ) : ℝ) ≤ 1 := by
    have hQ : (1 : ℝ) ≤ Parameters.restorationWidth i := by
      exact_mod_cast Parameters.restorationWidth_pos i
    have hid : (Parameters.restorationWidth i : ℝ) *
        ((Parameters.retainedFraction i : ℚ) : ℝ) = 1 / 160 := by
      have hh := congrArg (fun z : ℚ => (z : ℝ)) (Parameters.retainedFraction_identity i)
      norm_num at hh ⊢
      exact hh
    nlinarith
  have hgOne : (3 / 5 : ℝ) ≤ yLoss 0 (2 ^ Parameters.referenceExponent i)
      (Parameters.retainedFraction i : ℚ)
      (Parameters.certificateCost i - 1 +
        (Parameters.outerExponent i - Parameters.referenceExponent i +
          Parameters.referenceExponent i)) := by
    simpa only [Nat.sub_add_cancel (show Parameters.referenceExponent i ≤
      Parameters.outerExponent i by omega), yLoss, Parameters.referenceWidth,
      Nat.cast_pow, Nat.cast_ofNat, add_zero, div_one] using hs.1
  have hgSeed : HardSeed.columnDensity ((2 : ℝ) ^ Parameters.referenceExponent i) ≤
      ((Parameters.retainedFraction i : ℚ) : ℝ) *
        (2 : ℝ) ^ (-((Parameters.certificateCost i - 1 +
          Parameters.referenceExponent i : ℕ) : ℝ)) := by
    simpa only [Parameters.referenceWidth, Nat.cast_pow, Nat.cast_ofNat] using hs.2
  have h2' : Parameters.certificateCost i - 1 - 1 ≤
      Dfamily (interlaceFun (fun r y => N (e r) y) 1)
        (bracketGE Ref Y 1 ((2 : ℝ) ^ (-(Parameters.tailDepth i : ℝ))) (3 / 10)) := by
    omega
  have hh := aligned_moderate_profiles N e hwidth (by omega)
    (ParameterGates.hard_seed_exponent_domains i).2.1
    (by positivity : 0 < (2 : ℝ) ^ (-(Parameters.tailDepth i : ℝ)))
    (by simpa only [Parameters.referenceWidth, Nat.cast_pow, Nat.cast_ofNat] using
      ParameterGates.reference_row_request i)
    hθ0 hθ1 hprop h1 h2' hgOne hgSeed (by omega)
    (ParameterGates.dense_tail_loss i).1
  dsimp only
  convert hh using 1 <;> omega

end EthInapproximability.CurrentPaper.AlignedProtectedProfiles
