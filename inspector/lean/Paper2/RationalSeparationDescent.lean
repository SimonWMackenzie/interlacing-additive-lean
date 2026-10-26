import Paper2.RationalSeparation
import Paper2.PrefixPullback

/-!
# Separation on the original rationally weighted inputs

Frozen v12 Appendix A, `cl:rational-laws` applied to `cl:separation`.
The retained row sets and retained full tuples are lifted by keeping every
duplicate. Their masses give the uniform theorem's actual ceiling bounds.
The supplied protocol is pulled back, the checked uniform separation theorem
is applied, and its live-prefix conclusion is reflected to that same original
protocol. No separation conclusion or protocol control is an extra premise.
The dominant blocks also descend: exact fibre masses identify the counted
duplicate rows with the original prefix rectangles. This yields the unique
dominant-block bijection and the manuscript's strict `0.998` probability.
-/

namespace Paper2.RationalSeparation

open scoped BigOperators
open Workspace.Types.CommComplexity Workspace.Types.Protocol

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- A full inverse image as an indexed finite set. -/
noncomputable def liftSet {A B : Type*} [Fintype A]
    (f : A → B) (S : Finset B) : Finset A := by
  classical
  exact Finset.univ.filter (fun a => f a ∈ S)

@[simp] theorem mem_liftSet {A B : Type*} [Fintype A]
    (f : A → B) (S : Finset B) (a : A) : a ∈ liftSet f S ↔ f a ∈ S := by
  classical
  simp [liftSet]

def forgetLift {A B : Type*} [Fintype A]
    (f : A → B) (S : Finset B) : {a // a ∈ liftSet f S} → {b // b ∈ S} :=
  fun a => ⟨f a.val, (mem_liftSet f S a.val).mp a.property⟩

theorem forgetLift_surjective {A B : Type*} [Fintype A]
    (f : A → B) (hf : Function.Surjective f) (S : Finset B) :
    Function.Surjective (forgetLift f S) := by
  rintro ⟨b, hb⟩
  obtain ⟨a, rfl⟩ := hf b
  exact ⟨⟨a, (mem_liftSet f S a).mpr hb⟩, rfl⟩

def blockForget (μ : PositiveRationalLaw X) (h : ℕ+) (q : ℕ) :
    Fin q × Rows μ h → Fin q × X := fun a => (a.1, rowForget μ h a.2)

theorem blockForget_surjective (μ : PositiveRationalLaw X) (h : ℕ+) (q : ℕ) :
    Function.Surjective (blockForget μ h q) := by
  rintro ⟨i, a⟩
  obtain ⟨z, rfl⟩ := rowForget_surjective μ h a
  exact ⟨(i, z), rfl⟩

/-- The enlarged uniform row law pushes to the original rational law. -/
theorem rows_prob_preimage (μ : PositiveRationalLaw X) (h : ℕ+) (E : X → Prop) :
    (FiniteLaw.uniform (Rows μ h)).prob (fun a => E (rowForget μ h a)) =
      μ.toFiniteLaw.prob E := by
  rw [← rows_uniform_eq]
  change ((FiniteLaw.uniformFin h h.pos).prod μ.uniformCopies).prob
    (fun a => E (μ.forget a.2)) = _
  rw [FiniteLaw.prod_snd_pushesTo (FiniteLaw.uniformFin h h.pos) μ.uniformCopies
    (fun a => E (μ.forget a)), μ.uniformCopies_prob_preimage]

theorem tuple_uniform_eq (ν : PositiveRationalLaw Y) (q : ℕ) :
    ν.uniformCopies.iid q = FiniteLaw.uniform (Fin q → ν.Copies) := by
  apply FiniteLaw.eq_of_weight_eq
  funext z
  simp only [PositiveRationalLaw.uniformCopies_iid_weight, FiniteLaw.uniform,
    Fintype.card_fun, Fintype.card_fin, ν.card_copies, Nat.cast_pow, inv_pow]

/-- All retained column tuples are lifted together; they need not form a
product set or satisfy any conditional independence property. -/
theorem tuples_prob_preimage (ν : PositiveRationalLaw Y) (q : ℕ)
    (E : (Fin q → Y) → Prop) :
    (FiniteLaw.uniform (Fin q → ν.Copies)).prob (fun z => E (ν.forgetTuple q z)) =
      (ν.toFiniteLaw.iid q).prob E := by
  rw [← tuple_uniform_eq, ν.uniformCopies_iid_prob_preimage]

theorem lifted_block_card (μ : PositiveRationalLaw X) (h : ℕ+) (q : ℕ)
    (R : Finset (Fin q × X)) (i : Fin q) :
    ((liftSet (blockForget μ h q) R).filter (fun a => a.1 = i)).card =
      (liftSet (rowForget μ h) (liftSet (fun a => (i, a)) R)).card := by
  classical
  have he : (liftSet (blockForget μ h q) R).filter (fun a => a.1 = i) =
      {i} ×ˢ liftSet (rowForget μ h) (liftSet (fun a => (i, a)) R) := by
    ext a
    simp only [Finset.mem_filter, mem_liftSet, Finset.mem_product,
      Finset.mem_singleton, blockForget]
    aesop
  rw [he, Finset.card_product, Finset.card_singleton, one_mul]

/-- Probability thresholds on the original retained sets are precisely
the cardinality thresholds required by uniform separation on their lifts. -/
theorem lifted_bracket (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (h : ℕ+) (q : ℕ) (x z : ℝ)
    (R : Finset (Fin q × X)) (C : Finset (Fin q → Y))
    (hR : ∀ i, x ≤ μ.toFiniteLaw.prob (fun a => (i, a) ∈ R))
    (hC : z ≤ (ν.toFiniteLaw.iid q).prob (· ∈ C)) :
    (liftSet (blockForget μ h q) R, liftSet (ν.forgetTuple q) C) ∈
      NPCC.bracketGE (Rows μ h) ν.Copies q x z := by
  classical
  constructor
  · intro i _
    rw [lifted_block_card]
    apply (FiniteLaw.le_uniform_prob_iff _ x).mp
    have hh := hR i
    rw [← rows_prob_preimage μ h (fun a => (i, a) ∈ R)] at hh
    simpa only [mem_liftSet, Finset.mem_filter, Finset.mem_univ, true_and] using hh
  · have hh := hC
    rw [← tuples_prob_preimage ν q (· ∈ C)] at hh
    have hh' : z ≤ (FiniteLaw.uniform (Fin q → ν.Copies)).prob
        (· ∈ liftSet (ν.forgetTuple q) C) := by simpa only [mem_liftSet] using hh
    have hc := (FiniteLaw.le_uniform_prob_iff _ z).mp hh'
    simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using hc

/-- Actual protocol control for rational input laws. The finite ceiling
guard is constructed by uniform duplication, rather than assumed. -/
theorem rational_separation_firstK
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y) (F : X → Y → Bool)
    (b : ℕ) (hb : 1 ≤ b) (hD : 2 ≤ D F)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw
      ((2 : ℝ) ^ (-(b : ℝ))) (D F : ℤ))
    (Q : ℕ) (hQ : 1 ≤ Q) (x z : ℝ) (hx1 : x ≤ 1)
    (hz : (18 / 25 : ℝ) ≤ z) (hz1 : z ≤ 1)
    (hsep : 2 * (2 ^ Q : ℝ) * (2 : ℝ) ^ (-(b : ℝ)) < x)
    (R : Finset (Fin (2 ^ Q) × X)) (C : Finset (Fin (2 ^ Q) → Y))
    (hR : ∀ i, x ≤ μ.toFiniteLaw.prob (fun a => (i, a) ∈ R))
    (hC : z ≤ (ν.toFiniteLaw.iid (2 ^ Q)).prob (· ∈ C))
    (P : Protocol {a // a ∈ R} {c // c ∈ C} Bool)
    (hPc : P.Computes (NPCC.subgame (fullInterlace F (2 ^ Q)) R C))
    (hcost : P.cost ≤ D F + Q) :
    NPCC.Protocol.FirstKRowBitsOn Finset.univ Finset.univ Q P := by
  classical
  obtain ⟨h, hDeq, hp, hg⟩ := exists_admissible_uniform_representation
    μ ν F b Q x hsep hprofile
  let R' := liftSet (blockForget μ h (2 ^ Q)) R
  let C' := liftSet (ν.forgetTuple (2 ^ Q)) C
  let f := forgetLift (blockForget μ h (2 ^ Q)) R
  let g := forgetLift (ν.forgetTuple (2 ^ Q)) C
  let P' := NPCC.Protocol.pullback f g P
  have hPc' : P'.Computes
      (NPCC.subgame (fullInterlace (matrix μ ν F h) (2 ^ Q)) R' C') := by
    intro a c
    change (NPCC.Protocol.pullback f g P).eval a c = _
    rw [NPCC.Protocol.pullback_eval]
    exact hPc (f a) (g c)
  have hcost' : P'.cost ≤ D (matrix μ ν F h) + Q := by
    simpa only [P', NPCC.Protocol.pullback_cost, hDeq] using hcost
  have hρ : 0 ≤ (2 ^ Q : ℝ) * (2 : ℝ) ^ (-(b : ℝ)) := by positivity
  have hs := ClassicalSeparation.classical_separation (matrix μ ν F h) b hb
    (by simpa only [hDeq] using hD) hp Q hQ x z (by nlinarith) hx1 hz hz1
    (by nlinarith) hg (R', C') (lifted_bracket μ ν h (2 ^ Q) x z R C hR hC)
    P' hPc' hcost'
  exact (PrefixPullback.firstKRowBitsOn_pullback_iff_of_surjective f g
    (forgetLift_surjective _ (blockForget_surjective μ h _) R)
    (forgetLift_surjective _ (ν.forgetTuple_surjective _) C) Q P).mp hs.1

/-- The row-prefix label of every retained duplicate is the original
row's label, not merely an arbitrary label with the same cardinality. -/
theorem prefixLabel_lift
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y) (h : ℕ+) (Q : ℕ)
    (R : Finset (Fin (2 ^ Q) × X)) (C : Finset (Fin (2 ^ Q) → Y))
    (P : Protocol {a // a ∈ R} {c // c ∈ C} Bool)
    (a : Fin (2 ^ Q) × Rows μ h) (ha : a ∈ liftSet (blockForget μ h (2 ^ Q)) R) :
    NPCC.Protocol.prefixLabelFinQ (liftSet (blockForget μ h (2 ^ Q)) R)
        (NPCC.Protocol.pullback (forgetLift (blockForget μ h (2 ^ Q)) R)
          (forgetLift (ν.forgetTuple (2 ^ Q)) C) P) a =
      NPCC.Protocol.prefixLabelFinQ R P (blockForget μ h (2 ^ Q) a) := by
  classical
  have ha' := (mem_liftSet _ _ _).mp ha
  simp only [NPCC.Protocol.prefixLabelFinQ, dif_pos ha, dif_pos ha',
    PrefixPullback.prefixCodeRaw_pullback]
  rfl

/-- Exact mass of a particular block in a particular prefix rectangle.
The right side uses original row probabilities; the left counts actual
retained duplicate rows. -/
theorem prefix_fibre_mass
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y) (h : ℕ+) (Q : ℕ)
    (R : Finset (Fin (2 ^ Q) × X)) (C : Finset (Fin (2 ^ Q) → Y))
    (P : Protocol {a // a ∈ R} {c // c ∈ C} Bool) (j i : Fin (2 ^ Q)) :
    let R' := liftSet (blockForget μ h (2 ^ Q)) R
    let P' := NPCC.Protocol.pullback (forgetLift (blockForget μ h (2 ^ Q)) R)
      (forgetLift (ν.forgetTuple (2 ^ Q)) C) P
    (((R'.filter (fun a => NPCC.Protocol.prefixLabelFinQ R' P' a = j ∧
        a.1 = i)).card : ℝ) / Fintype.card (Rows μ h)) =
      μ.toFiniteLaw.prob (fun a => (i, a) ∈ R ∧
        NPCC.Protocol.prefixLabelFinQ R P (i, a) = j) := by
  classical
  dsimp only
  let S := liftSet (fun a => (i, a))
    (R.filter (fun a => NPCC.Protocol.prefixLabelFinQ R P a = j))
  have he : (liftSet (blockForget μ h (2 ^ Q)) R).filter
      (fun a => NPCC.Protocol.prefixLabelFinQ (liftSet (blockForget μ h (2 ^ Q)) R)
          (NPCC.Protocol.pullback (forgetLift (blockForget μ h (2 ^ Q)) R)
            (forgetLift (ν.forgetTuple (2 ^ Q)) C) P) a = j ∧ a.1 = i) =
      {i} ×ˢ liftSet (rowForget μ h) S := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton]
    constructor
    · rintro ⟨ha, hl, hi⟩
      rw [prefixLabel_lift μ ν h Q R C P a ha] at hl
      have ha' := (mem_liftSet _ _ _).mp ha
      refine ⟨hi, ?_⟩
      simp only [mem_liftSet, S, Finset.mem_filter]
      simpa only [blockForget, hi] using And.intro ha' hl
    · rintro ⟨hi, ha⟩
      have ha' : (i, rowForget μ h a.2) ∈ R ∧
          NPCC.Protocol.prefixLabelFinQ R P (i, rowForget μ h a.2) = j := by
        simpa only [mem_liftSet, S, Finset.mem_filter] using ha
      have hm : a ∈ liftSet (blockForget μ h (2 ^ Q)) R := by
        simpa only [mem_liftSet, blockForget, hi] using ha'.1
      refine ⟨hm, ?_, hi⟩
      rw [prefixLabel_lift μ ν h Q R C P a hm]
      simpa only [blockForget, hi] using ha'.2
  rw [he, Finset.card_product, Finset.card_singleton, one_mul,
    ← FiniteLaw.uniform_prob_finset]
  have ht := rows_prob_preimage μ h (fun a => (i, a) ∈ R ∧
    NPCC.Protocol.prefixLabelFinQ R P (i, a) = j)
  simpa only [mem_liftSet, S, Finset.mem_filter] using ht

/-- The dominant-block bijection and its probability estimates on the
original input sets. Any target strictly below the stated limiting bound
is obtained by one actual finite duplication; no limit or independence
assumption on retained inputs is used in the proof.

In particular the manuscript's `x = 0.999`, `u*rho <= 0.0001` application
allows `target = 0.998`. The non-dominant bound is strictly `2*rho`, without
a residual ceiling term. -/
theorem rational_separation_dominant
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y) (F : X → Y → Bool)
    (b : ℕ) (hb : 1 ≤ b) (hD : 2 ≤ D F)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw
      ((2 : ℝ) ^ (-(b : ℝ))) (D F : ℤ))
    (Q : ℕ) (hQ : 1 ≤ Q) (x z target : ℝ) (hx1 : x ≤ 1)
    (hz : (18 / 25 : ℝ) ≤ z) (hz1 : z ≤ 1)
    (hsep : 2 * (2 ^ Q : ℝ) * (2 : ℝ) ^ (-(b : ℝ)) < x)
    (htarget : 2 * ((2 ^ Q - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-(b : ℝ)) < x - target)
    (R : Finset (Fin (2 ^ Q) × X)) (C : Finset (Fin (2 ^ Q) → Y))
    (hR : ∀ i, x ≤ μ.toFiniteLaw.prob (fun a => (i, a) ∈ R))
    (hC : z ≤ (ν.toFiniteLaw.iid (2 ^ Q)).prob (· ∈ C))
    (P : Protocol {a // a ∈ R} {c // c ∈ C} Bool)
    (hPc : P.Computes (NPCC.subgame (fullInterlace F (2 ^ Q)) R C))
    (hcost : P.cost ≤ D F + Q) :
    NPCC.Protocol.FirstKRowBitsOn Finset.univ Finset.univ Q P ∧
    ∃ dom : Fin (2 ^ Q) ≃ Fin (2 ^ Q), ∀ j,
      target < μ.toFiniteLaw.prob (fun a => (dom j, a) ∈ R ∧
        NPCC.Protocol.prefixLabelFinQ R P (dom j, a) = j) ∧
      (∀ i, i ≠ dom j → μ.toFiniteLaw.prob (fun a => (i, a) ∈ R ∧
        NPCC.Protocol.prefixLabelFinQ R P (i, a) = j) <
        2 * (2 : ℝ) ^ (-(b : ℝ))) ∧
      ∃ a ∈ R, NPCC.Protocol.prefixLabelFinQ R P a = j ∧ a.1 = dom j := by
  classical
  let ρ := (2 : ℝ) ^ (-(b : ℝ))
  have hρ : 0 ≤ ρ := by positivity
  obtain ⟨n, hn, hgap, hmargin⟩ := DuplicationMargins.exists_ceiling_and_dominant_margin
    (2 ^ Q) μ.denominator μ.denominator_pos ρ x target hρ
    (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hsep) htarget
  let h : ℕ+ := ⟨n, hn⟩
  let M := Fintype.card (Rows μ h)
  let A := ⌈(M : ℝ) * x⌉₊
  let B := ⌈2 * ρ * (M : ℝ)⌉₊
  have hM : 0 < (M : ℝ) := by exact_mod_cast Fintype.card_pos (α := Rows μ h)
  have hMcast : (M : ℝ) = n * μ.denominator := by
    simp only [M, row_card, h, PNat.mk_coe, Nat.cast_mul]
  have hg : 2 ^ Q * B < A := by
    simpa only [A, B, hMcast, mul_assoc, mul_comm x] using hgap
  have hm : target < ((A : ℝ) - (2 ^ Q - 1 : ℕ) * (B : ℝ)) / M := by
    simpa only [A, B, hMcast, mul_assoc, mul_comm x] using hmargin
  have hDeq := matrix_D_eq μ ν F h
  have hp : RestrictionProfile (matrix μ ν F h)
      (FiniteLaw.uniform (Rows μ h)) (FiniteLaw.uniform ν.Copies)
      ((2 : ℝ) ^ (-(b : ℝ))) (D (matrix μ ν F h) : ℤ) := by
    rw [hDeq]
    exact (matrix_profile_iff μ ν F h _ _).mpr hprofile
  have hpower : (2 : ℝ) ^ (1 - (b : ℝ)) = 2 * ρ := by
    rw [sub_eq_add_neg, Real.rpow_add (by norm_num), Real.rpow_one]
  let R' := liftSet (blockForget μ h (2 ^ Q)) R
  let C' := liftSet (ν.forgetTuple (2 ^ Q)) C
  let f := forgetLift (blockForget μ h (2 ^ Q)) R
  let g := forgetLift (ν.forgetTuple (2 ^ Q)) C
  let P' := NPCC.Protocol.pullback f g P
  have hPc' : P'.Computes
      (NPCC.subgame (fullInterlace (matrix μ ν F h) (2 ^ Q)) R' C') := by
    intro a c
    change (NPCC.Protocol.pullback f g P).eval a c = _
    rw [NPCC.Protocol.pullback_eval]
    exact hPc (f a) (g c)
  have hcost' : P'.cost ≤ D (matrix μ ν F h) + Q := by
    simpa only [P', NPCC.Protocol.pullback_cost, hDeq] using hcost
  have hρu : 0 ≤ (2 ^ Q : ℝ) * ρ := by positivity
  obtain ⟨hfirst, dom, hdom⟩ := ClassicalSeparation.classical_separation_with_bijection
    (matrix μ ν F h) b hb (by simpa only [hDeq] using hD) hp Q hQ x z
    (by change 2 * (2 ^ Q : ℝ) * ρ < x at hsep; nlinarith) hx1 hz hz1
    (by change 2 * (2 ^ Q : ℝ) * ρ < x at hsep; nlinarith)
    (by simpa only [hpower, B, A, M] using hg)
    (R', C') (lifted_bracket μ ν h (2 ^ Q) x z R C hR hC) P' hPc' hcost'
  refine ⟨(PrefixPullback.firstKRowBitsOn_pullback_iff_of_surjective f g
    (forgetLift_surjective _ (blockForget_surjective μ h _) R)
    (forgetLift_surjective _ (ν.forgetTuple_surjective _) C) Q P).mp hfirst, dom, ?_⟩
  intro j
  have hj := hdom j
  have hcount : A - (2 ^ Q - 1) * B ≤
      (R'.filter (fun a => NPCC.Protocol.prefixLabelFinQ R' P' a = j ∧
        a.1 = dom j)).card := by simpa only [hpower, A, B, M] using hj.1
  have hsub : (2 ^ Q - 1) * B ≤ A :=
    (Nat.mul_le_mul_right B (Nat.sub_le _ _)).trans hg.le
  have hcount' : (A : ℝ) - (2 ^ Q - 1 : ℕ) * (B : ℝ) ≤
      ((R'.filter (fun a => NPCC.Protocol.prefixLabelFinQ R' P' a = j ∧
        a.1 = dom j)).card : ℝ) := by
    exact_mod_cast (show (A - (2 ^ Q - 1) * B : ℕ) ≤ _ from hcount)
  refine ⟨?_, ?_, ?_⟩
  · rw [← prefix_fibre_mass μ ν h Q R C P j (dom j)]
    exact hm.trans_le (div_le_div_of_nonneg_right hcount' hM.le)
  · intro i hi
    have hc : (R'.filter (fun a => NPCC.Protocol.prefixLabelFinQ R' P' a = j ∧
        a.1 = i)).card < B := by simpa only [hpower, B, M] using hj.2.1 i hi
    have hreal : ((R'.filter (fun a => NPCC.Protocol.prefixLabelFinQ R' P' a = j ∧
        a.1 = i)).card : ℝ) < 2 * ρ * M := Nat.lt_ceil.mp hc
    rw [← prefix_fibre_mass μ ν h Q R C P j i]
    exact (div_lt_iff₀ hM).mpr hreal
  · obtain ⟨a, ha⟩ := hj.2.2.1
    have ham := (Finset.mem_filter.mp ha).1
    have hal := (Finset.mem_filter.mp ha).2
    refine ⟨blockForget μ h (2 ^ Q) a, (mem_liftSet _ _ _).mp ham, ?_, hal.2⟩
    rw [← prefixLabel_lift μ ν h Q R C P a ham]
    exact hal.1

/-- A block is the unique dominant block precisely when its retained
prefix probability is at least `2*rho`. In particular dominance is not
an arbitrary assignment of one outer block to each prefix label. -/
theorem rational_separation_unique_dominant
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y) (F : X → Y → Bool)
    (b : ℕ) (hb : 1 ≤ b) (hD : 2 ≤ D F)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw
      ((2 : ℝ) ^ (-(b : ℝ))) (D F : ℤ))
    (Q : ℕ) (hQ : 1 ≤ Q) (x z : ℝ) (hx1 : x ≤ 1)
    (hz : (18 / 25 : ℝ) ≤ z) (hz1 : z ≤ 1)
    (hsep : 2 * (2 ^ Q : ℝ) * (2 : ℝ) ^ (-(b : ℝ)) < x)
    (R : Finset (Fin (2 ^ Q) × X)) (C : Finset (Fin (2 ^ Q) → Y))
    (hR : ∀ i, x ≤ μ.toFiniteLaw.prob (fun a => (i, a) ∈ R))
    (hC : z ≤ (ν.toFiniteLaw.iid (2 ^ Q)).prob (· ∈ C))
    (P : Protocol {a // a ∈ R} {c // c ∈ C} Bool)
    (hPc : P.Computes (NPCC.subgame (fullInterlace F (2 ^ Q)) R C))
    (hcost : P.cost ≤ D F + Q) :
    NPCC.Protocol.FirstKRowBitsOn Finset.univ Finset.univ Q P ∧
    ∃ dom : Fin (2 ^ Q) ≃ Fin (2 ^ Q), ∀ j,
      (∀ i, 2 * (2 : ℝ) ^ (-(b : ℝ)) ≤
        μ.toFiniteLaw.prob (fun a => (i, a) ∈ R ∧
          NPCC.Protocol.prefixLabelFinQ R P (i, a) = j) ↔ i = dom j) ∧
      ∃ a ∈ R, NPCC.Protocol.prefixLabelFinQ R P a = j ∧ a.1 = dom j := by
  have hu : 1 ≤ 2 ^ Q := Nat.one_le_pow Q 2 (by norm_num)
  have hcast : ((2 ^ Q - 1 : ℕ) : ℝ) = (2 ^ Q : ℝ) - 1 := by
    rw [Nat.cast_sub hu, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  have ht : 2 * ((2 ^ Q - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-(b : ℝ)) <
      x - 2 * (2 : ℝ) ^ (-(b : ℝ)) := by rw [hcast]; nlinarith
  obtain ⟨hfirst, dom, hd⟩ := rational_separation_dominant μ ν F b hb hD hprofile
    Q hQ x z (2 * (2 : ℝ) ^ (-(b : ℝ))) hx1 hz hz1 hsep ht R C hR hC P hPc hcost
  refine ⟨hfirst, dom, fun j => ⟨?_, (hd j).2.2⟩⟩
  intro i
  constructor
  · intro hi
    by_contra hne
    exact (not_le_of_gt ((hd j).2.1 i hne)) hi
  · rintro rfl
    exact (hd j).1.le

/-- The strict `0.998` dominant-block probability asserted in the final
paragraph of `cl:rational-laws`, now for the original rationally weighted
restriction and its actual protocol, rather than only its duplicates. -/
theorem rational_separation_manuscript
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y) (F : X → Y → Bool)
    (b : ℕ) (hb : 1 ≤ b) (hD : 2 ≤ D F)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw
      ((2 : ℝ) ^ (-(b : ℝ))) (D F : ℤ))
    (Q : ℕ) (hQ : 1 ≤ Q) (z : ℝ) (hz : (18 / 25 : ℝ) ≤ z) (hz1 : z ≤ 1)
    (hsmall : (2 ^ Q : ℝ) * (2 : ℝ) ^ (-(b : ℝ)) ≤ 1 / 10000)
    (R : Finset (Fin (2 ^ Q) × X)) (C : Finset (Fin (2 ^ Q) → Y))
    (hR : ∀ i, (999 / 1000 : ℝ) ≤ μ.toFiniteLaw.prob (fun a => (i, a) ∈ R))
    (hC : z ≤ (ν.toFiniteLaw.iid (2 ^ Q)).prob (· ∈ C))
    (P : Protocol {a // a ∈ R} {c // c ∈ C} Bool)
    (hPc : P.Computes (NPCC.subgame (fullInterlace F (2 ^ Q)) R C))
    (hcost : P.cost ≤ D F + Q) :
    NPCC.Protocol.FirstKRowBitsOn Finset.univ Finset.univ Q P ∧
    ∃ dom : Fin (2 ^ Q) ≃ Fin (2 ^ Q), ∀ j,
      (998 / 1000 : ℝ) < μ.toFiniteLaw.prob (fun a => (dom j, a) ∈ R ∧
        NPCC.Protocol.prefixLabelFinQ R P (dom j, a) = j) ∧
      (∀ i, i ≠ dom j → μ.toFiniteLaw.prob (fun a => (i, a) ∈ R ∧
        NPCC.Protocol.prefixLabelFinQ R P (i, a) = j) <
        2 * (2 : ℝ) ^ (-(b : ℝ))) ∧
      ∃ a ∈ R, NPCC.Protocol.prefixLabelFinQ R P a = j ∧ a.1 = dom j := by
  apply rational_separation_dominant μ ν F b hb hD hprofile Q hQ
    (999 / 1000) z (998 / 1000) (by norm_num) hz hz1
    (by nlinarith) ?_ R C hR hC P hPc hcost
  have hρ : 0 ≤ (2 : ℝ) ^ (-(b : ℝ)) := by positivity
  have hu : ((2 ^ Q - 1 : ℕ) : ℝ) ≤ (2 ^ Q : ℝ) := by
    exact_mod_cast Nat.sub_le (2 ^ Q) 1
  have hm := mul_le_mul_of_nonneg_right hu hρ
  nlinarith

end Paper2.RationalSeparation

#print axioms Paper2.RationalSeparation.rational_separation_firstK
#print axioms Paper2.RationalSeparation.rational_separation_dominant
#print axioms Paper2.RationalSeparation.rational_separation_unique_dominant
#print axioms Paper2.RationalSeparation.rational_separation_manuscript
