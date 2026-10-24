import Paper2.RationalRowEstimates
import Paper2.StrongSeedSelection
import Paper2.RestorationCoverParameters
import Paper2.ProjectionCover
import CurrentAdditive.DeterministicIndexedMatrix
import CurrentAdditive.ConditioningGeneralCore
import CurrentAdditive.DeterministicPairHighMoment
import CurrentAdditive.IndexedFlagMoment256
import CurrentAdditive.ExactPairTail
import CurrentAdditive.DeterministicExactPairEightWise
import CurrentAdditive.QuarticTVAdapter
import CurrentAdditive.DeterministicPairCrossAdapter
import Paper2.InterlaceRank
import Paper2.RestorationBridgeRational
import Paper2.SourceProtocolPrefix

/-! Private v35 finite readback. These declarations keep the original
retained-input carriers and laws visible. -/

namespace FiniteV35

open Paper2

section ExactTuples

/-- v35 `def:exact-tuples` as indexed positive-rational source data.
`CodeSource` stores distinct labels even when `decode` has collisions;
`exactLaw` is equality of every decoded marginal law through order `D`. -/
structure ExactTupleList (D q : ℕ) (Y : Type*) [Fintype Y]
    [DecidableEq Y] (μ : PositiveRationalLaw Y) where
  degree_pos : 1 ≤ D
  width_pos : 1 ≤ q
  source : CurrentAdditive.DeterministicIndexedMatrix.CodeSource D q Y μ

noncomputable def ExactTupleList.rowLaw
    {D q : ℕ} {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq Y] (μX : PositiveRationalLaw X)
    {μY : PositiveRationalLaw Y}
    (L : ExactTupleList D q Y μY) :
    PositiveRationalLaw (Fin q × X) := by
  have hq : q ≠ 0 := by have := L.width_pos; omega
  haveI : NeZero q := ⟨hq⟩
  exact (PositiveRationalLaw.uniform (Fin q)).prod μX

def ExactTupleList.entries
    {D q : ℕ} {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq Y] {μY : PositiveRationalLaw Y}
    (L : ExactTupleList D q Y μY) (M : X → Y → Bool) :
    (Fin q × X) → L.source.Label → Bool :=
  Paper2.indexedInterlace M L.source.decode

theorem ExactTupleList.entries_apply
    {D q : ℕ} {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq Y] {μY : PositiveRationalLaw Y}
    (L : ExactTupleList D q Y μY) (M : X → Y → Bool)
    (r : Fin q × X) (label : L.source.Label) :
    L.entries M r label = M r.2 (L.source.decode label r.1) := rfl

end ExactTuples

section Blocks

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- v35 `lem:product-blocks`, dyadic width at least four. The set `Q`
lists actual retained blocks; the columns are measured in the original
positive rational product law. -/
theorem product_blocks_power (μ : PositiveRationalLaw X)
    (ν : PositiveRationalLaw Y) (F : X → Y → Bool)
    (H l p : ℕ) {x : ℝ} (hH : 2 ≤ H) (hx : 0 < x)
    (hl : 2 ≤ l) (hscale : (2 : ℝ)^l * x ≤ 1)
    (hp : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (Q : Finset (Fin p)) (hQ : 2^(l-1)+1 ≤ Q.card)
    (R : Finset (Fin p × X)) (C : Finset (Fin p → Y))
    (hr : ∀ i ∈ Q, (2 : ℝ)^l*x ≤
      μ.toFiniteLaw.prob (fun a => (i,a) ∈ R))
    (hc : (9/25 : ℝ) ≤ (ν.toFiniteLaw.iid p).prob (· ∈ C)) :
    H+l ≤ Workspace.Types.CommComplexity.D
      (NPCC.subgame
        (Paper2.fullInterlace F p) R C) := by
  exact Paper2.RationalRowEstimates.small_capacity_power μ ν F H l p
    hH hx hl hscale hp Q hQ R C hr hc

/-- The `u=2` clause requires two distinct retained blocks. -/
theorem product_blocks_two (μ : PositiveRationalLaw X)
    (ν : PositiveRationalLaw Y) (F : X → Y → Bool)
    (H p : ℕ) {x : ℝ} (hH : 2 ≤ H) (hx : 0 < x)
    (hscale : 2*x ≤ 1)
    (hp : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (Q : Finset (Fin p)) (hQ : 2 ≤ Q.card)
    (R : Finset (Fin p × X)) (C : Finset (Fin p → Y))
    (hr : ∀ i ∈ Q, 2*x ≤ μ.toFiniteLaw.prob (fun a => (i,a) ∈ R))
    (hc : (9/25 : ℝ) ≤ (ν.toFiniteLaw.iid p).prob (· ∈ C)) :
    H+1 ≤ Workspace.Types.CommComplexity.D
      (NPCC.subgame
        (Paper2.fullInterlace F p) R C) := by
  exact Paper2.RationalRowEstimates.small_capacity_two μ ν F H p
    hH hx hscale hp Q hQ R C hr hc

/-- v35 `lem:many-product-blocks`, expressed with an explicit selection
of `9u/16` original blocks. Its column event is the retained original
full-product event, rather than an assumed product law after restriction. -/
theorem many_product_blocks (μ : PositiveRationalLaw X)
    (ν : PositiveRationalLaw Y) (F : X → Y → Bool)
    (H a : ℕ) (hH : 3 ≤ H) (ha : 4 ≤ a)
    (x : ℝ) (hx : 0 < x) (hscale : (2 : ℝ)^a*x ≤ 1)
    (hp : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (q : ℕ) (e : Fin (Paper2.StrongSeed.copies a) → Fin q)
    (he : Function.Injective e)
    (R : Finset (Fin q × X)) (K : Finset (Fin q → Y))
    (hr : ∀ i, (2 : ℝ)^a*x ≤
      μ.toFiniteLaw.prob (fun z => (e i,z) ∈ R))
    (hc : (2 : ℝ)^(-((2 : ℝ)^a/1024)) ≤
      (ν.toFiniteLaw.iid q).prob (· ∈ K)) :
    H+a ≤ Workspace.Types.CommComplexity.D
      (NPCC.subgame
        (Paper2.fullInterlace F q) R K) := by
  exact Paper2.StrongSeedSelection.selected_member μ ν F H a hH ha
    x hx hscale hp q e he R K hr hc

end Blocks

section Restoration

variable {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]

/-- v35 `lem:full-restoration` for a dyadic `Q=2^r` and the public
`ρ=2^(-b)` schedule. The YES upper protocol is a separate implication and
does not consume the lower-bound hypotheses. -/
theorem full_restoration
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (W : X → Y → Bool) (r b : ℕ) (θ δ : ℝ)
    (hC : 3 ≤ Workspace.Types.CommComplexity.D W)
    (hb : 1 ≤ b) (hθ : 0 < θ) (hδ : 0 < δ)
    (hδsmall : δ ≤ 1/64)
    (hQ : 80*(b : ℝ) ≤ (2 : ℝ)^r*δ)
    (hscale : (2 : ℝ)^r*θ < 1/20)
    (hnear : RestrictionLowerBound W μ.toFiniteLaw ν.toFiniteLaw
      θ (1-δ) (Workspace.Types.CommComplexity.D W : ℤ))
    (hprofile : RestrictionProfile W μ.toFiniteLaw ν.toFiniteLaw
      θ ((Workspace.Types.CommComplexity.D W : ℤ)-1)) :
    Workspace.Types.CommComplexity.D
      (Paper2.RestorationBridge.restored W r) =
        Workspace.Types.CommComplexity.D W+r ∧
    RestrictionProfile (Paper2.RestorationBridge.restored W r)
      (ν.toFiniteLaw.iid (2^r))
      ((FiniteLaw.uniformFin (2^r) (Nat.two_pow_pos r)).prod μ.toFiniteLaw)
      ((2 : ℝ)^(-(b : ℝ)))
      ((Workspace.Types.CommComplexity.D W+r : ℕ) : ℤ) := by
  exact Paper2.RestorationBridge.rational_restoration μ ν W r b θ δ
    hC hb hθ hδ hδsmall hQ hscale hnear hprofile

/-- The v35 upper implication uses only an upper protocol for the same W. -/
theorem full_restoration_upper
    (W : X → Y → Bool) (r y : ℕ)
    (hy : Workspace.Types.CommComplexity.D W ≤ y) :
    Workspace.Types.CommComplexity.D
      (Paper2.RestorationBridge.restored W r) ≤ y+r :=
  Paper2.RestorationBridge.upper W r y hy

end Restoration

section Template

open Paper2.SourceMatrix Paper2.SourceProtocolPrefix Paper2.SourceProtocolPrefixTree
open Workspace.Types.Protocol Workspace.Types.CommComplexity

/-- v35 `lem:template-prefix` for the actual restricted source matrix.
The source profile and public numerical guard are exposed as separate
premises; the conclusion concerns every protocol of the stated depth. -/
theorem template_prefix
    {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
    {q₁ q₂ a : ℕ} [NeZero q₁] [NeZero q₂]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (F : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin (2^a)))
    (ξ₀ : Tail (2^a) Y) (b : ℕ) (hb : 1 ≤ b) (ha : 1 ≤ a)
    (hD : 2 ≤ D (T (q₁ := q₁) (q₂ := q₂) (s := 2^a) F))
    (hprofile : RestrictionProfile (T F)
      (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw
      (SourceLaws.outerLaw ν q₁ q₂ (2^a)).toFiniteLaw
      ((2 : ℝ)^(-(b : ℝ)))
      (D (T (q₁ := q₁) (q₂ := q₂) (s := 2^a) F) : ℤ))
    (hsmall : (2^a : ℝ)*(2 : ℝ)^(-(b : ℝ)) ≤ 1/10000)
    (W : Set (RawRow q₁ q₂ (2^a) X I))
    (U : Set (TaggedColumn q₁ q₂ (2^a) Y))
    (hW : ∀ i, (999/1000 : ℝ) ≤
      (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw.prob
        (fun t => Sum.inl (i,t) ∈ W))
    (hU : (99/100 : ℝ) ≤
      (SourceLaws.fixedTailLaw ν q₁ q₂ (2^a)).toFiniteLaw.prob
        (fun z => TaggedColumn.fixedTail z ∈ U))
    (P : Protocol W U Bool)
    (hP : P.Computes (fun w z => N F activity ξ₀ z.val w.val))
    (hcost : P.cost ≤ D (T (q₁ := q₁) (q₂ := q₂) (s := 2^a) F)+a) :
    CompleteAlicePrefix a P ∧
    ∃ dom : Fin (2^a) ≃ Fin (2^a), ∀ j,
      (998/1000 : ℝ) <
        (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw.prob
          (fun t => Sum.inl (dom j,t) ∈ W ∧
            rowCode W P a (Sum.inl (dom j,t)) = j) := by
  obtain ⟨hprefix, _, dom, hdom⟩ :=
    raw_common_assignment μ ν F activity ξ₀ b hb ha hD hprofile
      hsmall W U hW hU P hP hcost
  exact ⟨hprefix, dom, fun j => (hdom j).1⟩

end Template

section Covers

open Paper2.ProductProjections Paper2.RestorationCoverParameters

def manySize (Q : ℕ) : ℕ := tStar Q / 4 + 1

noncomputable def ownerBudget (Q : ℕ) (η : ℝ) : ℕ :=
  (B1 Q η - 1) + manySize Q * (B2 Q - 1)

noncomputable def destinationBudget (Q : ℕ) (η : ℝ) : ℕ :=
  Nat.ceil ((16 * (ownerBudget Q η : ℝ)) / 7)

/-- The source's `θ/2 ≥ 2^(-t_*/1024)` numerical guard for its public
power-of-two choice of `t_*`. -/
theorem theta_half_ge_star {Q : ℕ} (hQ : 0 < Q) :
    (2 : ℝ)^(-((tStar Q : ℝ)/1024)) ≤ theta Q/2 := by
  have hmin : 1024*(b Q+1) ≤ tStar Q :=
    SourcePadding.le_powTwoCeil _
  have hminR : (b Q+1 : ℝ) ≤ (tStar Q : ℝ)/1024 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 1024)).2
    have hreal : (1024 : ℝ)*(b Q+1) ≤ (tStar Q : ℝ) := by
      exact_mod_cast hmin
    simpa only [mul_comm] using hreal
  calc
    (2 : ℝ)^(-((tStar Q : ℝ)/1024)) ≤
        (2 : ℝ)^(-(b Q+1 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = ((1/2 : ℝ)^b Q)/2 := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      have he : (b Q : ℝ)+1 = ((b Q+1 : ℕ) : ℝ) := by push_cast; ring
      rw [he, Real.rpow_natCast]
      rw [pow_succ]
      rw [mul_inv_rev, ← inv_pow]
      norm_num
      ring
    _ ≤ theta Q/2 := by
      exact div_le_div_of_nonneg_right (two_neg_b_le_theta hQ) (by norm_num)

/-- `E_exc = ceil(16 e₀/7)` absorbs a deficit of at least `7/16` from
each nonowner destination. -/
theorem nonowner_count_le_destinationBudget
    (Q : ℕ) (η : ℝ) (n : ℕ)
    (hdeficit : (7/16 : ℝ)*(n : ℝ) ≤ ownerBudget Q η) :
    n ≤ destinationBudget Q η := by
  have hreal : (n : ℝ) ≤
      (16*(ownerBudget Q η : ℝ))/7 := by linarith
  have hceil := Nat.le_ceil ((16*(ownerBudget Q η : ℝ))/7)
  have hcast : (n : ℝ) ≤ (destinationBudget Q η : ℝ) := by
    exact hreal.trans (by simpa only [destinationBudget] using hceil)
  exact_mod_cast hcast

/-- The maximal disjoint-family argument for poor projections of *any*
positive size up to `u`. This is the form needed by the selected v35 source. -/
theorem projection_cover_upto {ι K : Type*} [Fintype ι] [DecidableEq ι] [Fintype K]
    (μ : ι → FiniteLaw K) (Z : (ι → K) → Prop)
    (u B : ℕ) (hB : 1 ≤ B) (θ ρ : ℝ)
    (hθpos : 0 < θ) (hρ1 : ρ < 1)
    (hθ : θ ≤ (FiniteLaw.pi μ).prob Z) (hgap : ρ^B < θ) :
    ∃ C : Finset ι, C.card ≤ u*(B-1) ∧
      ∀ S : Finset ι, S.card ≤ u → Disjoint S C →
        ρ ≤ projectionMass μ Z S := by
  classical
  have hZ : ∃ z, Z z := by
    by_contra hn
    have hnone : ∀ z, ¬ Z z := not_exists.mp hn
    have hzero : (FiniteLaw.pi μ).prob Z = 0 := by
      simp [FiniteLaw.prob, hnone]
    linarith
  let P : Finset (Finset ι) := Finset.univ.filter
    (fun S => S.card ≤ u ∧ projectionMass μ Z S < ρ)
  have hmem (S : Finset ι) : S ∈ P ↔
      S.card ≤ u ∧ projectionMass μ Z S < ρ := by simp [P]
  have hne : ∀ S ∈ P, S.Nonempty := by
    intro S hS
    by_contra hn
    have heq : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hpoor := ((hmem S).mp hS).2
    rw [heq, projectionMass_empty_of_nonempty μ Z hZ] at hpoor
    linarith
  have hno : ∀ Q : Finset (Finset ι), Q ⊆ P →
      (Q : Set (Finset ι)).Pairwise Disjoint → Q.card ≠ B := by
    intro Q hQP hdisj hQB
    have hprod : (∏ S ∈ Q, projectionMass μ Z S) ≤ ρ^B := by
      calc
        (∏ S ∈ Q, projectionMass μ Z S) ≤ ∏ _S ∈ Q, ρ := by
          apply Finset.prod_le_prod
          · intro S _
            exact projectionMass_nonneg μ Z S
          · intro S hS
            exact ((hmem S).mp (hQP hS)).2.le
        _ = ρ^B := by simp [hQB]
    have hprojection := prob_le_prod_projectionMass μ Z Q hdisj
    linarith
  obtain ⟨Q, hQP, hdisj, hcover⟩ := exists_maximal_disjoint_cover P hne
  have hQB : Q.card ≤ B-1 := by
    by_contra hn
    have hlarge : B ≤ Q.card := by omega
    obtain ⟨Q', hQ'Q, hQ'card⟩ := Finset.exists_subset_card_eq hlarge
    exact hno Q' (hQ'Q.trans hQP) (hdisj.mono hQ'Q) hQ'card
  have hQsize : ∀ S ∈ Q, S.card ≤ u := by
    intro S hS
    exact ((hmem S).mp (hQP hS)).1
  refine ⟨Q.biUnion id, ?_, ?_⟩
  · calc
      (Q.biUnion id).card ≤ ∑ S ∈ Q, S.card := Finset.card_biUnion_le
      _ ≤ ∑ _S ∈ Q, u := by
        apply Finset.sum_le_sum
        intro S hS
        exact hQsize S hS
      _ = Q.card*u := by simp
      _ ≤ (B-1)*u := Nat.mul_le_mul_right u hQB
      _ = u*(B-1) := Nat.mul_comm _ _
  · intro S hsize hdisj
    by_contra hn
    have hpoor : projectionMass μ Z S < ρ := lt_of_not_ge hn
    exact (hcover S ((hmem S).mpr ⟨hsize, hpoor⟩)) hdisj

/-- v35 `lem:owner-projections`: one exceptional set protects singleton
and every set of at most `m_*` coordinates, under the original iid law. -/
theorem owner_projections {K : Type*} [Fintype K]
    (κ : FiniteLaw K) (w Q : ℕ) (hQ : 0 < Q)
    (η : ℝ) (hη : 0 < η) (hη1 : η < 1)
    (Y' : Set (Fin w → K))
    (hY : theta Q ≤ (κ.iid w).prob (· ∈ Y')) :
    ∃ E : Finset (Fin w), E.card ≤ ownerBudget Q η ∧
      (∀ S : Finset (Fin w), S.card = 1 → Disjoint S E →
        1-η ≤ projectionMass (fun _ => κ) (· ∈ Y') S) ∧
      (∀ S : Finset (Fin w), S.card ≤ manySize Q →
        Disjoint S E →
        (99/100 : ℝ) ≤ projectionMass (fun _ => κ) (· ∈ Y') S) := by
  classical
  have hpi : theta Q ≤ (FiniteLaw.pi (fun _ : Fin w => κ)).prob (· ∈ Y') := hY
  obtain ⟨E1, hE1, hcover1⟩ := projection_cover
    (fun _ : Fin w => κ) (· ∈ Y') 1 (B1 Q η) (B1_pos Q hη)
    (theta Q) (1-η) hpi (B1_gap hQ hη hη1)
  obtain ⟨Em, hEm, hcoverm⟩ := projection_cover_upto
    (fun _ : Fin w => κ) (· ∈ Y') (manySize Q) (B2 Q) (B2_pos Q)
    (theta Q) (99/100) (theta_pos hQ) (by norm_num)
    hpi (B2_gap hQ)
  refine ⟨E1 ∪ Em, ?_, ?_, ?_⟩
  · calc
      (E1 ∪ Em).card ≤ E1.card + Em.card := Finset.card_union_le _ _
      _ ≤ ownerBudget Q η := by simp only [ownerBudget]; omega
  · intro S hS hdisj
    have hd : Disjoint S E1 := by
      apply Finset.disjoint_left.mpr
      intro x hxS hxE1
      exact (Finset.disjoint_left.mp hdisj) hxS
        (Finset.mem_union.mpr (Or.inl hxE1))
    by_contra hbad
    have hpoor : projectionMass (fun _ => κ) (· ∈ Y') S < 1-η := lt_of_not_ge hbad
    exact (hcover1 S hS hpoor) hd
  · intro S hS hdisj
    have hd : Disjoint S Em := by
      apply Finset.disjoint_left.mpr
      intro x hxS hxEm
      exact (Finset.disjoint_left.mp hdisj) hxS
        (Finset.mem_union.mpr (Or.inr hxEm))
    exact hcoverm S hS hd

end Covers

section Moments

open CurrentAdditive

/-- v35 `lem:conditioning-moment` at both displayed orders. The source
Boolean tests need only joint laws through order 1024; full independence of
the original label law is not assumed. -/
theorem conditioning_moment_both {Ω : Type*} [Fintype Ω]
    (ν : FiniteLaw Ω) (m : ℕ) (F : Fin m → Ω → Bool)
    (hjoint : IndicatorJointAgreement ν F 1024) :
    expectation ν (fun ω =>
      |∑ i : Fin m, ((if F i ω then (1 : ℝ) else 0) -
        ν.prob (fun ω' => F i ω'))|^1024) ≤
        2*((1024 : ℝ)*m/4)^512 ∧
    expectation ν (fun ω =>
      |∑ i : Fin m, ((if F i ω then (1 : ℝ) else 0) -
        ν.prob (fun ω' => F i ω'))|^256) ≤
        2*((256 : ℝ)*m/4)^128 := by
  have h256 : IndicatorJointAgreement ν F 256 := by
    intro S hS E
    exact hjoint S (by omega) E
  constructor
  · rw [centered_indicator_even_moment_eq_proxy ν F 1024
      (by norm_num) hjoint]
    simpa only [CurrentAdditive.EvenMoment.ex, expectation] using
      CurrentAdditive.EvenMoment.iid_centered_indicator_moment_1024 ν m F
  · rw [centered_indicator_even_moment_eq_proxy ν F 256
      (by norm_num) h256]
    simpa only [CurrentAdditive.EvenMoment.ex, expectation,
      show ((256 : ℝ)*m)/4 = 64*m by ring] using
      CurrentAdditive.EvenMoment.iid_centered_indicator_moment_256 ν m F

/-- Both v35 moments for disjoint original coordinate events of size at most
eight in an exactly 8192-wise indexed tuple list. Conditioning is absent. -/
theorem conditioning_moment_disjoint_source
    {Ω A : Type*} [Fintype Ω] [Fintype A]
    (ν : FiniteLaw Ω) (μ : FiniteLaw A)
    {q m : ℕ} (decode : Ω → Fin q → A)
    (hwise : IsDWise 8192 ν decode μ)
    (blocks : Fin m → Finset (Fin q))
    (hsize : ∀ i, (blocks i).card ≤ 8)
    (hdisj : Pairwise (fun i j => Disjoint (blocks i) (blocks j)))
    (H : ∀ i : Fin m, (blocks i → A) → Bool) :
    let F : Fin m → Ω → Bool :=
      fun i ω => H i (fun j => decode ω j)
    expectation ν (fun ω =>
      |∑ i : Fin m, ((if F i ω then (1 : ℝ) else 0) -
        ν.prob (fun ω' => F i ω'))|^1024) ≤
        2*((1024 : ℝ)*m/4)^512 ∧
    expectation ν (fun ω =>
      |∑ i : Fin m, ((if F i ω then (1 : ℝ) else 0) -
        ν.prob (fun ω' => F i ω'))|^256) ≤
        2*((256 : ℝ)*m/4)^128 := by
  let F : Fin m → Ω → Bool :=
    fun i ω => H i (fun j => decode ω j)
  have hjoint : IndicatorJointAgreement ν F 1024 := by
    intro S hs E
    exact disjoint_blocks_indicator_joint_agreement ν μ decode
      (by simpa only [show 8*1024 = 8192 by norm_num] using hwise)
      blocks hsize hdisj H S hs E
  exact conditioning_moment_both ν m F hjoint

end Moments

section Pairs

open CurrentAdditive CurrentAdditive.SuffixLong

/-- The first displayed bound of v35 `lem:pair-projections` for an actual
indexed, eight-wise source. The set `K` is an event of labels; pair images
therefore have actual retained representatives, even with duplicate words. -/
theorem pair_projections_eight
    {S Z : Type*} [Fintype S] [Fintype Z]
    (source : FiniteLaw S) (μ : FiniteLaw Z)
    {m q : ℕ} (hm : 8 ≤ m) (decode : S → Fin q → Z)
    (hwise : IsDWise 8 source decode μ)
    (e : Fin (2*m) → Fin q) (he : Function.Injective e)
    (K : Set S)
    (hsmall : ∀ i : Fin m,
      (μ.iid 2).prob (· ∈ pairImage decode e K i) < 9/25) :
    source.prob (· ∈ K) ≤
      ((m : ℝ)/4 + 3*(m : ℝ)^2/16) /
        ((16/25 : ℝ)^4*(m : ℝ)^4) ∧
    source.prob (· ∈ K) < 9/(50*(m : ℝ)) := by
  classical
  let F : Fin m → S → Bool := fun i s => pairHit decode e K i (decode s)
  let β : Fin m → FiniteLaw Bool :=
    fun i => boolImageLaw (μ.iid q) (pairHit decode e K i)
  have hβ : ∀ i, (β i).prob (fun b => b = true) < 9/25 := by
    intro i
    have hmass := pairHit_ambient_mass μ decode e he K i
    simpa only [β, boolImageLaw, FiniteLaw.prob_singleton, hmass] using hsmall i
  have hK : ∀ s, s ∈ K → ∀ i, F i s = true := by
    intro s hs i
    exact pairHit_of_retained decode e K i s hs
  have hjoint : ∀ (s : Finset (Fin m)), s.card ≤ 4 →
      ∀ E : (s → Bool) → Prop,
        source.prob (fun ω => E (fun j : s => F j.val ω)) =
          (FiniteLaw.pi (fun j : s => β j.val)).prob E := by
    intro s hs E
    exact pairHit_source_four_wise_of_eight source μ decode hwise
      e he K s hs E
  exact CurrentAdditive.FourthMoment.exact_pair_tail_of_four_wise
    source F β (· ∈ K) hm hβ hK hjoint

/-- The first conditional estimate of v35 `lem:pair-projections`. The TV
premise is the conclusion of the selected exceptional-coordinate theorem,
and `hgood` says the chosen pairs avoid that very exceptional set. -/
theorem pair_projections_conditional_fourth
    {S Z : Type*} [Fintype S] [Fintype Z]
    (source : FiniteLaw S) (μ : FiniteLaw Z)
    {m q : ℕ} (hm : 0 < m) (decode : S → Fin q → Z)
    (e : Fin (2*m) → Fin q) (he : Function.Injective e)
    (Y K : Set S) (hK : K ⊆ Y)
    (hY : 0 < source.prob (· ∈ Y))
    (E : Finset (Fin q)) (ε : ℝ)
    (hgood : ∀ t : Fin (2*m), e t ∉ E)
    (hTV : ∀ J : Finset (Fin q),
      J ⊆ Finset.univ \ E → J.card ≤ 8 →
        projectionTV (condition source (· ∈ Y) hY) μ decode J ≤ ε)
    (hsmall : ∀ i : Fin m,
      (μ.iid 2).prob (· ∈ pairImage decode e K i) < 9/25) :
    source.prob (· ∈ K) / source.prob (· ∈ Y) ≤
      ((m : ℝ)/4 + 3*(m : ℝ)^2/16) /
        ((16/25 : ℝ)^4*(m : ℝ)^4) + 2*ε/(16/25 : ℝ)^4 := by
  classical
  let p : Fin m → ℝ := pairBaseMass μ decode e K
  have hp : ∀ i, p i = (μ.iid q).prob
      (fun c => pairHit decode e K i c) := by intro i; rfl
  have hpoint : ∀ s, s ∈ K → s ∈ Y ∧
      ∀ i, pairHit decode e K i (decode s) = true := by
    intro s hs
    exact ⟨hK hs, fun i => pairHit_of_retained decode e K i s hs⟩
  have hterms := quartic_terms_of_condition_good_projection source μ
    decode e K Y hY E ε hgood hTV
  exact CurrentAdditive.FourthMoment.conditional_pair_tail source
    (μ.iid q) decode (· ∈ Y) (· ∈ K) hY
    (pairHit decode e K) p ε hm hp
    (by intro i; rw [hp i, pairHit_ambient_mass μ decode e he K i]; exact hsmall i)
    hpoint (pairHit_product_cross μ decode e he K) hterms

/-- The second displayed conditional estimate of v35
`lem:pair-projections`. Its moment is taken on the original source; the
division by `Y` occurs only after the unconditioned tail calculation. -/
theorem pair_projections_conditional_high
    {S Z : Type*} [Fintype S] [Fintype Z]
    (source : FiniteLaw S) (μ : FiniteLaw Z)
    {m q : ℕ} (hm : 0 < m) (decode : S → Fin q → Z)
    (hwise : IsDWise 8192 source decode μ)
    (e : Fin (2*m) → Fin q) (he : Function.Injective e)
    (Y K : Set S) (v : ℝ) (hv : 0 < v)
    (hY : v ≤ source.prob (· ∈ Y)) (_hK : K ⊆ Y)
    (hsmall : ∀ i : Fin m,
      (μ.iid 2).prob (· ∈ pairImage decode e K i) < 9/25) :
    source.prob (· ∈ K) / source.prob (· ∈ Y) ≤
      2*(625 : ℝ)^512/(v*(m : ℝ)^512) := by
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  let Ssum : S → ℝ := centeredPairSourceSum μ decode e K
  have hpoint : ∀ s ∈ K, (16/25 : ℝ)*(m : ℝ) ≤ Ssum s := by
    intro s hs
    simpa only [Ssum, centeredPairSourceSum,
      CurrentAdditive.FourthMoment.centeredPair, pairBaseMass] using
      retained_centered_pair_sum_large μ decode e he K hsmall s hs
  have hmoment : sourceMoment source Ssum 1024 ≤
      2*(256*(m : ℝ))^512 :=
    pairHit_source_high_moment source μ decode hwise e he K
  have hden : 0 < ((16/25 : ℝ)*(m : ℝ))^1024 := by positivity
  have hfactor :
      (256*(m : ℝ))^512 =
        ((16/25 : ℝ)*(m : ℝ))^1024 *
          ((625 : ℝ)/(m : ℝ))^512 := by
    have hbase : (((16/25 : ℝ)*(m : ℝ))^2) *
        ((625 : ℝ)/(m : ℝ)) = 256*(m : ℝ) := by
      field_simp
      ring
    rw [← hbase, mul_pow, ← pow_mul]
  have hmarkov := event_le_1024_moment source K Ssum
    ((16/25 : ℝ)*(m : ℝ)) (by positivity) hpoint
  have hnum : source.prob (· ∈ K) ≤
      2*(625 : ℝ)^512/(m : ℝ)^512 := by
    apply (mul_le_mul_iff_right₀ hden).mp
    calc
      _ ≤ sourceMoment source Ssum 1024 := hmarkov
      _ ≤ 2*(256*(m : ℝ))^512 := hmoment
      _ = ((16/25 : ℝ)*(m : ℝ))^1024 *
          (2*(625 : ℝ)^512/(m : ℝ)^512) := by
        rw [hfactor]
        rw [div_pow]
        ring
  have hYpos : 0 < source.prob (· ∈ Y) := hv.trans_le hY
  have hnum0 : 0 ≤ 2*(625 : ℝ)^512/(m : ℝ)^512 := by positivity
  have hquot : source.prob (· ∈ K) / source.prob (· ∈ Y) ≤
      (2*(625 : ℝ)^512/(m : ℝ)^512)/v := by
    apply (div_le_div_iff₀ hYpos hv).2
    have hleft := mul_le_mul_of_nonneg_right hnum hv.le
    have hright := mul_le_mul_of_nonneg_left hY hnum0
    nlinarith
  convert hquot using 1; field_simp

/-- Final consequence of v35 `lem:pair-projections`: conditional retained
mass at least `1/(4m)` forces an actual selected pair whose image has at
least `9/25` mass in the original marginal product law. -/
theorem pair_projections_good
    {S Z : Type*} [Fintype S] [Fintype Z]
    (source : FiniteLaw S) (μ : FiniteLaw Z)
    {m q : ℕ} (hm : 16 ≤ m) (decode : S → Fin q → Z)
    (hwise : IsDWise 8192 source decode μ)
    (e : Fin (2*m) → Fin q) (he : Function.Injective e)
    (Y K : Set S) (v ε : ℝ)
    (hv : 0 < v) (hv1 : v ≤ 1)
    (hY : v ≤ source.prob (· ∈ Y)) (hK : K ⊆ Y)
    (hε : 0 < ε)
    (hεcap : ε ≤ (2 : ℝ)^(-20 : ℤ)/1024 * v^((1 : ℝ)/256))
    (E : Finset (Fin q))
    (hgood : ∀ t : Fin (2*m), e t ∉ E)
    (hTV : ∀ J : Finset (Fin q),
      J ⊆ Finset.univ \ E → J.card ≤ 8 →
        projectionTV (condition source (· ∈ Y) (hv.trans_le hY))
          μ decode J ≤ ε)
    (hcond : 1/(4*(m : ℝ)) ≤
      source.prob (· ∈ K)/source.prob (· ∈ Y)) :
    ∃ i : Fin m, (9/25 : ℝ) ≤
      (μ.iid 2).prob (· ∈ pairImage decode e K i) := by
  by_contra hn
  push Not at hn
  have hsmall : ∀ i : Fin m,
      (μ.iid 2).prob (· ∈ pairImage decode e K i) < 9/25 := hn
  have hmR : (16 : ℝ) ≤ m := by exact_mod_cast hm
  have hmPos : (0 : ℝ) < m := by linarith
  have hoverlap := moment_ranges_overlap_1024 v ε hv hv1 hε hεcap
  by_cases hmoderate : (m : ℝ) ≤ 1/(128*ε)
  · have htail := pair_projections_conditional_fourth source μ
      (by omega : 0 < m) decode e he Y K hK (hv.trans_le hY)
      E ε hgood hTV hsmall
    have hnum := CurrentAdditive.FourthMoment.conditional_pair_numeric
      (m : ℝ) ε hmR hε hmoderate
    exact (not_lt_of_ge hcond) (htail.trans_lt hnum)
  · have hthreshold : 16*1024*v^(-(1/511 : ℝ)) ≤ (m : ℝ) :=
      hoverlap.trans (le_of_lt (lt_of_not_ge hmoderate))
    have htail := pair_projections_conditional_high source μ
      (by omega : 0 < m) decode hwise e he Y K v hv hY hK hsmall
    have hnum := high_pair_tail_constant_1024 v (m : ℝ)
      hv hmPos hthreshold
    have hsmall8 : 1/(8*(m : ℝ)) < 1/(4*(m : ℝ)) := by
      apply (div_lt_div_iff₀ (by positivity : (0 : ℝ) < 8*m)
        (by positivity : (0 : ℝ) < 4*m)).2
      nlinarith
    exact (not_lt_of_ge hcond) (htail.trans_lt (hnum.trans hsmall8))

/-- The same literal pair-projection consequence with the manuscript's
`ε(v,τ) = min{τ, 2⁻²⁰ R⁻¹ v^(4/R)}` at `R = 1024`. The exceptional set is
the one used in the finite-TV premise, rather than a reselected set. -/
theorem pair_projections_good_source_epsilon
    {S Z : Type*} [Fintype S] [Fintype Z]
    (source : FiniteLaw S) (μ : FiniteLaw Z)
    {m q : ℕ} (hm : 16 ≤ m) (decode : S → Fin q → Z)
    (hwise : IsDWise 8192 source decode μ)
    (e : Fin (2*m) → Fin q) (he : Function.Injective e)
    (Y K : Set S) (v τ : ℝ)
    (hv : 0 < v) (hv1 : v ≤ 1) (hτ : 0 < τ)
    (hY : v ≤ source.prob (· ∈ Y)) (hK : K ⊆ Y)
    (E : Finset (Fin q))
    (hgood : ∀ t : Fin (2*m), e t ∉ E)
    (hTV : ∀ J : Finset (Fin q),
      J ⊆ Finset.univ \ E → J.card ≤ 8 →
        projectionTV (condition source (· ∈ Y) (hv.trans_le hY))
          μ decode J ≤ CurrentAdditive.conditioningEpsilonR 1024 v τ)
    (hcond : 1/(4*(m : ℝ)) ≤
      source.prob (· ∈ K)/source.prob (· ∈ Y)) :
    ∃ i : Fin m, (9/25 : ℝ) ≤
      (μ.iid 2).prob (· ∈ pairImage decode e K i) := by
  have hεpos : 0 < CurrentAdditive.conditioningEpsilonR 1024 v τ :=
    CurrentAdditive.conditioningEpsilonR_pos (by decide) hv hτ
  have hεcap : CurrentAdditive.conditioningEpsilonR 1024 v τ ≤
      (2 : ℝ)^(-20 : ℤ)/1024 * v^((1 : ℝ)/256) := by
    unfold CurrentAdditive.conditioningEpsilonR
    convert min_le_right τ
      ((2 : ℝ)^(-(20 : ℝ))/1024 * v^((4 : ℝ)/1024)) using 1;
      norm_num
  exact pair_projections_good source μ hm decode hwise e he Y K v
    (CurrentAdditive.conditioningEpsilonR 1024 v τ) hv hv1 hY hK
    hεpos hεcap E hgood hTV hcond

end Pairs

end FiniteV35

#print axioms FiniteV35.ExactTupleList.entries_apply
#print axioms FiniteV35.product_blocks_power
#print axioms FiniteV35.product_blocks_two
#print axioms FiniteV35.many_product_blocks
#print axioms FiniteV35.full_restoration
#print axioms FiniteV35.full_restoration_upper
#print axioms FiniteV35.template_prefix
#print axioms FiniteV35.theta_half_ge_star
#print axioms FiniteV35.nonowner_count_le_destinationBudget
#print axioms FiniteV35.projection_cover_upto
#print axioms FiniteV35.owner_projections
#print axioms FiniteV35.conditioning_moment_both
#print axioms FiniteV35.conditioning_moment_disjoint_source
#print axioms FiniteV35.pair_projections_eight
#print axioms FiniteV35.pair_projections_conditional_fourth
#print axioms FiniteV35.pair_projections_conditional_high
#print axioms FiniteV35.pair_projections_good
#print axioms FiniteV35.pair_projections_good_source_epsilon
