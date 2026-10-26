import Paper2.ForeignOwnerRectangle
import Paper2.TwoStreamObstruction
import CurrentAdditive.GeneratedOwnerFixedTailClean
import CurrentAdditive.GeneratedOwnerPairAveraging
import CurrentAdditive.GeneratedTwoStreamObstruction

/-!
Private v34 shared-selector interface. The two source instantiations below
continue to use their distinct ambient tuple laws. In particular the
generated-law statement never replaces a conditioned law by a product law.
-/

namespace V34SharedSelector

open Paper2

noncomputable def amin : ℝ :=
  ((99 / 100 : ℝ) + (255 / 256 : ℝ)^2 - 1) / (255 / 256 : ℝ)^2

theorem amin_gt_pair_threshold (τ : ℝ) (hτ : τ ≤ 1 / 1000) :
    49 / 64 + τ < amin := by
  unfold amin
  norm_num at *
  linarith

theorem amin_positive : 0 < amin := by
  unfold amin
  norm_num

/-- The distinguished pair carrier cannot be empty under the stated mass. -/
theorem pair_nonempty {α : Type*} [Fintype α]
    (κ : FiniteLaw α) (P0 : Finset α)
    (ha : amin ≤ κ.prob (· ∈ (P0 : Set α))) : P0.Nonempty := by
  by_contra h
  have he : P0 = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  simp [he, FiniteLaw.prob] at ha
  have hp := amin_positive
  linarith

private theorem prod_fst_pushes {A B : Type*} [Fintype A] [Fintype B]
    (α : FiniteLaw A) (β : FiniteLaw B) :
    (α.prod β).PushesTo α Prod.fst := by
  classical
  intro E
  conv_lhs => rw [FiniteLaw.prod_prob α β (fun a _ => E a)]
  have hinner (a : A) : β.prob (fun _ : B => E a) = if E a then 1 else 0 := by
    by_cases ha : E a <;> simp [ha]
  simp_rw [hinner]
  simp only [FiniteLaw.prob]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : E a <;> simp [ha]

/-- Pair mass alone supplies the first-selector floor used by both source
proofs; it makes no independence claim about a conditioned retained law. -/
theorem pair_first_floor {S : Type*} [Fintype S]
    (σ : FiniteLaw S) (P0 : Finset (S × S)) (τ : ℝ)
    (ha : amin ≤ (σ.prod σ).prob (· ∈ (P0 : Set _)))
    (hτ : τ ≤ 1 / 1000) :
    τ ≤ σ.prob (· ∈ (fun z : S × S => z.1) '' (P0 : Set _)) := by
  have hproj := FiniteLaw.prob_le_image (σ.prod σ) σ Prod.fst
    (prod_fst_pushes σ σ) (P0 : Set _)
  have hm := amin_gt_pair_threshold τ hτ
  linarith

/-- The manuscript's a_min inequality discharges the quantified retained
pair condition needed at every unsplit step of the protocol proof. -/
theorem pair_retention {S : Type*} [Fintype S] [DecidableEq S]
    (σ : FiniteLaw S) (P0 : Finset (S × S)) (τ : ℝ)
    (ha : amin ≤ (σ.prod σ).prob (· ∈ (P0 : Set _)))
    (hτ : τ ≤ 1 / 1000) :
    ∀ P' : Finset (S × S), P' ⊆ P0 →
      Paper2.SourceSupportStep.mass (σ.prod σ) (P0 \ P') < τ →
      (49 / 64 : ℝ) ≤ (σ.prod σ).prob (· ∈ (P' : Set _)) := by
  classical
  intro P' hsub hloss
  have hsplit : Paper2.SourceSupportStep.mass (σ.prod σ) (P0 \ P') +
      Paper2.SourceSupportStep.mass (σ.prod σ) P' =
      Paper2.SourceSupportStep.mass (σ.prod σ) P0 := by
    unfold Paper2.SourceSupportStep.mass FiniteLaw.prob
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : z ∈ P'
    · have hp := hsub hz
      simp [hz, hp]
    · by_cases hp : z ∈ P0 <;> simp [hz, hp]
  change _ + (σ.prod σ).prob (· ∈ (P' : Set _)) =
    (σ.prod σ).prob (· ∈ (P0 : Set _)) at hsplit
  have hm := amin_gt_pair_threshold τ hτ
  linarith

#print axioms amin_gt_pair_threshold
#print axioms amin_positive
#print axioms pair_nonempty
#print axioms pair_first_floor
#print axioms pair_retention

end V34SharedSelector

namespace Paper2.TwoStreamObstruction

open Paper2 Paper2.TwoStreamInitial Paper2.PairedSelectorPopulation

variable {B J Rw Ω F : Type*} [Fintype B] [Fintype J]
  [Fintype Rw] [Fintype Ω] [Fintype F]
  [DecidableEq J] {q s : ℕ} [NeZero q]

/-- Abstract full-product instance of the v34 shared selector lemma.
The pair carrier is exactly S² with its original ambient product law;
the stated pair mass supplies both the first-selector floor and every
deletion-retention premise of the existing protocol argument. -/
theorem v34_abstract_selected_pair_lower
    (μ : PositiveRationalLaw B) (ν : PositiveRationalLaw J)
    (base : B → J → Bool) (M : Rw → (Ω ⊕ F) → Bool)
    (H ell a : ℕ) (hH : 2 ≤ H) (hq : q = 2 ^ ell) (hs : s = 2 ^ a)
    (x : ℝ) (hx : 0 < x)
    (hbase : RestrictionProfile base μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (hT : RestrictionProfile
      (fun z : Fin q → J => fun c : Fin q × B => base c.2 (z c.1))
      (ν.iid q).toFiniteLaw (columnLaw μ).toFiniteLaw x ((H + ell : ℕ) : ℤ))
    (κΩ : FiniteLaw Ω) (κF : FiniteLaw F)
    (bin : Rw → Fin s) (selector : Rw → Fin q → J)
    (Φ : Ω → Fin s → Fin q × B) (ψ : F → Fin q × B)
    (hordinary : ∀ r c, M r (.inl c) =
      base (Φ c (bin r)).2 (selector r (Φ c (bin r)).1))
    (hΦ : κΩ.PushesTo ((columnLaw μ).toFiniteLaw.iid s) Φ)
    (hψ : κF.PushesTo (columnLaw μ).toFiniteLaw ψ)
    (ι : ((Fin q → J) × (Fin q → J)) → Rw)
    (star : Fin s) (P0 : Finset ((Fin q → J) × (Fin q → J)))
    (R : Set Rw) (O : Set Ω) (G : Set F)
    (hι : ∀ e ∈ P0, ι e ∈ R)
    (hstar : ∀ e ∈ P0, bin (ι e) = star ∧ selector (ι e) = e.1)
    (hforeign : ∀ e ∈ P0, ∀ f,
      M (ι e) (.inr f) = base (ψ f).2 (e.2 (ψ f).1))
    (hPair : V34SharedSelector.amin ≤
      ((ν.iid q).toFiniteLaw.prod (ν.iid q).toFiniteLaw).prob
        (· ∈ (P0 : Set _)))
    (hrow : ∀ i ≠ star, 2 * s * x ≤ (ν.iid q).toFiniteLaw.prob
      (fun z => ∃ r ∈ R, bin r = i ∧ selector r = z))
    (ε δ : ℝ) (hO : 1 - ε ≤ κΩ.prob (· ∈ O))
    (hF : δ ≤ κF.prob (· ∈ G)) (hδ : δ ≤ 1)
    (hslack : 2 * q * x + 5 * ε + 2 / q ≤ δ)
    (hτ : 2 * s * x ≤ 1 / 1000) :
    H + ell + a + 1 ≤ Compression.restrictionD M R
      (retainedColumns O G) := by
  let σ := (ν.iid q).toFiniteLaw
  have hfirst : 2 * s * x ≤ σ.prob
      (· ∈ (fun e : (Fin q → J) × (Fin q → J) => e.1) ''
        (P0 : Set _)) :=
    V34SharedSelector.pair_first_floor σ P0 (2 * s * x) hPair hτ
  have hret := V34SharedSelector.pair_retention σ P0 (2 * s * x) hPair hτ
  have hsmall : 2 * s * x ≤ 1 / 8 := by linarith
  have hpush : (σ.prod σ).PushesTo (σ.prod σ) id := by
    intro E
    rfl
  exact restriction_lower μ ν base M H ell a hH hq hs x hx hbase hT
    κΩ κF (σ.prod σ) bin selector Φ ψ hordinary hΦ hψ ι id hpush
    star P0 R O G hι hstar hforeign hfirst hrow
    (by intro P' hsub hloss
        simpa only [Set.image_id] using hret P' hsub hloss)
    ε δ hO hF hδ hslack hsmall

#print axioms v34_abstract_selected_pair_lower

end Paper2.TwoStreamObstruction

namespace Paper2.ForeignOwnerRectangle

open Paper2 Paper2.SourceMatrix Paper2.SourceLaws
  Paper2.SourceLawBinding Paper2.ForeignOwnerProjection
  Paper2.ForeignOwnerOtherBins Paper2.SourceProfileParameters
open Workspace.Types.Protocol Workspace.Types.CommComplexity

variable {V X : Type*} [Fintype V] [Nonempty V] [Fintype X]
  [DecidableEq X] {q₁ q₂ s w : ℕ} [NeZero q₁]

private theorem v34_width_ge_four (L : ℕ) : 4 ≤ width L := by
  unfold width
  have h := exponent_ge L
  have hp : 2 ^ 2 ≤ 2 ^ exponent L :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  norm_num at hp
  exact hp

local instance (L : ℕ) : NeZero (outerWidth L) := ⟨by
  unfold outerWidth
  positivity⟩

local instance (L : ℕ) : NeZero (width L - 2) := ⟨by
  have := width_admissible L
  omega⟩

local instance (L : ℕ) : NeZero (width L) := ⟨by
  unfold width
  positivity⟩

/-- The full-product source's distinguished pair is realised by one jointly
retained original tuple. The deletion guarantee is part of the interface. -/
theorem v34_full_product_pair_package
    (μ : PositiveRationalLaw X) (hs : 4 ≤ s)
    (i j : Fin w) (U : Set (Fin w → K V X q₁ q₂ s))
    (hgood : (99 / 100 : ℝ) ≤
      ((matrixColumnLaw (V := V) μ q₁ q₂ s hs).toFiniteLaw.prod
        (matrixColumnLaw (V := V) μ q₁ q₂ s hs).toFiniteLaw).prob
          (· ∈ (fun y => (y i, y j)) '' U))
    (τ : ℝ) (hτ : τ ≤ 1 / 1000) :
    ∃ p r : Fin s,
      ∃ P0 : Finset (Template q₁ q₂ X × Template q₁ q₂ X),
      (∀ z, z ∈ P0 ↔ z ∈ pairImage U i j p r) ∧
      (V34SharedSelector.amin ≤
        ((templateLaw μ q₁ q₂).toFiniteLaw.prod
          (templateLaw μ q₁ q₂).toFiniteLaw).prob (· ∈ (P0 : Set _))) ∧
      (∀ P' : Finset (Template q₁ q₂ X × Template q₁ q₂ X),
        P' ⊆ P0 →
        SourceSupportStep.mass
          ((templateLaw μ q₁ q₂).toFiniteLaw.prod
            (templateLaw μ q₁ q₂).toFiniteLaw) (P0 \ P') < τ →
        (49 / 64 : ℝ) ≤
          ((templateLaw μ q₁ q₂).toFiniteLaw.prod
            (templateLaw μ q₁ q₂).toFiniteLaw).prob (· ∈ (P' : Set _))) := by
  simpa [V34SharedSelector.amin] using
    original_pair_package (V := V) μ hs i j U hgood τ
      (V34SharedSelector.amin_gt_pair_threshold τ hτ)

/-- The v34 full-product lower bound for either of its actual foreign tags.
Both imported branches construct representatives in the original retained
product input and prove the respective foreign entry map. -/
theorem v34_full_product_lower
    {Y : Type*} [Fintype Y]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (base : X → Y → Bool) (L d w : ℕ)
    (activity : SourceConstruction.Items (width L) V →
      Fin (outerWidth L) → Option (Fin (width L)))
    (ξ₀ : Tail (width L) Y) (i j : Fin w) (hij : i ≠ j)
    (R : Set (Fin w × TaggedColumn (width L - 2)
      (outerWidth L) (width L) Y))
    (Y' : Set (Fin w → K V X (width L - 2) (outerWidth L) (width L)))
    (δsrc ζsrc ε δ : ℝ)
    (hpair : (99 / 100 : ℝ) ≤ ProductProjections.projectionMass
      (fun _ => (matrixColumnLaw (V := V) μ (width L - 2) (outerWidth L)
        (width L) (v34_width_ge_four L)).toFiniteLaw) (· ∈ Y') {i,j})
    (hsingle : 1 - SourceDeletionParameters.eta (width L) δsrc ζsrc ≤
      ProductProjections.projectionMass
        (fun _ => (matrixColumnLaw (V := V) μ (width L - 2)
          (outerWidth L) (width L) (v34_width_ge_four L)).toFiniteLaw)
        (· ∈ Y') {i})
    (hO : 1 - ε ≤
      (rawLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw.prob
        (fun Z => (i, .unrestricted Z) ∈ R))
    (hprotected :
      δ ≤ (fixedTailLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw.prob
        (fun f => (j, .fixedTail f) ∈ R) ∨
      δ ≤ (outerLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw.prob
        (fun f => (j, .diagonal f) ∈ R))
    (hδ : δ ≤ 1)
    (hslack : 2 * outerWidth L * x L + 5 * ε + 2 / outerWidth L ≤ δ)
    (hsmall : 2 * (width L : ℝ) * x L ≤ 1 / 1000)
    (hd : 3 ≤ d)
    (hp : RestrictionProfile base μ.toFiniteLaw ν.toFiniteLaw (rho L) (d : ℤ))
    (hinner : (width L : ℝ) * rho L ≤ 1 / 1000)
    (houter : (outerWidth L : ℝ) * x L ≤ 1 / 10000)
    (hwide : (10 * L : ℝ) ≤ (outerWidth L : ℝ) / 4096)
    (href : (width L : ℝ) * x L ≤ 1 / 10000) :
    d + exponent L + outerExponent L + exponent L + 1 ≤
      Compression.restrictionD (fullInterlace (N base activity ξ₀) w) R Y' := by
  rcases hprotected with hf | hdia
  · exact fixedTail_owner_lower μ ν base L d w activity ξ₀ i j hij
      R Y' δsrc ζsrc ε δ hpair hsingle hO hf hδ hslack hsmall
      hd hp hinner houter hwide href
  · exact diagonal_owner_lower μ ν base L d w activity ξ₀ i j hij
      R Y' δsrc ζsrc ε δ hpair hsingle hO hdia hδ hslack hsmall
      hd hp hinner houter hwide href

#print axioms v34_full_product_pair_package
#print axioms v34_full_product_lower

end Paper2.ForeignOwnerRectangle

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix
open Paper2.TwoStreamInitial

variable {G V Aux X Y : Type*}
  [Fintype G] [Fintype V] [Fintype Aux]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  [DecidableEq G] [DecidableEq V] [DecidableEq Aux]
  {D q₁ q₂ s : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

/-- Abstract generated-source instance of the v34 shared lemma. The
ambient selector law is the exact generated source law and the pair carrier
uses its product before any conditioning. The remaining entry equations
are the lemma's displayed matrix table. -/
theorem v34_abstract_selected_pair_lower
    {Rw F : Type*} [Fintype Rw] [Fintype F]
    (R₀ : X → Y → Bool)
    (M : Rw → ((src.outer.Label × src.gamma.Label) ⊕ F) → Bool)
    (H ell a : ℕ) (hH : 2 ≤ H) (hq : q₂ = 2^ell) (hs : s = 2^a)
    (x : ℝ) (hx : 0 < x) (hD : 8 ≤ D)
    (hA : RestrictionProfile (A src R₀)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
      x (H : ℤ))
    (hT : RestrictionProfile (T src R₀)
      src.inner.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw
      x ((H+ell : ℕ) : ℤ))
    (κF : FiniteLaw F)
    (bin : Rw → Fin s) (selector : Rw → src.inner.Label)
    (ψ : F → J src)
    (hordinary : ∀ row c, M row (.inl c) =
      T src R₀ (selector row) (src.outer.decode c.1 (bin row)))
    (hψ : κF.PushesTo
      ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw ψ)
    (ι : (src.inner.Label × src.inner.Label) → Rw)
    (star : Fin s) (P0 : Finset (src.inner.Label × src.inner.Label))
    (R : Set Rw) (O : Set (src.outer.Label × src.gamma.Label)) (G : Set F)
    (hι : ∀ e ∈ P0, ι e ∈ R)
    (hstar : ∀ e ∈ P0,
      bin (ι e) = star ∧ selector (ι e) = e.1)
    (hforeign : ∀ e ∈ P0, ∀ f,
      M (ι e) (.inr f) = T src R₀ e.2 (ψ f))
    (hPair : V34SharedSelector.amin ≤
      (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw).prob
        (· ∈ (P0 : Set _)))
    (hrow : ∀ i ≠ star, 2*s*x ≤ src.inner.law.toFiniteLaw.prob
      (fun z => ∃ r ∈ R, bin r = i ∧ selector r = z))
    (ε δ : ℝ)
    (hO : 1-ε ≤ (ordinaryLaw src).toFiniteLaw.prob (· ∈ O))
    (hF : δ ≤ κF.prob (· ∈ G)) (hδ : δ ≤ 1)
    (hslack : 2*q₂*x + 5*ε + 2/q₂ ≤ δ)
    (hτ : 2*s*x ≤ 1/1000) (hpairsmall : 2*q₂*x ≤ 1/8) :
    H+ell+a+1 ≤ Compression.restrictionD M R (retainedColumns O G) := by
  classical
  let σ := src.inner.law.toFiniteLaw
  have hfirst : 2*s*x ≤ σ.prob
      (· ∈ (fun e : src.inner.Label × src.inner.Label => e.1) ''
        (P0 : Set _)) :=
    V34SharedSelector.pair_first_floor σ P0 (2*s*x) hPair hτ
  have hret := V34SharedSelector.pair_retention σ P0 (2*s*x) hPair hτ
  have hsmall : 2*s*x ≤ 1/8 := by linarith
  have hpush : (σ.prod σ).PushesTo (σ.prod σ) id := by
    intro E
    rfl
  exact generated_two_stream_restriction_lower src R₀ M
    H ell a hH hq hs x hx hD hA hT (κF := κF) (κE := σ.prod σ)
    bin selector ψ hordinary hψ ι id hpush star P0 R O G
    hι hstar hforeign hfirst hrow
    (by intro P' hsub hloss
        simpa only [Set.image_id] using hret P' hsub hloss)
    ε δ hO hF hδ hslack hsmall hpairsmall

#print axioms v34_abstract_selected_pair_lower

/-- The v34 pair set is the image of actual retained generated rows,
measured under the original, unconditioned product law of source selectors. -/
theorem v34_generated_pair_mass
    (μI : PositiveRationalLaw (G × (V ⊕ Aux)))
    {w : ℕ} (streams : InternalStreams src μI w)
    (U : Set (InternalLabel src streams)) (i j : Fin w)
    (hgood : (99 / 100 : ℝ) ≤
      ((rowLaw src μI).toFiniteLaw.prod
        (rowLaw src μI).toFiniteLaw).prob
          (· ∈ (fun t =>
            (InternalStreams.decode src streams t i,
             InternalStreams.decode src streams t j)) '' U)) :
    ∃ p r : Fin s,
      V34SharedSelector.amin ≤
        (src.inner.law.toFiniteLaw.prod
          src.inner.law.toFiniteLaw).prob
            (· ∈ ownerPairImage src streams U i j p r) := by
  simpa [V34SharedSelector.amin] using
    owner_pair_image_mass_of_good_projection src μI streams U i j hgood

/-- The selected generated pair set remains a set of images of jointly
retained original rows. Its mass and deletion premise are under the ambient
selector product law, with no independence assertion after conditioning. -/
theorem v34_generated_pair_package
    (μI : PositiveRationalLaw (G × (V ⊕ Aux)))
    {w : ℕ} (streams : InternalStreams src μI w)
    (U : Set (InternalLabel src streams)) (i j : Fin w)
    (hgood : (99 / 100 : ℝ) ≤
      ((rowLaw src μI).toFiniteLaw.prod
        (rowLaw src μI).toFiniteLaw).prob
          (· ∈ (fun t =>
            (InternalStreams.decode src streams t i,
             InternalStreams.decode src streams t j)) '' U))
    (τ : ℝ) (hτ : τ ≤ 1 / 1000) :
    ∃ p r : Fin s,
      ∃ P0 : Finset (src.inner.Label × src.inner.Label),
      (∀ z, z ∈ P0 ↔ z ∈ ownerPairImage src streams U i j p r) ∧
      (V34SharedSelector.amin ≤
        (src.inner.law.toFiniteLaw.prod
          src.inner.law.toFiniteLaw).prob (· ∈ (P0 : Set _))) ∧
      (∀ P' : Finset (src.inner.Label × src.inner.Label),
        P' ⊆ P0 →
        SourceSupportStep.mass
          (src.inner.law.toFiniteLaw.prod
            src.inner.law.toFiniteLaw) (P0 \ P') < τ →
        (49 / 64 : ℝ) ≤
          (src.inner.law.toFiniteLaw.prod
            src.inner.law.toFiniteLaw).prob (· ∈ (P' : Set _))) := by
  classical
  obtain ⟨p, r, ha⟩ := v34_generated_pair_mass src μI streams U i j hgood
  let P0 : Finset (src.inner.Label × src.inner.Label) :=
    Finset.univ.filter (· ∈ ownerPairImage src streams U i j p r)
  have hP0 : ∀ z, z ∈ P0 ↔ z ∈ ownerPairImage src streams U i j p r := by
    intro z
    simp [P0]
  have ha0 : V34SharedSelector.amin ≤
      (src.inner.law.toFiniteLaw.prod
        src.inner.law.toFiniteLaw).prob (· ∈ (P0 : Set _)) := by
    convert ha using 1
    congr 1
    funext z
    exact propext (hP0 z)
  refine ⟨p, r, P0, hP0, ha0, ?_⟩
  exact ownerPair_retention src P0 V34SharedSelector.amin τ ha0
    (V34SharedSelector.amin_gt_pair_threshold τ hτ)

/-- The exact selected-pair version of the v34 generated shared lemma.
This starts from the manuscript's pair-image mass, rather than an earlier
good-projection premise, and covers both physical other-copy tags. -/
theorem v34_generated_from_selected_pair
    (μI : PositiveRationalLaw (G × (V ⊕ Aux)))
    {w : ℕ} (streams : InternalStreams src μI w)
    (R₀ : X → Y → Bool)
    (activity : (G × (V ⊕ Aux)) → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) (i j : Fin w) (p r : Fin s)
    (U : Set (InternalLabel src streams))
    (Vrows : Set (Fin w × Column src))
    (H ell a : ℕ) (hH : 2 ≤ H)
    (hq : q₂ = 2^ell) (hs : s = 2^a)
    (x : ℝ) (hx : 0 < x) (hD : 8 ≤ D)
    (hA : RestrictionProfile (A src R₀)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
      x (H : ℤ))
    (hT : RestrictionProfile (T src R₀)
      src.inner.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw
      x ((H+ell : ℕ) : ℤ))
    (hPair : V34SharedSelector.amin ≤
      (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw).prob
        (· ∈ ownerPairImage src streams U i j p r))
    (hOther : ∀ b ≠ p, 2*s*x ≤ src.inner.law.toFiniteLaw.prob
      (fun z => ∃ t ∈ U,
        streams.metadataStream.decode t.1 i = .inl b ∧
        streams.selectorStream.decode t.2.2 i = z))
    (ε δ : ℝ)
    (hO : 1-ε ≤ (ordinaryLaw src).toFiniteLaw.prob
      (fun o => (i, .ordinary o) ∈ Vrows))
    (hF :
      δ ≤ src.outer.law.toFiniteLaw.prob
        (fun f => (j, .fixedTail f) ∈ Vrows) ∨
      δ ≤ (Paper2.PairedSelectorPopulation.columnLaw src.gamma.law).toFiniteLaw.prob
        (fun f => (j, .diagonal f) ∈ Vrows))
    (hδ : δ ≤ 1)
    (hslack : 2*q₂*x+5*ε+2/q₂ ≤ δ)
    (hτ : 2*s*x ≤ 1/1000) (hpairsmall : 2*q₂*x ≤ 1/8) :
    H+ell+a+1 ≤ Compression.restrictionD
      (W src streams R₀ activity ξ₀) U Vrows := by
  have hmargin : 49/64 + 2*s*x < V34SharedSelector.amin :=
    V34SharedSelector.amin_gt_pair_threshold (2*s*x) hτ
  have hsmall : 2*s*x ≤ 1/8 := by linarith
  rcases hF with hf | hdia
  · exact owner_to_owner_W_lower_fixed_tail_bins src streams
      R₀ activity ξ₀ i j p r U Vrows H ell a hH hq hs x hx hD
      hA hT V34SharedSelector.amin ε δ hPair hmargin hOther
      hO hf hδ hslack hsmall hpairsmall
  · exact owner_to_owner_W_lower_fixed_bins src streams
      R₀ activity ξ₀ i j p r U Vrows H ell a hH hq hs x hx hD
      hA hT V34SharedSelector.amin ε δ hPair hmargin hOther
      hO hdia hδ hslack hsmall hpairsmall

/-- Exact v34 fixed-tail generated caller with the schedule margin discharged.
The imported theorem constructs actual retained row representatives and proves
both ordinary and foreign entry identities for `W`. -/
theorem v34_generated_fixedTail_lower
    (μI' : PositiveRationalLaw (G × (V ⊕ Aux)))
    {w : ℕ} (streams : InternalStreams src μI' w)
    (R₀ : X → Y → Bool)
    (activity : (G × (V ⊕ Aux)) → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) (i j : Fin w)
    (U : Set (InternalLabel src streams))
    (Vrows : Set (Fin w × Column src))
    (H ell a : ℕ) (hH : 2 ≤ H)
    (hq : q₂ = 2^ell) (hs : s = 2^a)
    (x : ℝ) (hx : 0 < x) (hD : 8 ≤ D)
    (hA : RestrictionProfile (A src R₀)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
      x (H : ℤ))
    (hT : RestrictionProfile (T src R₀)
      src.inner.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw
      x ((H+ell : ℕ) : ℤ))
    (hgood : (99 / 100 : ℝ) ≤
      ((rowLaw src μI').toFiniteLaw.prod
        (rowLaw src μI').toFiniteLaw).prob
          (· ∈ (fun t =>
            (InternalStreams.decode src streams t i,
             InternalStreams.decode src streams t j)) '' U))
    (hOther : ∀ p b : Fin s, b ≠ p →
      2*s*x ≤ src.inner.law.toFiniteLaw.prob
        (fun z => ∃ t ∈ U,
          streams.metadataStream.decode t.1 i = .inl b ∧
          streams.selectorStream.decode t.2.2 i = z))
    (ε δ : ℝ)
    (hO : 1-ε ≤ (ordinaryLaw src).toFiniteLaw.prob
      (fun o => (i, .ordinary o) ∈ Vrows))
    (hF : δ ≤ src.outer.law.toFiniteLaw.prob
      (fun f => (j, .fixedTail f) ∈ Vrows))
    (hδ : δ ≤ 1)
    (hslack : 2*q₂*x+5*ε+2/q₂ ≤ δ)
    (hτ : 2*s*x ≤ 1/1000) (hpairsmall : 2*q₂*x ≤ 1/8) :
    H+ell+a+1 ≤ Compression.restrictionD
      (W src streams R₀ activity ξ₀) U Vrows := by
  have hmargin : 49/64 + 2*s*x <
      ((99 / 100 : ℝ) + (255 / 256 : ℝ)^2 - 1) /
        (255 / 256 : ℝ)^2 :=
    V34SharedSelector.amin_gt_pair_threshold (2*s*x) hτ
  have hsmall : 2*s*x ≤ 1/8 := by linarith
  exact owner_to_owner_W_lower_fixed_tail_good_projection src μI' streams
    R₀ activity ξ₀ i j U Vrows H ell a hH hq hs x hx hD hA hT
    hgood hmargin hOther ε δ hO hF hδ hslack hsmall hpairsmall

/-- Exact v34 diagonal generated caller, again under the unconditioned
indexed-row product law for selecting the pair image. -/
theorem v34_generated_diagonal_lower
    (μI : PositiveRationalLaw (G × (V ⊕ Aux)))
    {w : ℕ} (streams : InternalStreams src μI w)
    (R₀ : X → Y → Bool)
    (activity : (G × (V ⊕ Aux)) → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) (i j : Fin w)
    (U : Set (InternalLabel src streams))
    (Vrows : Set (Fin w × Column src))
    (H ell a : ℕ) (hH : 2 ≤ H)
    (hq : q₂ = 2^ell) (hs : s = 2^a)
    (x : ℝ) (hx : 0 < x) (hD : 8 ≤ D)
    (hA : RestrictionProfile (A src R₀)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
      x (H : ℤ))
    (hT : RestrictionProfile (T src R₀)
      src.inner.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw
      x ((H+ell : ℕ) : ℤ))
    (hgood : (99 / 100 : ℝ) ≤
      ((rowLaw src μI).toFiniteLaw.prod
        (rowLaw src μI).toFiniteLaw).prob
          (· ∈ (fun t =>
            (InternalStreams.decode src streams t i,
             InternalStreams.decode src streams t j)) '' U))
    (hOther : ∀ p b : Fin s, b ≠ p →
      2*s*x ≤ src.inner.law.toFiniteLaw.prob
        (fun z => ∃ t ∈ U,
          streams.metadataStream.decode t.1 i = .inl b ∧
          streams.selectorStream.decode t.2.2 i = z))
    (ε δ : ℝ)
    (hO : 1-ε ≤ (ordinaryLaw src).toFiniteLaw.prob
      (fun o => (i, .ordinary o) ∈ Vrows))
    (hF : δ ≤
      (Paper2.PairedSelectorPopulation.columnLaw src.gamma.law).toFiniteLaw.prob
        (fun f => (j, .diagonal f) ∈ Vrows))
    (hδ : δ ≤ 1)
    (hslack : 2*q₂*x+5*ε+2/q₂ ≤ δ)
    (hτ : 2*s*x ≤ 1/1000) (hpairsmall : 2*q₂*x ≤ 1/8) :
    H+ell+a+1 ≤ Compression.restrictionD
      (W src streams R₀ activity ξ₀) U Vrows := by
  have hmargin : 49/64 + 2*s*x <
      ((99 / 100 : ℝ) + (255 / 256 : ℝ)^2 - 1) /
        (255 / 256 : ℝ)^2 :=
    V34SharedSelector.amin_gt_pair_threshold (2*s*x) hτ
  have hsmall : 2*s*x ≤ 1/8 := by linarith
  exact owner_to_owner_W_lower_good_projection src μI streams
    R₀ activity ξ₀ i j U Vrows H ell a hH hq hs x hx hD hA hT
    hgood hmargin hOther ε δ hO hF hδ hslack hsmall hpairsmall

#print axioms v34_generated_pair_mass
#print axioms v34_generated_pair_package
#print axioms v34_generated_from_selected_pair
#print axioms v34_generated_fixedTail_lower
#print axioms v34_generated_diagonal_lower

end CurrentAdditive.DeterministicIndexedMatrix.Sources
