import CurrentAdditive.V39FullProductSpecialization
import CurrentAdditive.V42IndexedAlignment

/-! Apply the checked common internal-interlace theorem to literal full
sources, then return its three conclusions to the original full-product
alphabets. Source profiles, source near-full hardness, source upper bound
and the stated scalar margins are the only mathematical inputs. -/

namespace CurrentAdditive.V42FullProductAlignment

open Paper2 Paper2.SourceMatrix
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicIndexedMatrix.Sources
open CurrentAdditive.V39FullProductSources

variable {G V Aux X Y : Type*}
  [Fintype G] [Fintype V] [Fintype Aux] [Fintype X] [Fintype Y]
  [DecidableEq G] [DecidableEq V] [DecidableEq Aux] [DecidableEq X] [DecidableEq Y]
  {q₁ q₂ s w : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
  (μX : PositiveRationalLaw X) (μY : PositiveRationalLaw Y)
  (μI : PositiveRationalLaw (G × (V ⊕ Aux)))

local notation "fullSrc" => fullSources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY
local notation "μK" => rowLaw fullSrc μI
local notation "streams" => fullStreams (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY μI w

/-- The common finite alignment conclusion on the original full-product
W. The auxiliary stream labels do not occur in the output matrix or laws. -/
theorem alignment
    (R₀ : X → Y → Bool) (activity : (G × (V ⊕ Aux)) → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) (H ell b r e0 : ℕ) (x θ η : ℝ)
    (hH : 2 ≤ H) (hr : 2 ≤ r) (hwr : w=2^r) (hq : q₂=2^ell) (hs : s=2^b)
    (hx : 0 < x) (hθ : 0 < θ) (hη : 0 < η)
    (hA : V38RestrictionProfiles.TwoThresholdProfile
      (fun γ j => SourceMatrix.M₁ R₀ j γ)
      (μY.iid (q₁+s+1)).toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw x (H : ℤ))
    (hT : V38RestrictionProfiles.TwoThresholdProfile (SourceMatrix.T (q₁ := q₁) (q₂ := q₂) (s := s) R₀)
      (SourceLaws.templateLaw μX q₁ q₂).toFiniteLaw
      (SourceLaws.outerLaw μY q₁ q₂ s).toFiniteLaw x ((H+ell : ℕ) : ℤ))
    (href : V38RestrictionProfiles.TwoThresholdProfile
      (fun c a => raw R₀ activity a c)
      (SourceLaws.rawLaw μY q₁ q₂ s).toFiniteLaw (μK).toFiniteLaw x ((H+ell+b : ℕ) : ℤ))
    (hnearfull : ∀ (U : Set (V38Matrix.TaggedColumn q₁ q₂ s Y))
      (Z : Set (RawRow q₁ q₂ s X (G × (V ⊕ Aux)))),
      1-η ≤ (V38Matrix.taggedLaw μY).toFiniteLaw.prob (· ∈ U) →
      1-η ≤ (μK).toFiniteLaw.prob (· ∈ Z) →
      H+ell+b+1 ≤ Compression.restrictionD
        (fun c a => raw R₀ activity a (V38Matrix.forgetTag ξ₀ c)) U Z)
    (hcap : V38Moments.exceptionCount θ (η/2) ≤ e0)
    (hexc : 4*(2*e0) ≤ w)
    (hexcReceipt : (2*(s : ℝ))*(2*e0) ≤ η*w/16)
    (hinit : 2*(w : ℝ)*x+η/(16*(255/256 : ℝ)) ≤ 1)
    (hwx : (w : ℝ)*x ≤ 1) (h2x : 2*x ≤ 1)
    (hloss : 2*(w : ℝ)^2*x ≤ η/(16*(255/256 : ℝ)))
    (hwidth : (w : ℝ)^2*q₂*x ≤ 1)
    (hforeignWidth : 4*(1/256 : ℝ)*w*q₂*x ≤ η/32)
    (hfloor : 2*s*x ≤ 1-η*(s : ℝ)/(2*(255/256 : ℝ)))
    (hpairMargin : 49/64+2*s*x <
      ((99/100 : ℝ)+(255/256 : ℝ)^2-1)/(255/256 : ℝ)^2)
    (hsmall : 2*s*x ≤ 1/8) (hpairSmall : 2*q₂*x ≤ 1/8)
    (hflag : V42IncomingGuard.flagConstant/(s : ℝ)^128 ≤ θ/4)
    (hException : V38Moments.exceptionCount (θ/4) 1 ≤ s*q₂)
    (hθ1 : θ ≤ 1) (he : V38Moments.exceptionCount θ 1 ≤ w/128)
    (hwxProfile : (w : ℝ)*x < 1/256)
    (hsourceUpper : Workspace.Types.CommComplexity.D
      (fun (c : V38Matrix.TaggedColumn q₁ q₂ s Y)
        (a : RawRow q₁ q₂ s X (G × (V ⊕ Aux))) =>
        raw R₀ activity a (V38Matrix.forgetTag ξ₀ c)) ≤ H+ell+b+1) :
    Workspace.Types.CommComplexity.D
      (fullW (q₁ := q₁) (w := w) R₀ activity ξ₀) = H+ell+b+1+r ∧
    (letI : Nonempty (Fin w) := Fin.pos_iff_nonempty.mp (by rw [hwr]; positivity)
     V38RestrictionProfiles.TwoThresholdProfile
      (fullW (q₁ := q₁) (w := w) R₀ activity ξ₀)
      ((μK).toFiniteLaw.iid w)
      ((PositiveRationalLaw.uniform (Fin w)).prod
        (V38Matrix.taggedLaw (q₁ := q₁) (q₂ := q₂) (s := s) μY)).toFiniteLaw
      θ (((H+ell+b+1+r : ℕ) : ℤ)-1)) ∧
    (letI : Nonempty (Fin w) := Fin.pos_iff_nonempty.mp (by rw [hwr]; positivity)
     ∀ (R : Set (Fin w × V38Matrix.TaggedColumn q₁ q₂ s Y))
       (Yevent : Set (Fin w → RawRow q₁ q₂ s X (G × (V ⊕ Aux)))),
      1-η/(16*w) ≤ ((PositiveRationalLaw.uniform (Fin w)).prod
        (V38Matrix.taggedLaw (q₁ := q₁) (q₂ := q₂) (s := s) μY)).toFiniteLaw.prob (· ∈ R) →
      θ ≤ ((μK).toFiniteLaw.iid w).prob (· ∈ Yevent) →
      H+ell+b+1+r ≤ Compression.restrictionD
        (fullW (q₁ := q₁) (w := w) R₀ activity ξ₀) Yevent R) := by
  classical
  letI : NeZero w := ⟨by rw [hwr]; positivity⟩
  have hrow : (μK).toFiniteLaw.PushesTo (μK).toFiniteLaw
      (rowEquiv (D := 8192) μX μY) := by intro E; rfl
  have href' := reference_profile_pullback (D := 8192) μX μY μK μK hrow
    R₀ activity ξ₀ x ((H+ell+b : ℕ) : ℤ) href
  have hnear' := source_nearfull_pullback (D := 8192) μX μY μK μK hrow
    R₀ activity ξ₀ (H+ell+b+1) η hnearfull
  have hu : Workspace.Types.CommComplexity.D
      (V38IndexedTwoTag.matrix fullSrc R₀ activity ξ₀) ≤ H+ell+b+1 := by
    have heq := funext fun c => funext fun a =>
      matrix_entry (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) (I := G × (V ⊕ Aux))
        μX μY R₀ activity ξ₀ c a
    rw [heq]
    exact (Workspace.ProofLemmas.SublemmaPrecompNoIncrease
      (fun c a => raw R₀ activity a (V38Matrix.forgetTag ξ₀ c))
      (columnMap (D := 8192) μX μY) (rowEquiv (D := 8192) μX μY)).trans hsourceUpper
  have hA' : V38RestrictionProfiles.TwoThresholdProfile (A fullSrc R₀)
      (fullSrc).gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw x (H : ℤ) := hA
  have hT' : V38RestrictionProfiles.TwoThresholdProfile (T fullSrc R₀)
      (fullSrc).inner.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₂)).prod (fullSrc).gamma.law).toFiniteLaw
      x ((H+ell : ℕ) : ℤ) := hT
  obtain ⟨hcost,hprofile,hnear⟩ := V42IndexedAlignment.alignment fullSrc μI streams
    R₀ activity ξ₀ H ell b r e0 x θ η hH hr hwr hq hs hx hθ hη
    hA' hT' href' hnear' hcap hexc hexcReceipt hinit hwx h2x hloss hwidth hforeignWidth
    hfloor hpairMargin hsmall hpairSmall hflag hException hθ1 he hwxProfile hu
  refine ⟨?_,?_,?_⟩
  · rwa [actualW_D_eq (D := 8192) μX μY μI w R₀ activity ξ₀] at hcost
  · exact (fullW_profile_iff (D := 8192) μX μY μI w R₀ activity ξ₀ θ _).mp hprofile
  · intro R Yevent hR hY
    have hR' : 1-η/(16*w) ≤
        (V39IndexedTwoFamilyRun.firstRowLaw fullSrc (by rw [hwr]; positivity)).prob
          (· ∈ copyColumnMap (D := 8192) μX μY ⁻¹' R) := by
      change 1-η/(16*w) ≤
        (((PositiveRationalLaw.uniform (Fin w)).prod (V38IndexedTwoTag.law fullSrc)).toFiniteLaw).prob
          (fun c => copyColumnMap (D := 8192) μX μY c ∈ R)
      rw [copyColumn_pushes (D := 8192) μX μY (· ∈ R)]
      exact hR
    have hY' : θ ≤ (streams).law.toFiniteLaw.prob
        (· ∈ tupleMap (D := 8192) μX μY μI w ⁻¹' Yevent) := by
      change θ ≤ (streams).law.toFiniteLaw.prob
        (fun t => tupleMap (D := 8192) μX μY μI w t ∈ Yevent)
      rw [tuple_event_prob]
      exact hY
    have hh := hnear (copyColumnMap (D := 8192) μX μY ⁻¹' R)
      (tupleMap (D := 8192) μX μY μI w ⁻¹' Yevent) hR' hY'
    rwa [actualW_restriction_preimage] at hh

#print axioms alignment

end CurrentAdditive.V42FullProductAlignment

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for axiomName in (← Lean.collectAxioms ``CurrentAdditive.V42FullProductAlignment.alignment) do
    unless allowed.contains axiomName do
      throwError "Forbidden axiom {axiomName} in full-product alignment"
  logInfo "Full-product alignment direct-consumer audit: only permitted axioms."

