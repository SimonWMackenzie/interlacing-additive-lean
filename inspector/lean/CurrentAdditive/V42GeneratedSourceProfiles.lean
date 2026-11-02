import CurrentAdditive.V42GeneratedProfileGuards
import CurrentAdditive.V39IndexedProfileCosts
import CurrentAdditive.V39IndexedReferenceProfile
import CurrentAdditive.V38IndexedMarked

/-! Replacement v42 `src:profiles`, literal generated source.  The new
dyadic explicit recipe is used at every layer.  Original list labels and
their rational weights are retained, including duplicate decoded values. -/

namespace CurrentAdditive.V42GeneratedSourceProfiles

open Paper2 Workspace.Types.CommComplexity V42Schedule
open CurrentAdditive.DeterministicIndexedMatrix

variable {X Y I : Type} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y]
  {k : ℕ} [NeZero (q₁ k)] [NeZero (q₂ k (4*k))] [NeZero (s k)]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}

def CostsAndProfiles
    (src : Sources (D := 8192) (q₁ := q₁ k) (q₂ := q₂ k (4*k)) (s := s k) μX μY)
    (μI : PositiveRationalLaw I) (R : X → Y → Bool)
    (activity : I → Fin (q₂ k (4*k)) → Option (Fin (s k)))
    (ξ₀ : SourceMatrix.Tail (s k) Y) (d : ℕ) : Prop :=
  D (Sources.A src R) = d+k ∧
  D (Sources.T src R) = d+k+(4*k+2*k) ∧
  V38RestrictionProfiles.TwoThresholdProfile (Sources.A src R)
    src.gamma.law.toFiniteLaw
    ((PositiveRationalLaw.uniform (Fin (q₁ k))).prod μX).toFiniteLaw
    (x (4*k) : ℝ) ((d+k : ℕ) : ℤ) ∧
  V38RestrictionProfiles.TwoThresholdProfile (Sources.T src R)
    src.inner.law.toFiniteLaw
    ((PositiveRationalLaw.uniform (Fin (q₂ k (4*k)))).prod src.gamma.law).toFiniteLaw
    (x (4*k) : ℝ) ((d+k+(4*k+2*k) : ℕ) : ℤ) ∧
  V38RestrictionProfiles.TwoThresholdProfile
    (V39IndexedReferenceProfile.reference src R activity ξ₀)
    (src.outer.law.prod src.gamma.law).toFiniteLaw
    (V39IndexedReferenceProfile.rowLaw src μI).toFiniteLaw
    (x (4*k) : ℝ) ((d+k+(4*k+2*k)+k : ℕ) : ℤ)

theorem costs_and_profiles
    (src : Sources (D := 8192) (q₁ := q₁ k) (q₂ := q₂ k (4*k)) (s := s k) μX μY)
    (μI : PositiveRationalLaw I) (R : X → Y → Bool)
    (activity : I → Fin (q₂ k (4*k)) → Option (Fin (s k)))
    (ξ₀ : SourceMatrix.Tail (s k) Y) (d : ℕ) (hk : 200 ≤ k)
    (hd : 2 ≤ d) (hD : D R = d)
    (hp : V38RestrictionProfiles.TwoThresholdProfile R μX.toFiniteLaw μY.toFiniteLaw
      (rho (4*k) : ℝ) (d : ℤ)) :
    CostsAndProfiles src μI R activity ξ₀ d := by
  obtain ⟨ha,hb,hρ,hx,hx1,_,_,_,_⟩ :=
    V42GeneratedProfileGuards.scalar_parameters k hk
  obtain ⟨hsa,hst,hsn,hba,hbt,hbn⟩ :=
    V42GeneratedProfileGuards.profile_guards k hk
  have hpA := V39IndexedProfiles.A_profile src R d k
    (rho (4*k) : ℝ) (x (4*k) : ℝ) 1
    hd ha hρ hx hx1 (by norm_num) hp hsa hba
  have hpT := V39IndexedProfiles.T_profile src R (d+k) (4*k+2*k)
    (x (4*k) : ℝ) 1 (by omega) hb hx hx1 (by norm_num) hpA hst hbt
  have hpN := V39IndexedReferenceProfile.reference_profile src μI R activity ξ₀
    (d+k+(4*k+2*k)) k (x (4*k) : ℝ) 1
    (by omega) ha hx hx1 (by norm_num) hpT hsn
    (by simpa only [SourceProfilesReference.templateThreshold] using hbn)
  have hq₁ : q₁ k ≤ 2^k := by
    change 2^k-2 ≤ 2^k
    exact Nat.sub_le _ _
  have hq₂ : q₂ k (4*k) ≤ 2^(4*k+2*k) := le_rfl
  have hA := V39IndexedProfiles.A_exact src R d k
    (x (4*k) : ℝ) hD hx1 hq₁ hpA
  have hT := V39IndexedProfiles.T_exact src R (d+k) (4*k+2*k)
    (x (4*k) : ℝ) hA hx1 hq₂ hpT
  exact ⟨hA,hT,hpA,hpT,hpN⟩

/-- The first q₁ list positions and three distinct tail positions need
one extra bit.  This uses the current two-threshold base profile and the
actual eight-wise marginal on the unchanged gamma labels. -/
theorem three_tail_cost
    (src : Sources (D := 8192) (q₁ := q₁ k) (q₂ := q₂ k (4*k)) (s := s k) μX μY)
    (R : X → Y → Bool) (d : ℕ) (hk : 200 ≤ k) (hd : 2 ≤ d)
    (hp : V38RestrictionProfiles.TwoThresholdProfile R μX.toFiniteLaw μY.toFiniteLaw
      (rho (4*k) : ℝ) (d : ℤ))
    (p p' : Fin (s k)) (hpp : p ≠ p')
    (Rows : Fin (q₁ k+3) → Set X) (W : Set src.gamma.Label)
    (hrow : ∀ i, 2*(s k : ℝ)*(rho (4*k) : ℝ) ≤ μX.toFiniteLaw.prob (· ∈ Rows i))
    (hW : (1/2 : ℝ) < src.gamma.law.toFiniteLaw.prob (· ∈ W)) :
    d+k+1 ≤ Compression.restrictionD
      (fun row col => R row.2 (Sources.selectedGamma src p p' col row.1))
      (ArbitraryPrefix.rowRectangle Finset.univ Rows) W := by
  have hs := (scalar_smallness k (4*k) (by omega) le_rfl).1
  obtain ⟨_,_,hρ,_,_,hsρ,_⟩ := V42GeneratedProfileGuards.scalar_parameters k hk
  have hq : 2^k+1 ≤ q₁ k+3 := by change 2^k+1 ≤ s k-2+3; unfold s at *; omega
  have hpw : (2 : ℝ)^(k+1)=2*(s k : ℝ) := by simp [s,pow_succ]; ring
  have hcount : 2^((k+1)-1)+1 ≤ (Finset.univ : Finset (Fin (q₁ k+3))).card := by
    simpa only [Nat.add_sub_cancel_right,Finset.card_univ,Fintype.card_fin] using hq
  have hrows : ∀ i ∈ (Finset.univ : Finset (Fin (q₁ k+3))),
      (2 : ℝ)^(k+1)*(rho (4*k) : ℝ) ≤ μX.toFiniteLaw.prob (· ∈ Rows i) := by
    intro i _; rw [hpw]; exact hrow i
  have hh := V38Fin2Exact.exactboost μX μY R src.gamma.law.toFiniteLaw
    (Sources.selectedGamma src p p') (Sources.selected_gamma_dwise src (by norm_num) p p' hpp)
    Finset.univ Rows W d (k+1) (rho (4*k) : ℝ) (by omega) hd hρ
    (by rw [hpw]; linarith) hp hcount hrows (by linarith)
  simpa only [Nat.add_assoc] using hh

#print axioms costs_and_profiles
#print axioms three_tail_cost

end CurrentAdditive.V42GeneratedSourceProfiles
