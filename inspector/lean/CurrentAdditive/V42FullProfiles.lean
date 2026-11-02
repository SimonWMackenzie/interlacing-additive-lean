import CurrentAdditive.V42FullSuccessor
import CurrentAdditive.V39SourceProfilesAllLarge

/-! Full-product source A,T,Nref at the new v42 block threshold.
The literal source widths s,q1,q2 are unchanged, so the checked source
profiles at the smaller 2^-10L threshold specialize to rho^8 exactly.
No old internal/final interlace or old endpoint is invoked. -/
namespace CurrentAdditive.V42FullProfiles
open Paper2 Paper2.SourceMatrix Workspace.Types.CommComplexity
open V42FullSuccessor V42PublicSchedule
open CurrentAdditive.EdgeSourceMatrix
set_option maxHeartbeats 2000000

theorem q₂_old (L : ℕ) : fullQ₂ L=V38Schedule.fullQ₂ L := by
  rw [V42FullSuccessor.fullQ₂_mul]
  rfl

theorem x_old_le (L : ℕ) : V38Schedule.fullX L≤V42Schedule.x L := by
  exact V42Schedule.reciprocal_le (10*L) (8*L) (by omega)

theorem profile_row_mono {A B : Type*} [Fintype A] [Fintype B]
    (F : A → B → Bool) (μ : FiniteLaw A) (ν : FiniteLaw B)
    (x y : ℝ) (d : ℤ) (hxy : x≤y)
    (hp : V38RestrictionProfiles.TwoThresholdProfile F μ ν x d) :
    V38RestrictionProfiles.TwoThresholdProfile F μ ν y d := by
  intro j U V hU hV
  exact hp j U V (hxy.trans hU) hV

variable {X Y V E : Type*} [Fintype X] [Fintype Y] [Fintype V] [Fintype E]
  [Nonempty V]

theorem profiles
    (L : ℕ) (hL : L=Nat.clog 2 (Fintype.card V))
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y) (R : X → Y → Bool)
    (order : Items (fullS L) V ≃ Fin (Fintype.card (Items (fullS L) V)))
    (edge : E → Bool → V) (rep : ℕ)
    (hq : fullQ₂ L=EdgeSource.sourceQ0 (Fin (4*fullS L)) E*rep)
    (ξ₀ : Tail (fullS L) Y) (d : ℕ) (hd : 3≤d)
    (γ : ℚ) (Δ : ℕ) (hγ : 0<γ) (hΔ : 0<Δ)
    (hnm : Fintype.card V≤2*Fintype.card E)
    (hdeg : 2*Fintype.card E≤Δ*Fintype.card V)
    (hlarge : V39FullCutoff.sourceCutoff γ Δ≤Fintype.card V)
    (hp : V38RestrictionProfiles.TwoThresholdProfile R μ.toFiniteLaw ν.toFiniteLaw
      (V42Schedule.rho L:ℝ) (d:ℤ)) (hD : D R=d) :
    V38RestrictionProfiles.TwoThresholdProfile
      (fun γ z => M₁ (q₁:=fullQ₁ L) (s:=fullS L) R z γ)
      (ν.iid (fullQ₁ L+fullS L+1)).toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin (fullQ₁ L))).prod μ).toFiniteLaw
      (V42Schedule.x L:ℝ) ((d+fullExponent L:ℕ):ℤ) ∧
    V38RestrictionProfiles.TwoThresholdProfile
      (T (q₁:=fullQ₁ L) (q₂:=fullQ₂ L) (s:=fullS L) R)
      (SourceLaws.templateLaw μ (fullQ₁ L) (fullQ₂ L)).toFiniteLaw
      (SourceLaws.outerLaw ν (fullQ₁ L) (fullQ₂ L) (fullS L)).toFiniteLaw
      (V42Schedule.x L:ℝ) ((d+fullExponent L+(L+2*fullExponent L):ℕ):ℤ) ∧
    V38RestrictionProfiles.TwoThresholdProfile
      (fun Z k => V38Matrix.matrix order edge (by have := fullS_ge_256 L; omega)
        rep hq R ξ₀ (.inl Z) k)
      (SourceLaws.rawLaw ν (fullQ₁ L) (fullQ₂ L) (fullS L)).toFiniteLaw
      (V38Matrix.columnLaw (q₁:=fullQ₁ L) (q₂:=fullQ₂ L) (s:=fullS L)
        (V:=V) μ (by have := fullS_ge_256 L; omega)).toFiniteLaw
      (V42Schedule.x L:ℝ) ((d+fullExponent L+(L+2*fullExponent L)+fullExponent L:ℕ):ℤ) := by
  subst L
  let L := Nat.clog 2 (Fintype.card V)
  have hpold : V38RestrictionProfiles.TwoThresholdProfile R μ.toFiniteLaw ν.toFiniteLaw
      ((V38Schedule.fullRho (Nat.clog 2 (Fintype.card V)):ℚ):ℝ) (d:ℤ) := by
    simpa only [V38Schedule.fullRho,V42Schedule.rho] using hp
  have hh := V39SourceProfilesAllLarge.costs_and_profiles μ ν R order edge
    (by have hh := fullS_ge_256 (Nat.clog 2 (Fintype.card V)); omega) rep hq ξ₀ d hd γ Δ
    (Fintype.card V) (Fintype.card E) hγ hΔ Fintype.card_pos hnm hdeg hlarge
    rfl rfl (q₂_old L) hpold hD
  dsimp only at hh
  have hx : ((V38Schedule.fullX L:ℚ):ℝ)≤(V42Schedule.x L:ℝ) := by
    exact_mod_cast x_old_le L
  exact ⟨profile_row_mono _ _ _ _ _ _ hx hh.2.2.1,
    profile_row_mono _ _ _ _ _ _ hx hh.2.2.2.1,
    profile_row_mono _ _ _ _ _ _ hx hh.2.2.2.2⟩

#print axioms profiles
end CurrentAdditive.V42FullProfiles
