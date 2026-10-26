import CurrentAdditive.V39FullScheduledSource
import CurrentAdditive.V39ThreeTail
import CurrentAdditive.V39FullCutoff

/-!
The actual two-threshold full-product source profiles on every input above
the proved public cutoff. The cutoff theorem is consumed at its exact
positive graph parameters; it is not an assumed eventual test pass.
-/

namespace CurrentAdditive.V39SourceProfilesAllLarge

open Workspace.Types.CommComplexity Paper2 V38Schedule
open Paper2.SourceMatrix
open CurrentAdditive.EdgeSourceMatrix CurrentAdditive.V38Matrix

variable {X Y V E : Type*} [Fintype X] [Fintype Y] [Fintype V] [Fintype E]
variable {q₁ q₂ s : ℕ}

theorem costs_and_profiles [Nonempty V] [NeZero q₁] [NeZero q₂] [NeZero s]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool)
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 4 ≤ s) (r : ℕ)
    (hq : q₂=EdgeSource.sourceQ0 (Fin (4*s)) E*r)
    (ξ₀ : Tail s Y) (d : ℕ) (hd : 3 ≤ d)
    (γ : ℚ) (Δ n m : ℕ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hn : 0 < n)
    (hnm : n ≤ 2*m) (hdeg : 2*m ≤ Δ*n)
    (hlarge : V39FullCutoff.sourceCutoff γ Δ ≤ n)
    (hS : s=fullS (Nat.clog 2 n))
    (hQ₁ : q₁=fullQ₁ (Nat.clog 2 n))
    (hQ₂ : q₂=fullQ₂ (Nat.clog 2 n))
    (hp : V38RestrictionProfiles.TwoThresholdProfile R
      μ.toFiniteLaw ν.toFiniteLaw ((fullRho (Nat.clog 2 n) : ℚ) : ℝ) (d : ℤ))
    (hD : D R=d) :
    let a := 16+ell (Nat.clog 2 n)
    let b := Nat.clog 2 n+2*a
    D (M₁ (q₁:=q₁) (s:=s) R)=d+a ∧
    D (T (q₁:=q₁) (q₂:=q₂) (s:=s) R)=d+a+b ∧
    V38RestrictionProfiles.TwoThresholdProfile
      (fun γ z => M₁ (q₁:=q₁) (s:=s) R z γ)
      (ν.iid (q₁+s+1)).toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μ).toFiniteLaw
      ((fullX (Nat.clog 2 n) : ℚ) : ℝ) ((d+a : ℕ) : ℤ) ∧
    V38RestrictionProfiles.TwoThresholdProfile (T (q₁:=q₁) (q₂:=q₂) (s:=s) R)
      (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw
      (SourceLaws.outerLaw ν q₁ q₂ s).toFiniteLaw
      ((fullX (Nat.clog 2 n) : ℚ) : ℝ) ((d+a+b : ℕ) : ℤ) ∧
    V38RestrictionProfiles.TwoThresholdProfile
      (fun Z k => V38Matrix.matrix order edge (by omega : 3 ≤ s) r hq R ξ₀ (.inl Z) k)
      (SourceLaws.rawLaw ν q₁ q₂ s).toFiniteLaw
      (columnLaw (q₁:=q₁) (q₂:=q₂) (s:=s) (V:=V) μ hs).toFiniteLaw
      ((fullX (Nat.clog 2 n) : ℚ) : ℝ) ((d+a+b+a : ℕ) : ℤ) := by
  have ht := V39FullCutoff.fullPublicTests_all_large γ Δ n m hγ hΔ hn hnm hdeg hlarge
  exact V39FullScheduledSource.costs_and_profiles μ ν R order edge hs r hq ξ₀ d hd
    (fullConstant γ Δ n m) (sourceDeltaV γ Δ n m) (sourceZeta γ) (Nat.clog 2 n) m
    hS hQ₁ hQ₂ ht.1 hp hD

/-- The same public cutoff supplies the exact capacity condition used by
the three-tail argument. This is a scalar consequence of its actual tests. -/
theorem row_capacity (γ : ℚ) (Δ n m : ℕ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hn : 0 < n)
    (hnm : n ≤ 2*m) (hdeg : 2*m ≤ Δ*n)
    (hlarge : V39FullCutoff.sourceCutoff γ Δ ≤ n) :
    2*(fullS (Nat.clog 2 n) : ℝ)*((fullRho (Nat.clog 2 n) : ℚ) : ℝ) ≤ 1 := by
  have ht := (V39FullCutoff.fullPublicTests_all_large γ Δ n m hγ hΔ hn hnm hdeg hlarge).1
  rcases ht with ⟨hs,_,_,h4,_⟩
  change 256 ≤ fullS (Nat.clog 2 n) at hs
  change 4*(fullS (Nat.clog 2 n) : ℚ)^2*fullRho (Nat.clog 2 n) ≤ 1 at h4
  have hsR : (256 : ℝ) ≤ fullS (Nat.clog 2 n) := by exact_mod_cast hs
  have h4R : 4*(fullS (Nat.clog 2 n) : ℝ)^2*
      ((fullRho (Nat.clog 2 n) : ℚ) : ℝ) ≤ 1 := by exact_mod_cast h4
  have hρ : (0 : ℝ) ≤ ((fullRho (Nat.clog 2 n) : ℚ) : ℝ) := by
    norm_num only [fullRho,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat]
    positivity
  have hm := mul_nonneg
    (show 0 ≤ 4*(fullS (Nat.clog 2 n) : ℝ)-2 by linarith)
    (show 0 ≤ (fullS (Nat.clog 2 n) : ℝ)*
      ((fullRho (Nat.clog 2 n) : ℚ) : ℝ) by positivity)
  nlinarith only [hm,h4R]

/-- The selected three-tail conclusion above the same public cutoff.
Only the original two-threshold profile and actual retained row/word
sets are inputs; there is no separate capacity or protocol-bound premise. -/
theorem three_tail
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (d : ℕ) (hd : 2 ≤ d)
    (γ : ℚ) (Δ n m : ℕ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hn : 0 < n)
    (hnm : n ≤ 2*m) (hdeg : 2*m ≤ Δ*n)
    (hlarge : V39FullCutoff.sourceCutoff γ Δ ≤ n)
    (hS : s=fullS (Nat.clog 2 n))
    (hQ₁ : q₁=fullQ₁ (Nat.clog 2 n))
    (hp : V38RestrictionProfiles.TwoThresholdProfile R
      μ.toFiniteLaw ν.toFiniteLaw ((fullRho (Nat.clog 2 n) : ℚ) : ℝ) (d : ℤ))
    (U : Set (Fin (q₁+3) × X)) (W : Set (Fin (q₁+3) → Y))
    (hU : ∀ i, 2*(s : ℝ)*((fullRho (Nat.clog 2 n) : ℚ) : ℝ) ≤
      μ.toFiniteLaw.prob (fun x => (i,x) ∈ U))
    (hW : (1/2 : ℝ) < (ν.toFiniteLaw.iid (q₁+3)).prob (· ∈ W)) :
    d+(16+ell (Nat.clog 2 n))+1 ≤
      Compression.restrictionD (fullInterlace R (q₁+3)) U W := by
  have hs256 := fullS_ge_256 (Nat.clog 2 n)
  have hq : q₁+3=s+1 := by rw [hS,hQ₁]; unfold fullQ₁; omega
  have hρ : (0 : ℝ) < ((fullRho (Nat.clog 2 n) : ℚ) : ℝ) := by
    norm_num only [fullRho,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat]
    positivity
  have hscale := row_capacity γ Δ n m hγ hΔ hn hnm hdeg hlarge
  rw [← hS] at hscale
  exact V39ThreeTail.interlace_lower μ ν R d (16+ell (Nat.clog 2 n))
    ((fullRho (Nat.clog 2 n) : ℚ) : ℝ) hd hρ
    (by simpa only [fullS] using hS) hq hscale hp U W hU hW

/-- Original whole-word form of the selected first-heads/three-tails bound.
The same retained word is used for every row after the joint projection. -/
theorem word_positions
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (d : ℕ) (hd : 2 ≤ d)
    (γ : ℚ) (Δ n m : ℕ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hn : 0 < n)
    (hnm : n ≤ 2*m) (hdeg : 2*m ≤ Δ*n)
    (hlarge : V39FullCutoff.sourceCutoff γ Δ ≤ n)
    (hS : s=fullS (Nat.clog 2 n))
    (hQ₁ : q₁=fullQ₁ (Nat.clog 2 n))
    (hp : V38RestrictionProfiles.TwoThresholdProfile R
      μ.toFiniteLaw ν.toFiniteLaw ((fullRho (Nat.clog 2 n) : ℚ) : ℝ) (d : ℤ))
    (e : Fin (q₁+3) → Fin (q₁+s+1)) (he : Function.Injective e)
    (U : Set (Fin (q₁+3) × X)) (W : Set (Word q₁ s Y))
    (hU : ∀ i, 2*(s : ℝ)*((fullRho (Nat.clog 2 n) : ℚ) : ℝ) ≤
      μ.toFiniteLaw.prob (fun x => (i,x) ∈ U))
    (hW : (1/2 : ℝ) < (ν.iid (q₁+s+1)).toFiniteLaw.prob (· ∈ W)) :
    d+(16+ell (Nat.clog 2 n))+1 ≤ Compression.restrictionD
      (fun (i : Fin (q₁+3) × X) (z : Word q₁ s Y) => R i.2 (z (e i.1))) U W := by
  have hs256 := fullS_ge_256 (Nat.clog 2 n)
  have hq : q₁+3=s+1 := by rw [hS,hQ₁]; unfold fullQ₁; omega
  have hρ : (0 : ℝ) < ((fullRho (Nat.clog 2 n) : ℚ) : ℝ) := by
    norm_num only [fullRho,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat]
    positivity
  have hscale := row_capacity γ Δ n m hγ hΔ hn hnm hdeg hlarge
  rw [← hS] at hscale
  exact V39ThreeTail.word_positions_lower μ ν R d (16+ell (Nat.clog 2 n))
    ((fullRho (Nat.clog 2 n) : ℚ) : ℝ) hd hρ
    (by simpa only [fullS] using hS) hq hscale hp e he U W hU hW

#print axioms costs_and_profiles
#print axioms row_capacity
#print axioms three_tail
#print axioms word_positions

end CurrentAdditive.V39SourceProfilesAllLarge
