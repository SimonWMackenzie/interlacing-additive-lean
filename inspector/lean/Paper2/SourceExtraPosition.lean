import Paper2.SourceProjectionWitness
import Paper2.RationalRowEstimates

/-!
# The extra position at a retained source witness

Frozen v12 Section 4, `src:profiles`, final paragraph, and the usable-witness
paragraph of `src:near-full`. The dyadic row-capacity theorem applies to the
actual `q₁+3=s+1` row groups. Whole retained words are projected together,
so their correlations are preserved. The last theorem compares this literal
interlace with the original retained source rectangle using fixed surviving
representatives; no protocol lower bound is a hypothesis.
-/

namespace Paper2.SourceExtraPosition

open SourceMatrix SourceProjection SourceProjectionWitness
open Workspace.Types.CommComplexity

variable {X Y I : Type*} [Fintype X] [Fintype Y]
variable {q₁ q₂ s : ℕ}

/-- The exact extra-position estimate on an actual retained interlace.
The base profile is only a lower-bound profile, not an exact-cost premise. -/
theorem extra_position_interlace
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (d a : ℕ) (ρ : ℝ)
    (hd : 2 ≤ d) (ha : 1 ≤ a) (hρ : 0 < ρ)
    (hs : s = 2 ^ a) (hq : q₁ + 3 = s + 1)
    (hscale : 2 * (s : ℝ) * ρ ≤ 1)
    (hprofile : RestrictionProfile R μ.toFiniteLaw ν.toFiniteLaw ρ (d : ℤ))
    (U : Set (Fin (q₁ + 3) × X)) (V : Set (Fin (q₁ + 3) → Y))
    (hU : ∀ i, 2 * (s : ℝ) * ρ ≤ μ.toFiniteLaw.prob (fun u => (i, u) ∈ U))
    (hV : (1 / 2 : ℝ) < (ν.toFiniteLaw.iid (q₁ + 3)).prob (· ∈ V)) :
    d + a + 1 ≤ Compression.restrictionD (fullInterlace R (q₁ + 3)) U V := by
  classical
  have hpow : (2 : ℝ) ^ (a + 1) = 2 * (s : ℝ) := by
    rw [hs, Nat.cast_pow, Nat.cast_ofNat, pow_succ]
    ring
  have hcount : 2 ^ ((a + 1) - 1) + 1 ≤
      (Finset.univ : Finset (Fin (q₁ + 3))).card := by
    simp only [Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel]
    omega
  have hh := RationalRowEstimates.small_capacity_power μ ν R d (a + 1) (q₁ + 3)
    hd hρ (by omega) (by simpa only [hpow] using hscale) hprofile
    Finset.univ hcount U.toFinset V.toFinset
    (fun i _ => by simpa only [hpow, Set.mem_toFinset] using hU i)
    (by simpa only [Set.mem_toFinset] using (by linarith :
      (9 / 25 : ℝ) ≤ (ν.toFiniteLaw.iid (q₁ + 3)).prob (· ∈ V)))
  change d + (a + 1) ≤ Compression.restrictionD (fullInterlace R (q₁ + 3))
    (U.toFinset : Set _) (V.toFinset : Set _) at hh
  simpa only [Set.coe_toFinset, Nat.add_assoc] using hh

/-- Any injective selection of `q₁+3` positions works. In particular this
covers the first `q₁` positions and any three distinct tail positions from
`src:profiles`, while retaining the actual original whole-word set. -/
theorem word_positions_lower
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (d a : ℕ) (ρ : ℝ)
    (hd : 2 ≤ d) (ha : 1 ≤ a) (hρ : 0 < ρ)
    (hs : s = 2 ^ a) (hq : q₁ + 3 = s + 1)
    (hscale : 2 * (s : ℝ) * ρ ≤ 1)
    (hprofile : RestrictionProfile R μ.toFiniteLaw ν.toFiniteLaw ρ (d : ℤ))
    (e : Fin (q₁ + 3) → Fin (q₁ + s + 1)) (he : Function.Injective e)
    (U : Set (Fin (q₁ + 3) × X)) (W : Set (Word q₁ s Y))
    (hU : ∀ i, 2 * (s : ℝ) * ρ ≤ μ.toFiniteLaw.prob (fun u => (i, u) ∈ U))
    (hW : (1 / 2 : ℝ) < (ν.iid (q₁ + s + 1)).toFiniteLaw.prob (· ∈ W)) :
    d + a + 1 ≤ Compression.restrictionD
      (fun (i : Fin (q₁ + 3) × X) (γ : Word q₁ s Y) => R i.2 (γ (e i.1))) U W := by
  have hmass := word_projection_mass ν e he W
  have hprojected : (1 / 2 : ℝ) <
      (ν.toFiniteLaw.iid (q₁ + 3)).prob (· ∈ wordProjection e '' W) := by
    simpa only [PositiveRationalLaw.toFiniteLaw_iid] using hW.trans_le hmass
  have hl := extra_position_interlace μ ν R d a ρ hd ha hρ hs hq hscale
    hprofile U (wordProjection e '' W) hU hprojected
  exact hl.trans (restrictionD_projected_le
    (fun (i : Fin (q₁ + 3) × X) (γ : Word q₁ s Y) => R i.2 (γ (e i.1)))
    (fullInterlace R (q₁ + 3)) id (wordProjection e) U W U
    (fun _ h => h) (fun _ _ _ _ => rfl))

/-- The head projections and three source families give exactly the
per-block row thresholds of the witness interlace. -/
theorem witness_rows_mass (μ : PositiveRationalLaw X) (t : ℝ)
    (α : Fin q₂) (A : Set (Template q₁ q₂ X)) (B : Fin 3 → Set X)
    (hhead : ∀ r, t ≤ μ.toFiniteLaw.prob
      (fun u => (r, u) ∈ (fun z : Template q₁ q₂ X => z α) '' A))
    (hsource : ∀ k, t ≤ μ.toFiniteLaw.prob (· ∈ B k)) :
    ∀ i, t ≤ μ.toFiniteLaw.prob (fun u => (i, u) ∈ witnessRowsFin α A B) := by
  intro i
  rcases hi : finSumFinEquiv.symm i with r | k
  · simpa only [witnessRowsFin, Set.mem_preimage, witnessRows, hi] using hhead r
  · simpa only [witnessRowsFin, Set.mem_preimage, witnessRows, hi] using hsource k

/-- The literal interlace at a usable collision witness has the extra bit.
Distinct active positions make the selected word coordinates independent
under the ambient product law; no independence is assumed for `W`. -/
theorem witness_interlace_lower
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (d a : ℕ) (ρ : ℝ)
    (hd : 2 ≤ d) (ha : 1 ≤ a) (hρ : 0 < ρ)
    (hs : s = 2 ^ a) (hq : q₁ + 3 = s + 1)
    (hscale : 2 * (s : ℝ) * ρ ≤ 1)
    (hprofile : RestrictionProfile R μ.toFiniteLaw ν.toFiniteLaw ρ (d : ℤ))
    (α : Fin q₂) (A : Set (Template q₁ q₂ X)) (B : Fin 3 → Set X)
    (p p' : Fin s) (hpp : p ≠ p') (W : Set (Word q₁ s Y))
    (hhead : ∀ r, 2 * (s : ℝ) * ρ ≤ μ.toFiniteLaw.prob
      (fun u => (r, u) ∈ (fun z : Template q₁ q₂ X => z α) '' A))
    (hsource : ∀ k, 2 * (s : ℝ) * ρ ≤ μ.toFiniteLaw.prob (· ∈ B k))
    (hW : (1 / 2 : ℝ) < (ν.iid (q₁ + s + 1)).toFiniteLaw.prob (· ∈ W)) :
    d + a + 1 ≤ Compression.restrictionD (fullInterlace R (q₁ + 3))
      (witnessRowsFin α A B) (witnessWords p p' W) := by
  apply extra_position_interlace μ ν R d a ρ hd ha hρ hs hq hscale hprofile
    (witnessRowsFin α A B) (witnessWords p p' W)
    (witness_rows_mass μ _ α A B hhead hsource)
  simpa only [PositiveRationalLaw.toFiniteLaw_iid] using
    hW.trans_le (witness_word_mass ν p p' hpp W)

/-- The extra-bit lower bound on the originally supplied retained source
rectangle. All embeddings use surviving rows fixed before the word varies. -/
theorem witness_source_lower [Fintype I] [NeZero s]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (d a : ℕ) (ρ : ℝ) (hd : 2 ≤ d) (ha : 1 ≤ a) (hρ : 0 < ρ)
    (hs : s = 2 ^ a) (hq : q₁ + 3 = s + 1)
    (hscale : 2 * (s : ℝ) * ρ ≤ 1)
    (hprofile : RestrictionProfile R μ.toFiniteLaw ν.toFiniteLaw ρ (d : ℤ))
    (bin : Fin s) (α : Fin q₂) (A : Set (Template q₁ q₂ X)) (B : Fin 3 → Set X)
    (W : Set (Word q₁ s Y)) (i₁ i₂ i₀ : I) (p p' : Fin s) (hpp : p ≠ p')
    (h₁ : activity i₁ α = some p) (h₂ : activity i₂ α = some p')
    (h₀ : activity i₀ α = none)
    (U : Set (TaggedColumn q₁ q₂ s Y)) (V : Set (RawRow q₁ q₂ s X I))
    (hA : ∀ z ∈ A, Sum.inl (bin, z) ∈ V)
    (hB : ∀ k u, u ∈ B k →
      Sum.inr (SourceProjectionDiagonal.collisionItem i₁ i₂ i₀ k, u) ∈ V)
    (hwords : ∀ γ ∈ W, TaggedColumn.diagonal (α, γ) ∈ U)
    (hhead : ∀ r, 2 * (s : ℝ) * ρ ≤ μ.toFiniteLaw.prob
      (fun u => (r, u) ∈ (fun z : Template q₁ q₂ X => z α) '' A))
    (hsource : ∀ k, 2 * (s : ℝ) * ρ ≤ μ.toFiniteLaw.prob (· ∈ B k))
    (hW : (1 / 2 : ℝ) < (ν.iid (q₁ + s + 1)).toFiniteLaw.prob (· ∈ W)) :
    d + a + 1 ≤ Compression.restrictionD (N R activity ξ₀) U V :=
  (witness_interlace_lower μ ν R d a ρ hd ha hρ hs hq hscale hprofile
    α A B p p' hpp W hhead hsource hW).trans
    (witness_interlace_D_le R activity ξ₀ bin α A B W i₁ i₂ i₀ p p'
      h₁ h₂ h₀ U V hA hB hwords)

end Paper2.SourceExtraPosition
