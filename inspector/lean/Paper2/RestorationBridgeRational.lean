import Paper2.RestorationBridge

/-!
# Restoration for positive rational laws

Frozen v12 Appendix A, `cl:bridge` and `cl:rational-laws`. The uniform
restoration theorem is transported through explicit duplicate labels.
Every original retained tuple set is lifted as one set, including all its
correlations. The regenerated profile uses the product law on tuples and
the independent uniform selector on the other side.
-/

namespace Paper2.RestorationBridge

open Workspace.Types.CommComplexity

variable {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]

theorem uniformFin_prod_uniform (q : ℕ) (hq : 0 < q) :
    (FiniteLaw.uniformFin q hq).prod (FiniteLaw.uniform X) =
      @FiniteLaw.uniform (Fin q × X) _ (by exact ⟨⟨⟨0, hq⟩, Classical.choice inferInstance⟩⟩) := by
  apply FiniteLaw.eq_of_weight_eq
  funext z
  simp [FiniteLaw.prod, FiniteLaw.uniformFin, FiniteLaw.uniform, mul_inv_rev, mul_comm]

/-- The exact rational-law restoration profile, with the output laws and
both full indexed carriers explicit. No robustness assumption is added. -/
theorem rational_profile (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (F : X → Y → Bool) (C r b : ℕ) (θ δ : ℝ)
    (hC : 3 ≤ C) (hb : 1 ≤ b)
    (hθ : 0 < θ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 64)
    (hQ : 80 * (b : ℝ) ≤ (2 : ℝ) ^ r * δ)
    (hscale : (2 : ℝ) ^ r * θ < 1 / 20)
    (hnear : RestrictionLowerBound F μ.toFiniteLaw ν.toFiniteLaw θ (1 - δ) (C : ℤ))
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw θ ((C : ℤ) - 1)) :
    RestrictionProfile (restored F r) (ν.toFiniteLaw.iid (2 ^ r))
      ((FiniteLaw.uniformFin (2 ^ r) (Nat.two_pow_pos r)).prod μ.toFiniteLaw)
      ((2 : ℝ) ^ (-(b : ℝ))) ((C + r : ℕ) : ℤ) := by
  let M : μ.Copies → ν.Copies → Bool := fun x y => F (μ.forget x) (ν.forget y)
  have hn : RestrictionLowerBound M (FiniteLaw.uniform _) (FiniteLaw.uniform _)
      θ (1 - δ) (C : ℤ) := by
    simpa only [RationalSeparation.copies_uniform_eq] using
      (rationalCopies_restrictionLowerBound_iff μ ν F θ (1 - δ) (C : ℤ)).mpr hnear
  have hp : RestrictionProfile M (FiniteLaw.uniform _) (FiniteLaw.uniform _)
      θ ((C : ℤ) - 1) := by
    simpa only [RationalSeparation.copies_uniform_eq] using
      (rationalCopies_profile_iff μ ν F θ ((C : ℤ) - 1)).mpr hprofile
  have hu := uniform_profile M C r b θ δ hC hb hθ hδ hδ1 hQ hscale hn hp
  have hrows : (FiniteLaw.uniform (Fin (2 ^ r) → ν.Copies)).PushesTo
      (ν.toFiniteLaw.iid (2 ^ r)) (ν.forgetTuple (2 ^ r)) :=
    RationalSeparation.tuples_prob_preimage ν (2 ^ r)
  have hcols : (FiniteLaw.uniform (Fin (2 ^ r) × μ.Copies)).PushesTo
      ((FiniteLaw.uniformFin (2 ^ r) (Nat.two_pow_pos r)).prod μ.toFiniteLaw)
      (μ.forgetBlock (2 ^ r)) := by
    rw [← uniformFin_prod_uniform (2 ^ r) (Nat.two_pow_pos r),
      ← RationalSeparation.copies_uniform_eq]
    exact μ.uniformCopies_block_prob_preimage (2 ^ r)
      (FiniteLaw.uniformFin (2 ^ r) (Nat.two_pow_pos r))
  exact (restrictionProfile_pullback_iff (restored F r)
    (ν.toFiniteLaw.iid (2 ^ r))
    ((FiniteLaw.uniformFin (2 ^ r) (Nat.two_pow_pos r)).prod μ.toFiniteLaw)
    (FiniteLaw.uniform (Fin (2 ^ r) → ν.Copies))
    (FiniteLaw.uniform (Fin (2 ^ r) × μ.Copies))
    (ν.forgetTuple (2 ^ r)) (μ.forgetBlock (2 ^ r)) hrows hcols
    (ν.forgetTuple_surjective (2 ^ r)) (μ.forgetBlock_surjective (2 ^ r))
    ((2 : ℝ) ^ (-(b : ℝ))) ((C + r : ℕ) : ℤ)).mp hu

/-- Testing a profile on the entire rectangle gives its top full-matrix
lower bound, with no assumptions about singleton masses. -/
theorem profile_full_lower (F : X → Y → Bool) (μ : FiniteLaw X) (ν : FiniteLaw Y)
    (ρ : ℝ) (c : ℕ) (hρ : ρ ≤ 1) (hp : RestrictionProfile F μ ν ρ (c : ℤ)) :
    c ≤ D F := by
  classical
  have h := hp ⟨0, by decide⟩ Set.univ Set.univ
    (by simpa using hρ) (by norm_num)
  have heq : Compression.restrictionD F Set.univ Set.univ = D F := by
    have hh := pullback_D_eq_of_surjective F Subtype.val Subtype.val
      (fun x => ⟨⟨x, Set.mem_univ x⟩, rfl⟩)
      (fun y => ⟨⟨y, Set.mem_univ y⟩, rfl⟩)
    exact hh
  simpa only [Fin.val_zero, Nat.cast_zero, sub_zero, heq, Nat.cast_le] using h

/-- Full T40 lower/upper conclusion. The base parameter equals the actual
base cost only here; the restriction theorem above needs merely the base
lower bounds. Width leastness is not needed, so this includes the least
admissible power of two specified in the manuscript. -/
theorem rational_restoration (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (F : X → Y → Bool) (r b : ℕ) (θ δ : ℝ)
    (hC : 3 ≤ D F) (hb : 1 ≤ b)
    (hθ : 0 < θ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 64)
    (hQ : 80 * (b : ℝ) ≤ (2 : ℝ) ^ r * δ)
    (hscale : (2 : ℝ) ^ r * θ < 1 / 20)
    (hnear : RestrictionLowerBound F μ.toFiniteLaw ν.toFiniteLaw
      θ (1 - δ) (D F : ℤ))
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw θ ((D F : ℤ) - 1)) :
    D (restored F r) = D F + r ∧
      RestrictionProfile (restored F r) (ν.toFiniteLaw.iid (2 ^ r))
        ((FiniteLaw.uniformFin (2 ^ r) (Nat.two_pow_pos r)).prod μ.toFiniteLaw)
        ((2 : ℝ) ^ (-(b : ℝ))) ((D F + r : ℕ) : ℤ) := by
  have hp := rational_profile μ ν F (D F) r b θ δ hC hb hθ hδ hδ1 hQ hscale
    hnear hprofile
  refine ⟨le_antisymm (upper F r (D F) le_rfl) ?_, hp⟩
  exact profile_full_lower (restored F r) _ _ _ _
    (dyadic_threshold_lt_one b hb).le hp

theorem restored_cardinalities (F : X → Y → Bool) (r : ℕ) :
    Fintype.card (Fin (2 ^ r) → Y) = (Fintype.card Y) ^ (2 ^ r) ∧
      Fintype.card (Fin (2 ^ r) × X) = 2 ^ r * Fintype.card X := by simp

end Paper2.RestorationBridge
