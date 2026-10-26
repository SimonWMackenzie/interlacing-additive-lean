import CurrentAdditive.V39TwoCopyBundleFin2
import CurrentAdditive.V39FullProductSpecialization
import Paper2.RestorationBridgeRational

/-! Selected v39 cl:bridge for literal full iid tuples and the current
Fin 2 profile. The inherited first-bit defect induction is supplied with
its three two-copy bounds by V39TwoCopyBundleFin2; no third base-profile
threshold or generated-source width budget is assumed. -/

namespace CurrentAdditive.V39FullIidRestoration

open Paper2 Paper2.RestorationBridge

open Workspace.Types.CommComplexity Workspace.Types.Interlace

variable {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]

/-- The restored matrix has the original column tuples as its rows. -/
def restored (F : X → Y → Bool) (r : ℕ) :
    (Fin (2 ^ r) → Y) → (Fin (2 ^ r) × X) → Bool :=
  fun z a => fullInterlace F (2 ^ r) a z

/-- The lower bounds hold on every actual retained rectangle of
the interlace. Retained columns may be an arbitrary correlated set. -/
theorem uniform_retained (F : X → Y → Bool) (C r b j : ℕ) (θ δ : ℝ)
    (hC : 3 ≤ C) (hb : 1 ≤ b) (hj : j ≤ 2)
    (hθ : 0 < θ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 64)
    (hQ : 80 * (b : ℝ) ≤ (2 : ℝ) ^ r * δ)
    (hscale : (2 : ℝ) ^ r * θ < 1 / 20)
    (hnear : RestrictionLowerBound F (FiniteLaw.uniform X) (FiniteLaw.uniform Y)
      θ (1 - δ) (C : ℤ))
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile F (FiniteLaw.uniform X) (FiniteLaw.uniform Y)
      θ ((C : ℤ) - 1))
    (R : Finset (Fin (2 ^ r) × X)) (K : Finset (Fin (2 ^ r) → Y))
    (hR : (3 / 5 : ℝ) / 2 ^ j ≤ (FiniteLaw.uniform _).prob (· ∈ R))
    (hK : (2 : ℝ) ^ (-(b : ℝ)) ≤ (FiniteLaw.uniform _).prob (· ∈ K)) :
    C + (r - j) ≤ D (NPCC.subgame (fullInterlace F (2 ^ r)) R K) := by
  have hθ1 := theta_upper r θ hθ hscale
  have hfamily : C ≤ ClassicalRows.restrictionCost F 1 θ (1 - δ) := by
    exact_mod_cast ClassicalSeparation.oneCopy_family_lowerBound F θ (1 - δ)
      (C : ℤ) (by linarith) (by linarith) hnear
  obtain ⟨hp, hcount⟩ := entry_parameters r b (Fintype.card X) θ δ hb
    Fintype.card_pos hθ hδ hδ1 hQ hscale j hj
  have hRcard := (FiniteLaw.le_uniform_prob_iff R ((3 / 5 : ℝ) / 2 ^ j)).mp hR
  have hKcard := (FiniteLaw.le_uniform_prob_iff K ((2 : ℝ) ^ (-(b : ℝ)))).mp hK
  apply EthBridge.theorem_two_V F C r j θ (3 / 5) (δ * Real.log 2)
    ((2 : ℝ) ^ (-(b : ℝ))) (exponent_lower r b δ hb hδ1 hQ) hj
    (dyadic_threshold_pos b) (dyadic_threshold_lt_one b hb)
    (EthBridge.package_row_scale r j θ (1 / 10) hθ (by norm_num)
      (by norm_num at *; exact hscale))
    hθ hθ1 (by norm_num) (by norm_num)
    (mul_pos hδ (Real.log_pos (by norm_num))) Fintype.card_pos Fintype.card_pos hC
    (DefectLogMargin.natural_log_margin hδ1)
    (DefectInduction.near_full_input F C θ δ hθ hθ1 hδ hδ1 hfamily)
    (CurrentAdditive.V39TwoCopyBundleFin2.two_copy_input F C hC θ hθ hθ1 hprofile) hp hcount R K
  · simpa only [Fintype.card_prod, Fintype.card_fin] using hRcard
  · simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using hKcard

/-- Source `cl:bridge`: transposition turns the two current row-density
tests into the regenerated two-threshold profile. -/
theorem uniform_profile (F : X → Y → Bool) (C r b : ℕ) (θ δ : ℝ)
    (hC : 3 ≤ C) (hb : 1 ≤ b)
    (hθ : 0 < θ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 64)
    (hQ : 80 * (b : ℝ) ≤ (2 : ℝ) ^ r * δ)
    (hscale : (2 : ℝ) ^ r * θ < 1 / 20)
    (hnear : RestrictionLowerBound F (FiniteLaw.uniform X) (FiniteLaw.uniform Y)
      θ (1 - δ) (C : ℤ))
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile F (FiniteLaw.uniform X) (FiniteLaw.uniform Y)
      θ ((C : ℤ) - 1)) :
    V38RestrictionProfiles.TwoThresholdProfile (restored F r) (FiniteLaw.uniform _) (FiniteLaw.uniform _)
      ((2 : ℝ) ^ (-(b : ℝ))) ((C + r : ℕ) : ℤ) := by
  classical
  intro j U V hU hV
  have hV' : (3 / 5 : ℝ) / 2 ^ j.val ≤
      (FiniteLaw.uniform _).prob (· ∈ V.toFinset) := by
    simpa only [Set.mem_toFinset, one_div, inv_pow, div_eq_mul_inv, one_mul] using hV
  have hU' : (2 : ℝ) ^ (-(b : ℝ)) ≤
      (FiniteLaw.uniform _).prob (· ∈ U.toFinset) := by simpa using hU
  have hl := uniform_retained F C r b j.val θ δ hC hb (by omega)
    hθ hδ hδ1 hQ hscale hnear hprofile V.toFinset U.toFinset hV' hU'
  have heq : D (NPCC.subgame (fullInterlace F (2 ^ r)) V.toFinset U.toFinset) =
      Compression.restrictionD (restored F r) U V := by
    change Compression.restrictionD (fullInterlace F (2 ^ r))
      (V.toFinset : Set _) (U.toFinset : Set _) = _
    simp only [Set.coe_toFinset]
    unfold Compression.restrictionD restored
    exact (transpose_D _).symm
  rw [heq] at hl
  have hjr : j.val ≤ r := by have := exponent_lower r b δ hb hδ1 hQ; omega
  have hlZ : ((C + (r - j.val) : ℕ) : ℤ) ≤
      (Compression.restrictionD (restored F r) U V : ℤ) := by exact_mod_cast hl
  simpa only [Nat.cast_add, Nat.cast_sub hjr, add_sub_assoc] using hlZ

/-- The selector protocol supplies the upper bound independently of all
lower-bound hypotheses. -/
theorem upper (F : X → Y → Bool) (r U : ℕ) (hU : D F ≤ U) :
    D (restored F r) ≤ U + r := by
  have hh := fullInterlace_two_pow_D_le F r
  have heq : D (restored F r) = D (fullInterlace F (2 ^ r)) := transpose_D _
  rw [heq]
  omega


theorem rational_profile (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (F : X → Y → Bool) (C r b : ℕ) (θ δ : ℝ)
    (hC : 3 ≤ C) (hb : 1 ≤ b)
    (hθ : 0 < θ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 64)
    (hQ : 80 * (b : ℝ) ≤ (2 : ℝ) ^ r * δ)
    (hscale : (2 : ℝ) ^ r * θ < 1 / 20)
    (hnear : RestrictionLowerBound F μ.toFiniteLaw ν.toFiniteLaw θ (1 - δ) (C : ℤ))
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile F μ.toFiniteLaw ν.toFiniteLaw θ ((C : ℤ) - 1)) :
    V38RestrictionProfiles.TwoThresholdProfile (restored F r) (ν.toFiniteLaw.iid (2 ^ r))
      ((FiniteLaw.uniformFin (2 ^ r) (Nat.two_pow_pos r)).prod μ.toFiniteLaw)
      ((2 : ℝ) ^ (-(b : ℝ))) ((C + r : ℕ) : ℤ) := by
  let M : μ.Copies → ν.Copies → Bool := fun x y => F (μ.forget x) (ν.forget y)
  have hn : RestrictionLowerBound M (FiniteLaw.uniform _) (FiniteLaw.uniform _)
      θ (1 - δ) (C : ℤ) := by
    simpa only [RationalSeparation.copies_uniform_eq] using
      (rationalCopies_restrictionLowerBound_iff μ ν F θ (1 - δ) (C : ℤ)).mpr hnear
  have hp : V38RestrictionProfiles.TwoThresholdProfile M (FiniteLaw.uniform _) (FiniteLaw.uniform _)
      θ ((C : ℤ)-1) := by
    intro j
    simpa only [RationalSeparation.copies_uniform_eq] using
      (rationalCopies_restrictionLowerBound_iff μ ν F θ
        ((3/5 : ℝ)*(1/2 : ℝ)^j.val) (((C : ℤ)-1)-(j.val : ℤ))).mpr (hprofile j)
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
  exact (CurrentAdditive.V39FullProductSources.twoThreshold_pullback_iff (restored F r)
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
    (ρ : ℝ) (c : ℕ) (hρ : ρ ≤ 1) (hp : V38RestrictionProfiles.TwoThresholdProfile F μ ν ρ (c : ℤ)) :
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
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile F μ.toFiniteLaw ν.toFiniteLaw θ ((D F : ℤ) - 1)) :
    D (restored F r) = D F + r ∧
      V38RestrictionProfiles.TwoThresholdProfile (restored F r) (ν.toFiniteLaw.iid (2 ^ r))
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


#print axioms uniform_retained
#print axioms uniform_profile
#print axioms rational_profile
#print axioms rational_restoration

end CurrentAdditive.V39FullIidRestoration
