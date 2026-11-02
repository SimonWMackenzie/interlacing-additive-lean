import Paper2.RestorationBridgeParameters
import Paper2.RationalSeparationDescent
import Paper2.InterlaceProtocol

/-!
# Restoration by interlacing and transposition

Frozen v12 Appendix A, `cl:bridge`. Arbitrary retained rows first force
enough well populated blocks. The inherited `theorem_two_V` then projects
the actual retained columns to those blocks and applies the checked
first-bit induction. Its numerical hypotheses are discharged here from
the source's explicit constants, rather than assumed as a profile.
-/

namespace Paper2.RestorationBridge

open Workspace.Types.CommComplexity Workspace.Types.Interlace

variable {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]

/-- The restored matrix has the original column tuples as its rows. -/
def restored (F : X → Y → Bool) (r : ℕ) :
    (Fin (2 ^ r) → Y) → (Fin (2 ^ r) × X) → Bool :=
  fun z a => fullInterlace F (2 ^ r) a z

/-- All three lower bounds hold on every actual retained rectangle of
the interlace. Retained columns may be an arbitrary correlated set. -/
theorem uniform_retained (F : X → Y → Bool) (C r b j : ℕ) (θ δ : ℝ)
    (hC : 3 ≤ C) (hb : 1 ≤ b) (hj : j ≤ 2)
    (hθ : 0 < θ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 64)
    (hQ : 80 * (b : ℝ) ≤ (2 : ℝ) ^ r * δ)
    (hscale : (2 : ℝ) ^ r * θ < 1 / 20)
    (hnear : RestrictionLowerBound F (FiniteLaw.uniform X) (FiniteLaw.uniform Y)
      θ (1 - δ) (C : ℤ))
    (hprofile : RestrictionProfile F (FiniteLaw.uniform X) (FiniteLaw.uniform Y)
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
    (DefectInduction.two_copy_input F C hC θ hθ hθ1 hprofile) hp hcount R K
  · simpa only [Fintype.card_prod, Fintype.card_fin] using hRcard
  · simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using hKcard

/-- Source `cl:bridge`: transposition turns the three arbitrary row-density
tests into the regenerated three-rung profile. -/
theorem uniform_profile (F : X → Y → Bool) (C r b : ℕ) (θ δ : ℝ)
    (hC : 3 ≤ C) (hb : 1 ≤ b)
    (hθ : 0 < θ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 64)
    (hQ : 80 * (b : ℝ) ≤ (2 : ℝ) ^ r * δ)
    (hscale : (2 : ℝ) ^ r * θ < 1 / 20)
    (hnear : RestrictionLowerBound F (FiniteLaw.uniform X) (FiniteLaw.uniform Y)
      θ (1 - δ) (C : ℤ))
    (hprofile : RestrictionProfile F (FiniteLaw.uniform X) (FiniteLaw.uniform Y)
      θ ((C : ℤ) - 1)) :
    RestrictionProfile (restored F r) (FiniteLaw.uniform _) (FiniteLaw.uniform _)
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

end Paper2.RestorationBridge
