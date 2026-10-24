import CurrentAdditive.ConditioningGeneralComplete
import CurrentAdditive.DeterministicIndexedMatrix
import Paper2.RestorationBridgeRational

/-!
The numerical population step in v27 Appendix H, `det:restore`.  This is
written for the actual three profile rungs: `m = 2^j` with `j = 0,1,2`.
The separate source conditioning and protocol arguments will use this bound.
-/

namespace CurrentAdditive.DeterministicRestoration

open Paper2

/-- From the displayed public width and row-threshold guards, the retained
population can pay for more than half of the `k = Q/m` blocks, after removing
all exceptional coordinates.  The cast of the exceptional count is explicit. -/
theorem population_budget
    (m k e : ℕ) (θ : ℝ)
    (hm : 1 ≤ m) (hm4 : m ≤ 4)
    (hQ : (128 : ℝ) * ((e : ℝ) + 1) ≤ (2 * m * k : ℕ))
    (hθ : (2 * m * k : ℕ) * θ ≤ 1 / 20)
    (hθ0 : 0 ≤ θ) :
    (((k + 1 + e : ℕ) : ℝ) * (1 - (2 * k : ℕ) * θ)) ≤
      ((2 * m * k : ℕ) : ℝ) *
        (((3 / 5 : ℝ) / m) - (2 * k : ℕ) * θ) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm4R : (m : ℝ) ≤ 4 := by exact_mod_cast hm4
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg _
  have hklarge : (16 : ℝ) * ((e : ℝ) + 1) ≤ k := by
    norm_num at hQ ⊢
    nlinarith
  have hcost : ((2 * m * k : ℕ) : ℝ) * ((2 * k : ℕ) : ℝ) * θ ≤
      ((2 * k : ℕ) : ℝ) / 20 := by
    have h := mul_le_mul_of_nonneg_left hθ
      (show (0 : ℝ) ≤ ((2 * k : ℕ) : ℝ) by positivity)
    nlinarith
  have hpositive : 0 ≤ (((k + 1 + e : ℕ) : ℝ)) := Nat.cast_nonneg _
  have hrowterm :
      (((k + 1 + e : ℕ) : ℝ) * (1 - (2 * k : ℕ) * θ)) ≤
      ((k + 1 + e : ℕ) : ℝ) := by
    have hprod : 0 ≤ (((k + 1 + e : ℕ) : ℝ) * ((2 * k : ℕ) : ℝ) * θ) := by
      positivity
    nlinarith
  have hmain : ((k + 1 + e : ℕ) : ℝ) ≤
      ((6 : ℝ) / 5) * k - ((2 * k : ℕ) : ℝ) / 20 := by
    norm_num at hklarge ⊢
    nlinarith
  have hrewrite :
      ((2 * m * k : ℕ) : ℝ) * ((3 / 5 : ℝ) / m) =
      ((6 : ℝ) / 5) * k := by
    push_cast
    field_simp [ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hmR)]
    ring
  calc
    _ ≤ ((k + 1 + e : ℕ) : ℝ) := hrowterm
    _ ≤ ((6 : ℝ) / 5) * k - ((2 * k : ℕ) : ℝ) / 20 := hmain
    _ ≤ ((2 * m * k : ℕ) : ℝ) *
          (((3 / 5 : ℝ) / m) - (2 * k : ℕ) * θ) := by
      rw [mul_sub, hrewrite]
      linarith

/-- Conditioning on an arbitrary retained set of original source labels.
The exceptional coordinates are analysis witnesses, never constructor inputs.
The decoded tuple source is the generated `CodeSource`, rather than the full
independent product on visible tuples. -/
theorem generated_good_coordinates
    {Z : Type*} [Fintype Z] [DecidableEq Z]
    {Q : ℕ} (ν : Paper2.PositiveRationalLaw Z)
    (src : CurrentAdditive.DeterministicIndexedMatrix.CodeSource
      (8 * 1024) Q Z ν)
    (Y : Set src.Label) (φ δ : ℝ)
    (hφ : 0 < φ) (hY : φ ≤ src.law.toFiniteLaw.prob (· ∈ Y))
    (hδ : 0 < δ) :
    ∃ E : Finset (Fin Q),
      E.card ≤ CurrentAdditive.conditioningExceptionCountR 1024 φ (δ / 2) ∧
      ∀ J : Finset (Fin Q),
        J ⊆ (Finset.univ : Finset (Fin Q)) \ E → J.card ≤ 8 →
          CurrentAdditive.projectionTV
            (CurrentAdditive.condition src.law.toFiniteLaw (· ∈ Y)
              (lt_of_lt_of_le hφ hY))
            ν.toFiniteLaw src.decode J ≤
              CurrentAdditive.conditioningEpsilonR 1024 φ (δ / 2) := by
  exact CurrentAdditive.conditioning_exceptional_coordinates_R
    (by decide : Even 1024) (by omega : 8 ≤ 1024)
    src.law.toFiniteLaw ν.toFiniteLaw src.decode (· ∈ Y)
    φ (δ / 2) hφ hY (by linarith) src.exactLaw

private theorem width_decompose (r j : ℕ) (h : j + 1 ≤ r) :
    2 ^ r = 2 * 2 ^ j * 2 ^ (r - j - 1) := by
  have hr : r = 1 + j + (r - j - 1) := by omega
  conv_lhs => rw [hr]
  simp only [pow_add, pow_one]

/-- The displayed `Q≥128(e+1)` guard itself forces at least seven selector
bits.  No extra profile-width premise is needed. -/
theorem width_exponent_seven (r e : ℕ)
    (hQ : (128 : ℝ) * ((e : ℝ) + 1) ≤ (2 ^ r : ℕ)) :
    7 ≤ r := by
  by_contra h
  have hr : r ≤ 6 := by omega
  have hp : 2 ^ r ≤ (64 : ℕ) := by
    exact Nat.pow_le_pow_right (by norm_num) hr
  have hpR : (((2 ^ r : ℕ) : ℝ)) ≤ 64 := by exact_mod_cast hp
  have he : (0 : ℝ) ≤ e := Nat.cast_nonneg _
  linarith

/-- The exact `j=0,1,2` profile thresholds in Appendix H satisfy the
population selector's budget.  The assumption `r≥3` is separately entailed
by the public width guard, since `Q=2^r≥128`. -/
theorem profile_population_budget (r e : ℕ) (j : Fin 3) (θ : ℝ)
    (hQ : (128 : ℝ) * ((e : ℝ) + 1) ≤ (2 ^ r : ℕ))
    (hθ : ((2 ^ r : ℕ) : ℝ) * θ ≤ 1 / 20)
    (hθ0 : 0 ≤ θ) :
    (((2 ^ (r - j.val - 1) + 1 + e : ℕ) : ℝ) *
      (1 - ((2 ^ (r - j.val) : ℕ) : ℝ) * θ)) ≤
        ((2 ^ r : ℕ) : ℝ) *
          (((3 / 5 : ℝ) * (1 / 2 : ℝ) ^ j.val) -
            ((2 ^ (r - j.val) : ℕ) : ℝ) * θ) := by
  have hr : 3 ≤ r := by
    have h := width_exponent_seven r e hQ
    omega
  have hj : j.val + 1 ≤ r := by have := j.isLt; omega
  have hm : 1 ≤ 2 ^ j.val := by
    have hp : 0 < 2 ^ j.val := pow_pos (by decide : 0 < (2 : ℕ)) _
    omega
  have hm4 : 2 ^ j.val ≤ 4 := by
    have := j.isLt
    interval_cases j.val <;> norm_num
  have hdecomp := width_decompose r j.val hj
  have hpow : 2 * 2 ^ (r - j.val - 1) = 2 ^ (r - j.val) := by
    have heq : r - j.val = 1 + (r - j.val - 1) := by omega
    rw [heq, pow_add]
    norm_num
  have hbase := population_budget (2 ^ j.val) (2 ^ (r - j.val - 1))
    e θ hm hm4 (by simpa [hdecomp] using hQ)
    (by simpa [hdecomp] using hθ) hθ0
  convert hbase using 1
  · simp only [hpow]
  · simp only [hdecomp, hpow]
    fin_cases j <;> norm_num

/-- The actual indexed, transposed restricted interlace has the manuscript's
unconditional protocol upper bound.  This works for duplicate decoded tuple
labels and does not use the lower-bound hypotheses. -/
theorem generated_restore_upper
    {X Z : Type*} [Fintype X] [Fintype Z]
    [DecidableEq Z] (ν : Paper2.PositiveRationalLaw Z)
    (F : X → Z → Bool) (r : ℕ)
    (src : CurrentAdditive.DeterministicIndexedMatrix.CodeSource
      8192 (2 ^ r) Z ν) :
    Workspace.Types.CommComplexity.D
      (fun (seed : src.Label) (a : Fin (2 ^ r) × X) =>
        F a.2 (src.decode seed a.1)) ≤
      Workspace.Types.CommComplexity.D F + r := by
  have h := Paper2.indexedInterlace_transpose_D_le F
    (Nat.two_pow_pos r) src.decode
  simpa only [Paper2.indexedInterlace, Nat.clog_pow 2 r (by decide),
    Nat.add_comm] using h

/-- Once the three lower profile rungs are proved, their top rung matches
the unconditional indexed upper protocol on exactly the same source labels. -/
theorem generated_restore_cost_of_profile
    {X Z : Type*} [Fintype X] [Fintype Z]
    [DecidableEq Z] (μ : Paper2.PositiveRationalLaw X)
    (ν : Paper2.PositiveRationalLaw Z)
    (F : X → Z → Bool) (r C : ℕ) (φ : ℝ)
    (src : CurrentAdditive.DeterministicIndexedMatrix.CodeSource
      8192 (2 ^ r) Z ν)
    (hC : Workspace.Types.CommComplexity.D F = C)
    (hφ : φ ≤ 1)
    (hp : Paper2.RestrictionProfile
      (fun (seed : src.Label) (a : Fin (2 ^ r) × X) =>
        F a.2 (src.decode seed a.1))
      src.law.toFiniteLaw
      ((Paper2.PositiveRationalLaw.uniform (Fin (2 ^ r))).prod μ).toFiniteLaw
      φ ((C + r : ℕ) : ℤ)) :
    Workspace.Types.CommComplexity.D
      (fun (seed : src.Label) (a : Fin (2 ^ r) × X) =>
        F a.2 (src.decode seed a.1)) = C + r := by
  letI : Nonempty src.Label := src.law.nonempty
  letI : Nonempty X := μ.nonempty
  letI : Nonempty (Fin (2 ^ r)) := ⟨⟨0, Nat.two_pow_pos r⟩⟩
  apply le_antisymm
  · simpa only [hC] using generated_restore_upper ν F r src
  · exact Paper2.RestorationBridge.profile_full_lower _ _ _ φ (C + r) hφ hp

#print axioms population_budget
#print axioms generated_good_coordinates
#print axioms width_exponent_seven
#print axioms profile_population_budget
#print axioms generated_restore_upper
#print axioms generated_restore_cost_of_profile

end CurrentAdditive.DeterministicRestoration
