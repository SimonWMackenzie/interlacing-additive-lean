import Paper2.RationalSeparationDescent
import Paper2.ClassicalCapacities

/-!
# Row amplification and capacity bounds for rational input laws

Frozen v12 Appendix A, `cl:row-ladder`, `cl:small-capacities`, and
`cl:rational-laws`. Each theorem starts with the original rationally weighted
base matrix and the actual retained interlace rows and full column tuples.
All-copy lifts satisfy the classical uniform theorem's integer ceilings.
Their communication complexity equals that of the original restriction.
-/

namespace Paper2.RationalRowEstimates

open scoped BigOperators
open Workspace.Types.CommComplexity Workspace.Types.Interlace
open RationalSeparation

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- All-copy lifting preserves the exact cost of this particular retained
interlace. The original retained full-tuple event may be arbitrarily correlated. -/
theorem lifted_D_eq (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (F : X → Y → Bool) (h : ℕ+) (p : ℕ)
    (R : Finset (Fin p × X)) (C : Finset (Fin p → Y)) :
    D (NPCC.subgame (fullInterlace (matrix μ ν F h) p)
      (liftSet (blockForget μ h p) R) (liftSet (ν.forgetTuple p) C)) =
      D (NPCC.subgame (fullInterlace F p) R C) := by
  classical
  exact pullback_D_eq_of_surjective (NPCC.subgame (fullInterlace F p) R C)
    (forgetLift (blockForget μ h p) R) (forgetLift (ν.forgetTuple p) C)
    (forgetLift_surjective _ (blockForget_surjective μ h p) R)
    (forgetLift_surjective _ (ν.forgetTuple_surjective p) C)

/-- A lower-bound profile is not needed to transport a single threshold:
every row/column threshold and every integer lower bound is preserved. -/
theorem matrix_lowerBound_iff (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (F : X → Y → Bool) (h : ℕ+) (x z : ℝ) (H : ℤ) :
    RestrictionLowerBound (matrix μ ν F h)
      (FiniteLaw.uniform (Rows μ h)) (FiniteLaw.uniform ν.Copies) x z H ↔
      RestrictionLowerBound F μ.toFiniteLaw ν.toFiniteLaw x z H := by
  have hh := uniform_row_duplication_restrictionLowerBound_iff
    (fun x y => F (μ.forget x) (ν.forget y)) μ.uniformCopies ν.uniformCopies h h.pos x z H
  rw [rows_uniform_eq μ h, copies_uniform_eq ν] at hh
  have he : FiniteLaw.uniform ν.Copies = ν.uniformCopies := (copies_uniform_eq ν).symm
  have hr : RestrictionLowerBound (fun x y => F (μ.forget x) (ν.forget y))
      μ.uniformCopies (FiniteLaw.uniform ν.Copies) x z H ↔
      RestrictionLowerBound F μ.toFiniteLaw ν.toFiniteLaw x z H := by
    simpa only [he] using rationalCopies_restrictionLowerBound_iff μ ν F x z H
  exact hh.trans hr

/-- Selected blocks retain their own original row-probability thresholds.
Rows from additional blocks are allowed and are left in the matrix. -/
theorem lifted_selected_rows (μ : PositiveRationalLaw X) (h : ℕ+) (p : ℕ)
    (Q : Finset (Fin p)) (R : Finset (Fin p × X)) (x : ℝ)
    (hR : ∀ i ∈ Q, x ≤ μ.toFiniteLaw.prob (fun a => (i, a) ∈ R)) :
    NPCC.IsEquipartitionedGE (liftSet (blockForget μ h p) R) Q
      ⌈(Fintype.card (Rows μ h) : ℝ) * x⌉₊ := by
  classical
  intro i hi
  rw [lifted_block_card]
  apply (FiniteLaw.le_uniform_prob_iff _ x).mp
  have hh := hR i hi
  rw [← rows_prob_preimage μ h (fun a => (i, a) ∈ R)] at hh
  simpa only [mem_liftSet] using hh

theorem lifted_columns (ν : PositiveRationalLaw Y) (p : ℕ)
    (C : Finset (Fin p → Y)) (z : ℝ)
    (hC : z ≤ (ν.toFiniteLaw.iid p).prob (· ∈ C)) :
    ⌈(Fintype.card ν.Copies : ℝ) ^ p * z⌉₊ ≤
      (liftSet (ν.forgetTuple p) C).card := by
  have hh := hC
  rw [← tuples_prob_preimage ν p (· ∈ C)] at hh
  have hm : z ≤ (FiniteLaw.uniform (Fin p → ν.Copies)).prob
      (· ∈ liftSet (ν.forgetTuple p) C) := by simpa only [mem_liftSet] using hh
  have hc := (FiniteLaw.le_uniform_prob_iff _ z).mp hm
  simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using hc

/-- Literal probability form of the `K=2^l>=4` capacity estimate, on the
original retained matrix and arbitrary selected outer blocks. `H` is only
a lower-bound parameter and need not equal the full matrix's complexity. -/
theorem small_capacity_power (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (F : X → Y → Bool) (H l p : ℕ) {x : ℝ}
    (hH : 2 ≤ H) (hx0 : 0 < x) (hl : 2 ≤ l)
    (hscale : (2 : ℝ) ^ l * x ≤ 1)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (Q : Finset (Fin p)) (hQ : 2 ^ (l - 1) + 1 ≤ Q.card)
    (R : Finset (Fin p × X)) (C : Finset (Fin p → Y))
    (hrow : ∀ i ∈ Q, (2 : ℝ) ^ l * x ≤ μ.toFiniteLaw.prob (fun a => (i, a) ∈ R))
    (hcol : (9 / 25 : ℝ) ≤ (ν.toFiniteLaw.iid p).prob (· ∈ C)) :
    H + l ≤ D (NPCC.subgame (fullInterlace F p) R C) := by
  have hp := (matrix_profile_iff μ ν F 1 x (H : ℤ)).mpr hprofile
  have hh := ClassicalCapacities.small_capacity_power (matrix μ ν F 1) H l p
    hH hx0 hl hscale hp Q hQ
    (liftSet (blockForget μ 1 p) R) (liftSet (ν.forgetTuple p) C)
    (lifted_selected_rows μ 1 p Q R _ hrow) (lifted_columns ν p C _ hcol)
  rw [show interlaceFun (matrix μ ν F 1) p = fullInterlace (matrix μ ν F 1) p from rfl,
    lifted_D_eq] at hh
  exact hh

/-- Both small cases (`K=1` and `K=2`) use two blocks and the doubled row
threshold, exactly as in the source. There is no one-block claim. -/
theorem small_capacity_two (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (F : X → Y → Bool) (H p : ℕ) {x : ℝ}
    (hH : 2 ≤ H) (hx0 : 0 < x) (hscale : 2 * x ≤ 1)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (Q : Finset (Fin p)) (hQ : 2 ≤ Q.card)
    (R : Finset (Fin p × X)) (C : Finset (Fin p → Y))
    (hrow : ∀ i ∈ Q, 2 * x ≤ μ.toFiniteLaw.prob (fun a => (i, a) ∈ R))
    (hcol : (9 / 25 : ℝ) ≤ (ν.toFiniteLaw.iid p).prob (· ∈ C)) :
    H + 1 ≤ D (NPCC.subgame (fullInterlace F p) R C) := by
  have hp := (matrix_profile_iff μ ν F 1 x (H : ℤ)).mpr hprofile
  have hh := ClassicalCapacities.small_capacity_two (matrix μ ν F 1) H p
    hH hx0 hscale hp Q hQ
    (liftSet (blockForget μ 1 p) R) (liftSet (ν.forgetTuple p) C)
    (lifted_selected_rows μ 1 p Q R _ hrow) (lifted_columns ν p C _ hcol)
  rw [show interlaceFun (matrix μ ν F 1) p = fullInterlace (matrix μ ν F 1) p from rfl,
    lifted_D_eq] at hh
  exact hh

/-- The one-copy hypothesis at any column threshold `z`, transferred from
the three original weighted lower bounds. Unlike protocol-order separation,
this does not require `H` to be the exact complexity of `F`. -/
theorem base_lambda (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (F : X → Y → Bool) (h : ℕ+) (H : ℕ) (x z : ℝ) (hx : x ≤ 1) (hz : z ≤ 1)
    (h₀ : RestrictionLowerBound F μ.toFiniteLaw ν.toFiniteLaw x z (H : ℤ))
    (h₁ : RestrictionLowerBound F μ.toFiniteLaw ν.toFiniteLaw x (z / 2) ((H : ℤ) - 1))
    (h₂ : RestrictionLowerBound F μ.toFiniteLaw ν.toFiniteLaw x (z / 4) ((H : ℤ) - 2)) :
    H ≤ ClassicalRows.lambda (matrix μ ν F h) 1 x z := by
  have hu₀ := ClassicalSeparation.oneCopy_family_lowerBound (matrix μ ν F h) x z
    (H : ℤ) hx hz ((matrix_lowerBound_iff μ ν F h x z _).mpr h₀)
  have hu₁ := ClassicalSeparation.oneCopy_family_lowerBound (matrix μ ν F h) x (z / 2)
    ((H : ℤ) - 1) hx (by linarith) ((matrix_lowerBound_iff μ ν F h x (z / 2) _).mpr h₁)
  have hu₂ := ClassicalSeparation.oneCopy_family_lowerBound (matrix μ ν F h) x (z / 4)
    ((H : ℤ) - 2) hx (by linarith) ((matrix_lowerBound_iff μ ν F h x (z / 4) _).mpr h₂)
  change (H : ℤ) - 1 ≤
    (ClassicalRows.restrictionCost (matrix μ ν F h) 1 x (z / 2) : ℤ) at hu₁
  change (H : ℤ) - 2 ≤
    (ClassicalRows.restrictionCost (matrix μ ν F h) 1 x (z / 4) : ℤ) at hu₂
  apply (ClassicalRows.le_lambda_iff _ 1 H x z).mpr
  refine ⟨by exact_mod_cast hu₀, ?_, ?_⟩
  · have he : (H : ℤ) ≤ 1 +
        (ClassicalRows.restrictionCost (matrix μ ν F h) 1 x (z / 2) : ℤ) := by omega
    exact_mod_cast he
  · have he : (H : ℤ) ≤ 2 +
        (ClassicalRows.restrictionCost (matrix μ ν F h) 1 x (z / 4) : ℤ) := by omega
    exact_mod_cast he

theorem lambda_le_rung (F : X → Y → Bool) (p : ℕ) (x z : ℝ) (j : Fin 3) :
    ClassicalRows.lambda F p x z ≤ j.val +
      ClassicalRows.restrictionCost F p x (z / (2 : ℝ) ^ j.val) := by
  fin_cases j
  · simpa only [Fin.val_zero, pow_zero, div_one, zero_add] using
      ClassicalRows.lambda_le_top F p x z
  · have hh := (min_le_right (ClassicalRows.restrictionCost F p x z)
      (min (1 + ClassicalRows.restrictionCost F p x (z / 2))
        (2 + ClassicalRows.restrictionCost F p x (z / 4)))).trans (min_le_left _ _)
    simpa only [ClassicalRows.lambda_eq, Fin.val_one, pow_one] using hh
  · simpa only [Fin.reduceFinMk, show (2 : ℝ) ^ 2 = 4 by norm_num] using
      ClassicalRows.lambda_le_bottom F p x z

/-- General-column-threshold row amplification in the probability form of
the source. Every rung is an actual retained-matrix bound, not a claim about
a substitute matrix or a uniform distribution on the retained tuples. -/
theorem row_ladder (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (F : X → Y → Bool) (H l : ℕ) (x z : ℝ)
    (hH : 2 ≤ H) (hl : 1 ≤ l) (hx : 0 < x) (hz : 0 < z) (hz1 : z ≤ 1)
    (hscale : (2 : ℝ) ^ l * x ≤ 1)
    (h₀ : RestrictionLowerBound F μ.toFiniteLaw ν.toFiniteLaw x z (H : ℤ))
    (h₁ : RestrictionLowerBound F μ.toFiniteLaw ν.toFiniteLaw x (z / 2) ((H : ℤ) - 1))
    (h₂ : RestrictionLowerBound F μ.toFiniteLaw ν.toFiniteLaw x (z / 4) ((H : ℤ) - 2))
    (j : Fin 3)
    (R : Finset (Fin (2 ^ (l - 1) + 1) × X))
    (C : Finset (Fin (2 ^ (l - 1) + 1) → Y))
    (hR : ∀ i, (2 : ℝ) ^ l * x ≤ μ.toFiniteLaw.prob (fun a => (i, a) ∈ R))
    (hC : z ^ 2 / (2 : ℝ) ^ j.val ≤
      (ν.toFiniteLaw.iid (2 ^ (l - 1) + 1)).prob (· ∈ C)) :
    H + l ≤ j.val + D (NPCC.subgame (fullInterlace F (2 ^ (l - 1) + 1)) R C) := by
  have hx1 : x ≤ 1 := (le_mul_of_one_le_left hx.le
    (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))).trans hscale
  have hbase := base_lambda μ ν F 1 H x z hx1 hz1 h₀ h₁ h₂
  have hlam := ClassicalRows.row_ladder (matrix μ ν F 1) H hH hx hz hz1 hbase l hl hscale
  have hrung := hlam.trans (lambda_le_rung (matrix μ ν F 1)
    (2 ^ (l - 1) + 1) ((2 : ℝ) ^ l * x) (z ^ 2) j)
  have hmember := ClassicalRows.restrictionCost_le_member (matrix μ ν F 1)
    (2 ^ (l - 1) + 1) ((2 : ℝ) ^ l * x) (z ^ 2 / (2 : ℝ) ^ j.val)
    (liftSet (blockForget μ 1 _) R) (liftSet (ν.forgetTuple _) C)
    (lifted_bracket μ ν 1 _ _ _ R C hR hC)
  have hh := hrung.trans (Nat.add_le_add_left hmember j.val)
  rw [show interlaceFun (matrix μ ν F 1) (2 ^ (l - 1) + 1) =
      fullInterlace (matrix μ ν F 1) (2 ^ (l - 1) + 1) from rfl,
    lifted_D_eq] at hh
  exact hh

end Paper2.RationalRowEstimates

#print axioms Paper2.RationalRowEstimates.lifted_D_eq
#print axioms Paper2.RationalRowEstimates.small_capacity_power
#print axioms Paper2.RationalRowEstimates.small_capacity_two
#print axioms Paper2.RationalRowEstimates.row_ladder
