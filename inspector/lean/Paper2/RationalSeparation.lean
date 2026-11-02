import Paper2.ClassicalSeparation
import Paper2.DuplicationMargins

/-!
# Applying classical separation to rationally weighted inputs

Frozen v12 Appendix A, `cl:rational-laws`. A common denominator is followed
by an actual positive integer number of uniform row copies. This module
connects the profile and finite ceiling arguments to the checked separation
theorem. The representation is for proof purposes, not a runtime claim.
-/

namespace Paper2

open scoped BigOperators
open Workspace.Types.CommComplexity Workspace.Types.Protocol

namespace FiniteLaw

theorem eq_of_weight_eq {α : Type*} [Fintype α] (μ ν : FiniteLaw α)
    (h : μ.weight = ν.weight) : μ = ν := by
  cases μ
  cases ν
  cases h
  rfl

end FiniteLaw

namespace RationalSeparation

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Extra uniform row labels after the common-denominator realization. -/
abbrev Rows (μ : PositiveRationalLaw X) (h : ℕ+) := Fin (h : ℕ) × μ.Copies

def rowForget (μ : PositiveRationalLaw X) (h : ℕ+) : Rows μ h → X :=
  fun x => μ.forget x.2

theorem rowForget_surjective (μ : PositiveRationalLaw X) (h : ℕ+) :
    Function.Surjective (rowForget μ h) := by
  intro x
  obtain ⟨z, hz⟩ := μ.forget_surjective x
  exact ⟨(⟨0, h.pos⟩, z), hz⟩

def matrix (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (F : X → Y → Bool) (h : ℕ+) : Rows μ h → ν.Copies → Bool :=
  fun x y => F (rowForget μ h x) (ν.forget y)

theorem row_card (μ : PositiveRationalLaw X) (h : ℕ+) :
    Fintype.card (Rows μ h) = (h : ℕ) * μ.denominator := by
  simp [Rows, μ.card_copies]

theorem copies_uniform_eq (μ : PositiveRationalLaw X) :
    μ.uniformCopies = FiniteLaw.uniform μ.Copies := by
  apply FiniteLaw.eq_of_weight_eq
  funext x
  simp only [PositiveRationalLaw.uniformCopies, FiniteLaw.uniform, μ.card_copies]

theorem rows_uniform_eq (μ : PositiveRationalLaw X) (h : ℕ+) :
    (FiniteLaw.uniformFin h h.pos).prod μ.uniformCopies = FiniteLaw.uniform (Rows μ h) := by
  apply FiniteLaw.eq_of_weight_eq
  funext x
  rw [uniformCopies_furtherDuplication_weight]
  simp only [FiniteLaw.uniform, row_card]

/-- Forgetting extra labels gives the original exact deterministic cost. -/
theorem matrix_D_eq (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (F : X → Y → Bool) (h : ℕ+) : D (matrix μ ν F h) = D F :=
  pullback_D_eq_of_surjective F (rowForget μ h) ν.forget
    (rowForget_surjective μ h) ν.forget_surjective

/-- The actual enlarged matrix has the same lower-bound profile under its
genuinely uniform laws, including arbitrary partial-fibre restrictions. -/
theorem matrix_profile_iff (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (F : X → Y → Bool) (h : ℕ+) (ρ : ℝ) (d : ℤ) :
    RestrictionProfile (matrix μ ν F h)
      (FiniteLaw.uniform (Rows μ h)) (FiniteLaw.uniform ν.Copies) ρ d ↔
    RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw ρ d := by
  have hh := uniform_row_duplication_profile_iff
    (fun x y => F (μ.forget x) (ν.forget y)) μ.uniformCopies ν.uniformCopies h h.pos ρ d
  rw [rows_uniform_eq μ h, copies_uniform_eq ν] at hh
  have hcopy : FiniteLaw.uniform ν.Copies = ν.uniformCopies :=
    (copies_uniform_eq ν).symm
  have hrat : RestrictionProfile (fun x y => F (μ.forget x) (ν.forget y))
      μ.uniformCopies (FiniteLaw.uniform ν.Copies) ρ d ↔
      RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw ρ d := by
    simpa only [hcopy] using (rationalCopies_profile_iff μ ν F ρ d)
  exact hh.trans hrat

/-- Positive rational inputs yield an actual finite uniform matrix with
the same exact cost and profile, and with the strict separation ceiling
guard. The duplication factor is proved to exist from the strict margin,
not supplied as an assumed successful representation. -/
theorem exists_admissible_uniform_representation
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y) (F : X → Y → Bool)
    (b Q : ℕ) (x : ℝ)
    (hsep : 2 * (2 ^ Q : ℝ) * (2 : ℝ) ^ (-(b : ℝ)) < x)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw
      ((2 : ℝ) ^ (-(b : ℝ))) (D F : ℤ)) :
    ∃ h : ℕ+,
      D (matrix μ ν F h) = D F ∧
      RestrictionProfile (matrix μ ν F h)
        (FiniteLaw.uniform (Rows μ h)) (FiniteLaw.uniform ν.Copies)
        ((2 : ℝ) ^ (-(b : ℝ))) (D (matrix μ ν F h) : ℤ) ∧
      2 ^ Q * ⌈(2 : ℝ) ^ (1 - (b : ℝ)) * (Fintype.card (Rows μ h) : ℝ)⌉₊ <
        ⌈(Fintype.card (Rows μ h) : ℝ) * x⌉₊ := by
  have hρ : 0 ≤ (2 : ℝ) ^ (-(b : ℝ)) := Real.rpow_nonneg (by norm_num) _
  obtain ⟨n, hn, hmargin⟩ := DuplicationMargins.exists_strict_ceiling_margin
    (2 ^ Q) μ.denominator μ.denominator_pos ((2 : ℝ) ^ (-(b : ℝ))) x hρ
    (by simpa using hsep)
  let h : ℕ+ := ⟨n, hn⟩
  refine ⟨h, matrix_D_eq μ ν F h, ?_, ?_⟩
  · rw [matrix_D_eq]
    exact (matrix_profile_iff μ ν F h _ _).mpr hprofile
  · have hp : (2 : ℝ) ^ (1 - (b : ℝ)) = 2 * (2 : ℝ) ^ (-(b : ℝ)) := by
      rw [sub_eq_add_neg, Real.rpow_add (by norm_num), Real.rpow_one]
    simpa only [row_card, Nat.cast_mul, hp, h, PNat.mk_coe, mul_assoc, mul_comm x]
      using hmargin

end RationalSeparation
end Paper2
