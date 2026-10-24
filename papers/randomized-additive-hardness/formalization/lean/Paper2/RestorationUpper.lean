import Paper2.SourceNearFull
import Paper2.InterlaceProtocol
import Paper2.RestorationReferenceProfileSource

/-!
# Actual full-product restoration selector upper bound

This is only the universal upper-bound half of frozen v12 `res:alignment`.
The source is the same graph-constructed `SourceConstruction.matrix` used
by the lower-bound argument; no source-cost equality is a premise.
-/

namespace Paper2.RestorationUpper

open Workspace.Types.CommComplexity SourceMatrix SourceProfileParameters

local instance (L : ℕ) : NeZero (width L) := ⟨by unfold width; positivity⟩
local instance (L : ℕ) : NeZero (outerWidth L) := ⟨by unfold outerWidth; positivity⟩
local instance (L : ℕ) : NeZero (width L - 2) := ⟨by
  have h := width_admissible L
  omega⟩

/-- The literal transposed full-product selector source of `res:alignment`. -/
noncomputable def sourceW {X Y V E : Type*} [Fintype X] [Fintype Y]
    [Fintype V] [Fintype E]
    (F : X → Y → Bool) (L : ℕ)
    (order : SourceConstruction.Items (width L) V ≃
      Fin (Fintype.card (SourceConstruction.Items (width L) V)))
    (edge : E → Bool → V) (sourceCopies : ℕ)
    (hq : outerWidth L = SourceItems.sourceQ0 (Fin (4 * width L)) E * sourceCopies)
    (ξ₀ : Tail (width L) Y) (selectorCopies : ℕ) :=
  fun ys z => fullInterlace
    (SourceConstruction.matrix (q₁ := width L - 2) order edge
      (by have := SourceProfiles.width_ge_four L; omega)
      sourceCopies hq F ξ₀) selectorCopies z ys

/-- The original graph-source protocol budget is at most `C`, obtained
from the base cost and the explicit source selector protocol. -/
theorem actual_source_D_le
    {X Y V E : Type*} [Fintype X] [Fintype Y]
    [Fintype V] [Fintype E]
    (F : X → Y → Bool) (L d C : ℕ) (hD : D F = d) (hC : 1 ≤ C)
    (hCeq : C - 1 = d + exponent L + outerExponent L + exponent L)
    (order : SourceConstruction.Items (width L) V ≃
      Fin (Fintype.card (SourceConstruction.Items (width L) V)))
    (edge : E → Bool → V) (sourceCopies : ℕ)
    (hq : outerWidth L = SourceItems.sourceQ0 (Fin (4 * width L)) E * sourceCopies)
    (ξ₀ : Tail (width L) Y) :
    D (SourceConstruction.matrix (q₁ := width L - 2) order edge
      (by have := SourceProfiles.width_ge_four L; omega)
      sourceCopies hq F ξ₀) ≤ C := by
  have hup := (SourceConstruction.matrix_upper_budgets
    (q₁ := width L - 2) order edge
    (by have := SourceProfiles.width_ge_four L; omega)
    sourceCopies hq F ξ₀ (exponent L) (outerExponent L)
    (by have := SourceProfiles.width_ge_four L; omega) rfl rfl).1
  rw [hD] at hup
  omega

/-- The transposed selector `W` on the actual Items graph source has a
full-product protocol of cost at most `C+r` when `w=2^r`. -/
theorem actual_sourceW_D_le
    {X Y V E : Type*} [Fintype X] [Fintype Y]
    [Fintype V] [Fintype E]
    (F : X → Y → Bool) (L d C r w : ℕ) (hD : D F = d) (hC : 1 ≤ C)
    (hCeq : C - 1 = d + exponent L + outerExponent L + exponent L)
    (hw : w = 2 ^ r)
    (order : SourceConstruction.Items (width L) V ≃
      Fin (Fintype.card (SourceConstruction.Items (width L) V)))
    (edge : E → Bool → V) (sourceCopies : ℕ)
    (hq : outerWidth L = SourceItems.sourceQ0 (Fin (4 * width L)) E * sourceCopies)
    (ξ₀ : Tail (width L) Y) :
    D (sourceW F L order edge sourceCopies hq ξ₀ w) ≤ C + r := by
  have hsource := actual_source_D_le F L d C hD hC hCeq
    order edge sourceCopies hq ξ₀
  have hselector := Paper2.fullInterlace_two_pow_D_le
    (SourceConstruction.matrix (q₁ := width L - 2) order edge
      (by have := SourceProfiles.width_ge_four L; omega)
      sourceCopies hq F ξ₀) r
  rw [← hw] at hselector
  change D (fun ys z => fullInterlace
    (SourceConstruction.matrix (q₁ := width L - 2) order edge
      (by have := SourceProfiles.width_ge_four L; omega)
      sourceCopies hq F ξ₀) w z ys) ≤ C + r
  rw [transpose_D]
  omega

end Paper2.RestorationUpper

#print axioms Paper2.RestorationUpper.actual_source_D_le
#print axioms Paper2.RestorationUpper.actual_sourceW_D_le
