import CurrentAdditive.IndexedStagePresentation
import CurrentAdditive.DeterministicETHSeed

/-! The literal lookup matrix as the seed of the dependent indexed-stage
construction. The size field is an explicit conservative budget for its
table and uniform rational law entries; the successor's own clock is
charged through its separate `StepInputs` producer. -/

namespace CurrentAdditive.DeterministicETHSeedStage

open CurrentAdditive.DeterministicParameters
open CurrentAdditive.IndexedStagePresentation
open Workspace.Types.CommComplexity
open Paper2.LookupSeed

def seedEncodingBudget (L : ℕ) : ℕ :=
  2 ^ width L * (2 * width L + 4) +
  width L * (width L + 2) + N L + 2

/-- The full Boolean cube, not an existential cost certificate, is the
initial state used at every graph. Its laws are the original uniform laws. -/
noncomputable def seedStage (L : ℕ) : Stage (N L) where
  Row := Fin (width L) → Bool
  Col := Fin (width L)
  rowFinite := inferInstance
  colFinite := inferInstance
  rowDecEq := inferInstance
  colDecEq := inferInstance
  rowLaw := rowLaw (width L)
  colLaw := columnLaw (width L) (Nat.two_pow_pos (exponent L))
  matrix := matrix (width L)
  encodingSize := seedEncodingBudget L
  entries_le_encoding := by
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      seedEncodingBudget]
    have hp : 2 ^ width L * width L ≤
        2 ^ width L * (2 * width L + 4) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  public_side := by
    have hw : L ≤ width L := by
      have h := width_admissible L
      omega
    have hp : N L ≤ 2 ^ width L := by
      exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hw
    simpa only [N, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin] using
      (le_trans hp (le_max_left (2 ^ width L) (width L)))
  stepClock := 0

theorem seedStage_matrix (L : ℕ) :
    (seedStage L).matrix = matrix (width L) := rfl

theorem seedStage_cost (L : ℕ) :
    D (seedStage L).matrix = exponent L + 1 := by
  simpa only [seedStage_matrix] using (selected_seed_finite L).1

theorem seedStage_profile (L : ℕ) :
    Paper2.RestrictionProfile (seedStage L).matrix
      (seedStage L).rowLaw.toFiniteLaw
      (seedStage L).colLaw.toFiniteLaw
      ((1/2:ℝ)^L) (D (seedStage L).matrix : ℤ) := by
  have hp := (selected_seed_finite L).2.1
  have hc : (D (seedStage L).matrix : ℤ) = (exponent L : ℤ) + 1 := by
    exact_mod_cast seedStage_cost L
  rw [hc]
  simpa only [seedStage] using hp

theorem rho_real_eq (L : ℕ) :
    ((ρ L : ℚ) : ℝ) = (1/2:ℝ)^L := by
  simp [ρ, N, one_div_pow]

theorem seedStage_profile_public (L : ℕ) :
    Paper2.RestrictionProfile (seedStage L).matrix
      (seedStage L).rowLaw.toFiniteLaw
      (seedStage L).colLaw.toFiniteLaw
      ((ρ L : ℚ) : ℝ) (D (seedStage L).matrix : ℤ) := by
  rw [rho_real_eq]
  exact seedStage_profile L

#print axioms seedStage
#print axioms seedStage_cost
#print axioms seedStage_profile
#print axioms seedStage_profile_public

end CurrentAdditive.DeterministicETHSeedStage
