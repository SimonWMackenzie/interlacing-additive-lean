import CurrentAdditive.ExplicitStageNumbering
import CurrentAdditive.SeedRowEquiv
import CurrentAdditive.DeterministicETHSeedStageProd

/-! The original lookup seed with explicit Fin row labels in the exact order
printed by the inherited physical seed machine.  The row decoder is `seedRow`
and retains every Boolean word once. -/

namespace CurrentAdditive.IndexedExecutableStepRecovery

open Paper2
open Paper2.LookupSeed
open CurrentAdditive.DeterministicParameters
open CurrentAdditive.DeterministicETHSeed
open CurrentAdditive.DeterministicETHSeedStage
open CurrentAdditive.IndexedStagePresentation
open SeedT45.SeedTable

noncomputable def indexedSeedStage (L : ℕ) : Stage (N L) where
  Row := Fin (2 ^ width L)
  Col := Fin (width L)
  rowFinite := inferInstance
  colFinite := inferInstance
  rowDecEq := inferInstance
  colDecEq := inferInstance
  rowLaw := numberedLaw (rowLaw (width L)) (seedRowEquiv (width L))
  colLaw := numberedLaw (columnLaw (width L)
    (Nat.two_pow_pos (exponent L))) (Equiv.refl _)
  matrix := indexedSeed L
  encodingSize := seedEncodingBudget L
  entries_le_encoding := by
    simp only [Fintype.card_fin, seedEncodingBudget]
    have h : 2 ^ width L * width L ≤
        2 ^ width L * (2 * width L + 4) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  public_side := by
    have hw : L ≤ width L := by
      have h := width_admissible L
      omega
    have hp : N L ≤ 2 ^ width L :=
      Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hw
    simpa only [N, Fintype.card_fin] using
      (le_trans hp (le_max_left (2 ^ width L) (width L)))
  stepClock := 0

theorem indexedSeedStage_cost (L : ℕ) :
    Workspace.Types.CommComplexity.D (indexedSeedStage L).matrix =
      exponent L + 1 := by
  exact indexedSeed_cost L

theorem indexedSeedStage_profile_public (L : ℕ) :
    RestrictionProfile (indexedSeedStage L).matrix
      (indexedSeedStage L).rowLaw.toFiniteLaw
      (indexedSeedStage L).colLaw.toFiniteLaw
      (((ρ L : ℚ) : ℝ))
      (Workspace.Types.CommComplexity.D (indexedSeedStage L).matrix : ℤ) := by
  let μr := rowLaw (width L)
  let μc := columnLaw (width L) (Nat.two_pow_pos (exponent L))
  have hsource : RestrictionProfile (matrix (width L))
      μr.toFiniteLaw μc.toFiniteLaw (((ρ L : ℚ) : ℝ))
      (Workspace.Types.CommComplexity.D (matrix (width L)) : ℤ) := by
    rw [CurrentAdditive.DeterministicETHSeedStage.rho_real_eq]
    rw [(selected_seed_finite L).1]
    exact (selected_seed_finite L).2.1
  have htransport := restrictionProfile_pullback_iff
    (matrix (width L)) μr.toFiniteLaw μc.toFiniteLaw
    (numberedLaw μr (seedRowEquiv (width L))).toFiniteLaw
    (numberedLaw μc (Equiv.refl _)).toFiniteLaw
    (seedRowEquiv (width L)) (Equiv.refl _)
    (numberedLaw_pushesTo μr (seedRowEquiv (width L)))
    (numberedLaw_pushesTo μc (Equiv.refl _))
    (seedRowEquiv (width L)).surjective (Equiv.refl _).surjective
    (((ρ L : ℚ) : ℝ))
    (Workspace.Types.CommComplexity.D (matrix (width L)) : ℤ)
  have hnum := htransport.mpr hsource
  have hcost : Workspace.Types.CommComplexity.D (matrix (width L)) =
      Workspace.Types.CommComplexity.D (indexedSeed L) :=
    (selected_seed_finite L).1.trans (indexedSeed_cost L).symm
  rw [congrArg (fun z : ℕ => (z : ℤ)) hcost] at hnum
  change RestrictionProfile (indexedSeed L)
    (numberedLaw μr (seedRowEquiv (width L))).toFiniteLaw
    (numberedLaw μc (Equiv.refl _)).toFiniteLaw
    (((ρ L : ℚ) : ℝ))
    (Workspace.Types.CommComplexity.D (indexedSeed L) : ℤ)
  simpa only [seedRowEquiv_apply, Equiv.refl_apply,
    indexedSeed, seedTable] using hnum

#print axioms indexedSeedStage
#print axioms indexedSeedStage_cost
#print axioms indexedSeedStage_profile_public

end CurrentAdditive.IndexedExecutableStepRecovery
