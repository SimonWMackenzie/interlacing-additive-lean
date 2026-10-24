import CurrentAdditive.V39GraphGenerated
import CurrentAdditive.SeedIndexedStage
import CurrentAdditive.V38RestrictionProfiles
import CurrentAdditive.V38Schedule

/-! The literal stored lookup seed has the current two-threshold profile
under the exact uniform vectors written by its constructor. -/

namespace CurrentAdditive.V39GeneratedConstruction

open Paper2 Paper2.LookupSeed V38Schedule Workspace.Types.CommComplexity
open CurrentAdditive.IndexedExecutableStepRecovery
open CurrentAdditive.DeterministicETHSeed

private theorem law_ext {A : Type} [Fintype A] (μ ν : PositiveRationalLaw A)
    (h : μ.weight=ν.weight) : μ=ν := by cases μ; cases ν; cases h; rfl

theorem lookupSeed_profile (L : ℕ) :
    V38RestrictionProfiles.TwoThresholdProfile (lookupSeed L).entry
      (lookupSeed L).rowLaw.toFiniteLaw (lookupSeed L).colLaw.toFiniteLaw
      ((generatedRho L : ℚ) : ℝ) ((exponent L+1 : ℕ) : ℤ) := by
  have hp := indexedSeedStage_profile_public L
  have hr : (indexedSeedStage L).rowLaw=(lookupSeed L).rowLaw := by
    apply law_ext
    funext i
    change ((Fintype.card (Fin (width L) → Bool) : ℚ)⁻¹) =
      ((2^(width L) : ℕ) : ℚ)⁻¹
    simp only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,
      Nat.cast_pow,Nat.cast_ofNat,one_div]
  have hc : (indexedSeedStage L).colLaw=(lookupSeed L).colLaw := by
    apply law_ext
    funext i
    change ((Fintype.card (Fin (width L)) : ℚ)⁻¹) = ((width L : ℕ) : ℚ)⁻¹
    simp only [Fintype.card_fin,one_div]
  rw [hr,hc,indexedSeedStage_cost] at hp
  intro j
  exact hp ⟨j.val,by omega⟩

theorem storedLookupSeed_profile (L : ℕ) :
    V38RestrictionProfiles.TwoThresholdProfile (storedLookupSeed L).entry
      (storedLookupSeed L).rowLaw.toFiniteLaw (storedLookupSeed L).colLaw.toFiniteLaw
      ((generatedRho L : ℚ) : ℝ) ((exponent L+1 : ℕ) : ℤ) := by
  change V38RestrictionProfiles.TwoThresholdProfile (storedLookupSeed L).numbered.entry
    (storedLookupSeed L).numbered.rowLaw.toFiniteLaw
    (storedLookupSeed L).numbered.colLaw.toFiniteLaw _ _
  rw [show (storedLookupSeed L).numbered=lookupSeed L from
    StoredMatrix.ofNumbered_numbered (lookupSeed L)]
  exact lookupSeed_profile L

end CurrentAdditive.V39GeneratedConstruction

#print axioms CurrentAdditive.V39GeneratedConstruction.lookupSeed_profile
#print axioms CurrentAdditive.V39GeneratedConstruction.storedLookupSeed_profile
