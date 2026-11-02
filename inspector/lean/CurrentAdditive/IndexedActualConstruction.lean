import CurrentAdditive.SeedIndexedStage
import CurrentAdditive.ExplicitRectangleTarget
import CurrentAdditive.IndexedSemanticIteration
import CurrentAdditive.DeterministicEndpointAssembly

/-! The same literal `Sources.successor` iteration, started from the seed's
explicit indexed row set.  This constructor has no physical Code_D clock or
NO-side conclusion baked into it. -/

namespace CurrentAdditive.IndexedExecutableStepRecovery

open CurrentAdditive.DeterministicParameters
open CurrentAdditive.IndexedStagePresentation
open CurrentAdditive.IndexedSemanticIteration
open CurrentAdditive.DeterministicIteration
open Workspace.Types.CommComplexity

variable (v e L : ℕ) [NeZero v] [NeZero (s L)] [NeZero (s L-3)]
  [NeZero (q₁ L)] [NeZero (q₂ L)] [NeZero (w L)] [NeZero (Q L)]

noncomputable def indexedActualConstruction
    (T : Schedule (Fin v) (Fin e) L)
    (inputs : ∀ R : Stage (N L), StepInputs (V := Fin v) (E := Fin e) L R T) :
    Construction (IndexedSemanticIteration.Graph (Fin v) (Fin e)) (Stage (N L)) :=
  construction L T (fun _ => indexedSeedStage L) inputs

theorem indexedActual_seed_cost
    (T : Schedule (Fin v) (Fin e) L)
    (inputs : ∀ R : Stage (N L), StepInputs (V := Fin v) (E := Fin e) L R T)
    (G : IndexedSemanticIteration.Graph (Fin v) (Fin e)) :
    (indexedActualConstruction v e L T inputs).cost
      ((indexedActualConstruction v e L T inputs).seed G) =
      Paper2.LookupSeed.exponent L + 1 := indexedSeedStage_cost L

theorem indexedActual_seed_profile
    (T : Schedule (Fin v) (Fin e) L)
    (inputs : ∀ R : Stage (N L), StepInputs (V := Fin v) (E := Fin e) L R T)
    (G : IndexedSemanticIteration.Graph (Fin v) (Fin e)) :
    (indexedActualConstruction v e L T inputs).profile G
      ((indexedActualConstruction v e L T inputs).seed G) :=
  indexedSeedStage_profile_public L

theorem indexedActual_universal
    (T : Schedule (Fin v) (Fin e) L)
    (inputs : ∀ R : Stage (N L), StepInputs (V := Fin v) (E := Fin e) L R T)
    (G : IndexedSemanticIteration.Graph (Fin v) (Fin e)) :
    UniversalContract (indexedActualConstruction v e L T inputs) G
      (Paper2.LookupSeed.exponent L + 1) (h L) :=
  IndexedSemanticIteration.universal L T (fun _ => indexedSeedStage L)
    inputs G (Paper2.LookupSeed.exponent L + 1)
    (le_of_eq (indexedSeedStage_cost L))

theorem indexedActual_valid
    (T : Schedule (Fin v) (Fin e) L)
    (inputs : ∀ R : Stage (N L), StepInputs (V := Fin v) (E := Fin e) L R T)
    (G : IndexedSemanticIteration.Graph (Fin v) (Fin e)) :
    ValidContract (indexedActualConstruction v e L T inputs) G :=
  IndexedSemanticIteration.valid L T (fun _ => indexedSeedStage L) inputs G

theorem indexedActual_yes
    (T : Schedule (Fin v) (Fin e) L)
    (inputs : ∀ R : Stage (N L), StepInputs (V := Fin v) (E := Fin e) L R T)
    (G : IndexedSemanticIteration.Graph (Fin v) (Fin e))
    (colour : Fin v → Fin 3)
    (proper : ∀ z, colour (G z false) ≠ colour (G z true)) :
    YesContract (indexedActualConstruction v e L T inputs) G
      (Paper2.LookupSeed.exponent L + 1) (h L) :=
  IndexedSemanticIteration.yes L T (fun _ => indexedSeedStage L)
    inputs G (Paper2.LookupSeed.exponent L + 1)
    (le_of_eq (indexedSeedStage_cost L)) colour proper

noncomputable def indexedActualNumberedTables
    (T : Schedule (Fin v) (Fin e) L)
    (inputs : ∀ R : Stage (N L), StepInputs (V := Fin v) (E := Fin e) L R T)
    (numberings : ∀ R : Stage (N L), ExplicitNumberings R) :
    CurrentAdditive.DeterministicEndpointAssembly.TablePresentation
      (indexedActualConstruction v e L T inputs) (N L) where
  rows := rows
  cols := cols
  table := fun R => numberedTable R (numberings R)
  rows_pos := rows_pos
  cols_pos := cols_pos
  exact_cost := fun R => numberedTable_cost R (numberings R)
  entries_le_encoding := Stage.entries_le_encoding
  public_side := Stage.public_side

#print axioms indexedActualConstruction
#print axioms indexedActual_seed_cost
#print axioms indexedActual_seed_profile
#print axioms indexedActual_universal
#print axioms indexedActual_valid
#print axioms indexedActual_yes
#print axioms indexedActualNumberedTables

end CurrentAdditive.IndexedExecutableStepRecovery
