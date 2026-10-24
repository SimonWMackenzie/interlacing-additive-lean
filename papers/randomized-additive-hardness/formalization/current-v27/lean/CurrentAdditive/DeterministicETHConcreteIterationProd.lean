import CurrentAdditive.DeterministicETHGraphScheduleProd
import CurrentAdditive.DeterministicETHSeedStageProd

/-! The actual Boolean-cube seed and literal indexed source successor as a
single iterated construction.  Step inputs are the concrete source data
delivered by the Code D producer; the NO-side restoration and resource
claims are proved separately on this same construction. -/

namespace CurrentAdditive.DeterministicETHConcreteIteration

open CurrentAdditive.DeterministicParameters
open CurrentAdditive.IndexedStagePresentation
open CurrentAdditive.IndexedSemanticIteration
open CurrentAdditive.DeterministicIteration
open CurrentAdditive.DeterministicETHSeedStage
open Workspace.Types.CommComplexity

variable (v e L : ℕ) [NeZero v] [NeZero (s L)] [NeZero (s L-3)]
  [NeZero (q₁ L)] [NeZero (q₂ L)] [NeZero (w L)] [NeZero (Q L)]

noncomputable def actualConstruction
    (T : Schedule (Fin v) (Fin e) L)
    (inputs : ∀ R : Stage (N L), StepInputs (V := Fin v) (E := Fin e) L R T) :
    Construction (IndexedSemanticIteration.Graph (Fin v) (Fin e)) (Stage (N L)) :=
  construction L T (fun _ => seedStage L) inputs

theorem actual_seed_cost
    (T : Schedule (Fin v) (Fin e) L)
    (inputs : ∀ R : Stage (N L), StepInputs (V := Fin v) (E := Fin e) L R T)
    (G : IndexedSemanticIteration.Graph (Fin v) (Fin e)) :
    (actualConstruction v e L T inputs).cost
      ((actualConstruction v e L T inputs).seed G) =
      Paper2.LookupSeed.exponent L + 1 := seedStage_cost L

theorem actual_seed_profile
    (T : Schedule (Fin v) (Fin e) L)
    (inputs : ∀ R : Stage (N L), StepInputs (V := Fin v) (E := Fin e) L R T)
    (G : IndexedSemanticIteration.Graph (Fin v) (Fin e)) :
    (actualConstruction v e L T inputs).profile G
      ((actualConstruction v e L T inputs).seed G) :=
  seedStage_profile_public L

theorem actual_valid
    (T : Schedule (Fin v) (Fin e) L)
    (inputs : ∀ R : Stage (N L), StepInputs (V := Fin v) (E := Fin e) L R T)
    (G : IndexedSemanticIteration.Graph (Fin v) (Fin e)) :
    ValidContract (actualConstruction v e L T inputs) G :=
  IndexedSemanticIteration.valid L T (fun _ => seedStage L) inputs G

theorem actual_universal
    (T : Schedule (Fin v) (Fin e) L)
    (inputs : ∀ R : Stage (N L), StepInputs (V := Fin v) (E := Fin e) L R T)
    (G : IndexedSemanticIteration.Graph (Fin v) (Fin e)) :
    UniversalContract (actualConstruction v e L T inputs) G
      (Paper2.LookupSeed.exponent L + 1) (h L) :=
  IndexedSemanticIteration.universal L T (fun _ => seedStage L)
    inputs G (Paper2.LookupSeed.exponent L + 1) (le_of_eq (seedStage_cost L))

theorem actual_yes
    (T : Schedule (Fin v) (Fin e) L)
    (inputs : ∀ R : Stage (N L), StepInputs (V := Fin v) (E := Fin e) L R T)
    (G : IndexedSemanticIteration.Graph (Fin v) (Fin e))
    (colour : Fin v → Fin 3)
    (proper : ∀ z, colour (G z false) ≠ colour (G z true)) :
    YesContract (actualConstruction v e L T inputs) G
      (Paper2.LookupSeed.exponent L + 1) (h L) :=
  IndexedSemanticIteration.yes L T (fun _ => seedStage L)
    inputs G (Paper2.LookupSeed.exponent L + 1) (le_of_eq (seedStage_cost L))
    colour proper

noncomputable def actualTables
    (T : Schedule (Fin v) (Fin e) L)
    (inputs : ∀ R : Stage (N L), StepInputs (V := Fin v) (E := Fin e) L R T) :
    CurrentAdditive.DeterministicEndpointAssembly.TablePresentation
      (actualConstruction v e L T inputs) (N L) :=
  IndexedSemanticIteration.tables L T (fun _ => seedStage L) inputs

#print axioms actualConstruction
#print axioms actual_seed_cost
#print axioms actual_seed_profile
#print axioms actual_universal
#print axioms actual_yes
#print axioms actualTables

end CurrentAdditive.DeterministicETHConcreteIteration

namespace CurrentAdditive.DeterministicETHConcreteIteration

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open CurrentAdditive.DeterministicParameters
open CurrentAdditive.IndexedSemanticIteration
open CurrentAdditive.DeterministicIteration
open Paper2
open Paper2.Unit4Shell.T10Finite

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))
  (Φ : ValidFormula) (L : ℕ)
  [NeZero (t10Graph D B Φ).vertices]
  [NeZero (s L)] [NeZero (s L-3)] [NeZero (q₁ L)]
  [NeZero (q₂ L)] [NeZero (w L)] [NeZero (Q L)]

/-- The source formula's YES promise gives a colouring of the very graph
fed to the literal successor, hence the cheaper bound at every stage. -/
theorem actual_t10_yes
    (T : Schedule (Fin (t10Graph D B Φ).vertices)
      (Fin (t10Graph D B Φ).edges.length) L)
    (inputs : ∀ R : IndexedStagePresentation.Stage (N L),
      StepInputs (V := Fin (t10Graph D B Φ).vertices)
        (E := Fin (t10Graph D B Φ).edges.length) L R T)
    (hSAT : EncodedCNF.Satisfiable Φ.val) :
    YesContract
      (actualConstruction (t10Graph D B Φ).vertices
        (t10Graph D B Φ).edges.length L T inputs)
      (CanonicalEdgeTape.graphEdge (t10Graph D B Φ)
        (t10Graph_valid D B Φ))
      (Paper2.LookupSeed.exponent L + 1) (h L) := by
  obtain ⟨_, _, _, _, _, hyes, _⟩ := t10_source D B Φ
  obtain ⟨colour, proper⟩ := hyes hSAT
  exact actual_yes (t10Graph D B Φ).vertices
    (t10Graph D B Φ).edges.length L T inputs
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ)
      (t10Graph_valid D B Φ)) colour proper

#print axioms actual_t10_yes

end CurrentAdditive.DeterministicETHConcreteIteration
