import CurrentAdditive.DeterministicETHPhysicalFixedBackend
import CurrentAdditive.DeterministicETHPhysicalSquare
import CurrentAdditive.DeterministicFixedIndexedSeedEndpoint

/-! The exact numbered successor rectangle is handed to one fixed physical
square/estimator/header/comparator machine. The only producer premise is that
a fixed machine prints this rectangle, with its complete charged clock. -/

namespace CurrentAdditive.DeterministicETHPhysicalFixedIndexedMain

set_option maxRecDepth 2048

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open CurrentAdditive.DeterministicParameters
open CurrentAdditive.DeterministicAdmissibility
open CurrentAdditive.DeterministicETHGapNo
open CurrentAdditive.DeterministicFixedDecision
open CurrentAdditive.DeterministicIteration
open CurrentAdditive.DeterministicEndpointAssembly
open CurrentAdditive.DeterministicETHConcreteIteration
open CurrentAdditive.DeterministicETHNumberedPresentation
open CurrentAdditive.IndexedExecutableStepRecovery
open CurrentAdditive.IndexedSemanticIteration
open CurrentAdditive.IndexedStagePresentation
open CurrentAdditive.DeterministicETHPhysicalSquare
open CurrentAdditive.DeterministicETHPhysicalFixedBackend
open CurrentAdditive.DeterministicETHEncodedTable
open CurrentAdditive.DeterministicFixedIndexedSeedEndpoint
open Paper2.Unit4Shell.T10Finite
open Paper2
open Workspace.Types.CommComplexity
open scoped Classical

noncomputable def machine (producer Me : BitMachine.Machine) (u : ℝ) : BitMachine.Machine :=
  BitMachineComposition.composition producer
    (CurrentAdditive.DeterministicETHPhysicalFixedBackend.machine Me (⌈2*u⌉₊+1))

universe uG uS

theorem matrix_square_eq {Graph : Type uG} {State : Type uS}
    (C : Construction Graph State) (N : ℕ)
    (P : TablePresentation C N) (R : State) (b : ℕ) :
    CurrentAdditive.DeterministicETHPhysicalFixedBackend.matrix
      (CurrentAdditive.DeterministicETHPhysicalFixedBackend.square
        (rectangleInstance (P.table R) b)) =
      squareWord (paddedTable C N P R) := by
  let I := rectangleInstance (P.table R) b
  have hsq : Paper2.ASquare.squareFun (P.rows R) (P.cols R)
      (MatrixMaterialization.rowMajor (P.table R)) =
      Paper2.SquarePadding.matrix (P.rows_pos R) (P.cols_pos R) (P.table R) := by
    rw [Paper2.ASquare.squareFun_eq_matrix (P.rows_pos R) (P.cols_pos R),
      rectangle_tableGame_rowMajor]
  simp only [CurrentAdditive.DeterministicETHPhysicalFixedBackend.matrix,
    CurrentAdditive.DeterministicETHPhysicalFixedBackend.square,
    Paper2.ASquare.squareInstance, rectangleInstance,
    AFront.Projection.matrixWord, squareWord, Paper2.AModel.matrixWord,
    paddedTable, hsq]

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))
  (Φ : ValidFormula) (L : ℕ)
  [NeZero (t10Graph D B Φ).vertices]
  [NeZero (s L)] [NeZero (s L-3)] [NeZero (q₁ L)]
  [NeZero (q₂ L)] [NeZero (w L)] [NeZero (Q L)]

theorem indexed_t10_fixed_physical_main
    (A C₁ C₀ : ℕ) (u : ℝ)
    (hL : L = publicLog (max (t10Graph D B Φ).vertices Φ.val.variables)
      B.degreeBound (sourceGap D B))
    (T : Schedule (Fin (t10Graph D B Φ).vertices)
      (Fin (t10Graph D B Φ).edges.length) L)
    (inputs : ∀ R : Stage (N L),
      StepInputs (V := Fin (t10Graph D B Φ).vertices)
        (E := Fin (t10Graph D B Φ).edges.length) L R T)
    (numberings : ∀ R : Stage (N L), ExplicitNumberings R)
    (hA : 2 ≤ A) (hC₀ : 2*C₁+2 ≤ C₀)
    (hresource : ResourceContract
      (indexedActualConstruction (t10Graph D B Φ).vertices
        (t10Graph D B Φ).edges.length L T inputs)
      (CanonicalEdgeTape.graphEdge (t10Graph D B Φ)
        (t10Graph_valid D B Φ)) (N L) A C₁)
    (est : List Bool → List Bool) (hest : AccurateFixed est u)
    (producer Me : BitMachine.Machine) (tproducer Te : ℕ)
    (hproducer :
      let G := CanonicalEdgeTape.graphEdge (t10Graph D B Φ)
        (t10Graph_valid D B Φ)
      let C := indexedActualConstruction (t10Graph D B Φ).vertices
        (t10Graph D B Φ).edges.length L T inputs
      let P := indexedActualNumberedTables (t10Graph D B Φ).vertices
        (t10Graph D B Φ).edges.length L T inputs numberings
      let k := ⌈2*u⌉₊+1
      let R := state C G k
      producer.OutputsWithin (EncodedCNF.encode Φ.val)
        (encodeInstance (rectangleInstance (P.table R)
          (budget (Paper2.LookupSeed.exponent L+1) (h L) k))) tproducer)
    (hMe :
      let G := CanonicalEdgeTape.graphEdge (t10Graph D B Φ)
        (t10Graph_valid D B Φ)
      let C := indexedActualConstruction (t10Graph D B Φ).vertices
        (t10Graph D B Φ).edges.length L T inputs
      let P := indexedActualNumberedTables (t10Graph D B Φ).vertices
        (t10Graph D B Φ).edges.length L T inputs numberings
      let k := ⌈2*u⌉₊+1
      let R := state C G k
      Me.OutputsWithin (squareWord (paddedTable C (N L) P R))
        (est (squareWord (paddedTable C (N L) P R))) Te) :
    let G := CanonicalEdgeTape.graphEdge (t10Graph D B Φ)
      (t10Graph_valid D B Φ)
    let C := indexedActualConstruction (t10Graph D B Φ).vertices
      (t10Graph D B Φ).edges.length L T inputs
    let P := indexedActualNumberedTables (t10Graph D B Φ).vertices
      (t10Graph D B Φ).edges.length L T inputs numberings
    let k := ⌈2*u⌉₊+1
    let R := state C G k
    let I := rectangleInstance (P.table R)
      (budget (Paper2.LookupSeed.exponent L+1) (h L) k)
    let out := est (squareWord (paddedTable C (N L) P R))
    (machine producer Me u).OutputsWithin (EncodedCNF.encode Φ.val)
      [decide (EncodedCNF.Satisfiable Φ.val)]
      (tproducer + 2*(encodeInstance I).length+2 +
        CurrentAdditive.DeterministicETHPhysicalFixedBackend.clock I k out Te) := by
  let G := CanonicalEdgeTape.graphEdge (t10Graph D B Φ)
    (t10Graph_valid D B Φ)
  let C := indexedActualConstruction (t10Graph D B Φ).vertices
    (t10Graph D B Φ).edges.length L T inputs
  let P := indexedActualNumberedTables (t10Graph D B Φ).vertices
    (t10Graph D B Φ).edges.length L T inputs numberings
  let k := ⌈2*u⌉₊+1
  let R := state C G k
  let I := rectangleInstance (P.table R)
    (budget (Paper2.LookupSeed.exponent L+1) (h L) k)
  let out := est (squareWord (paddedTable C (N L) P R))
  have hmid := indexed_t10_fixed_midpoint D B Φ L A C₁ C₀ u
    hL T inputs numberings hA hC₀ hresource est hest
  obtain ⟨z, hz, hy, hn, _⟩ := hmid
  have hbit : decide (z < (I.threshold:ℝ)+(k:ℝ)/2) =
      decide (EncodedCNF.Satisfiable Φ.val) := by
    by_cases hs : EncodedCNF.Satisfiable Φ.val
    · have hlt : z < (I.threshold:ℝ)+(k:ℝ)/2 := by
        simpa [I, k] using hy hs
      simp [hs, hlt]
    · have hnot : ¬ z < (I.threshold:ℝ)+(k:ℝ)/2 := by
        have hlt := hn hs
        exact not_lt_of_ge (le_of_lt (by simpa [I, k] using hlt))
      simp [hs, hnot]
  have hI : I.Valid := rectangleInstance_valid (P.table R) _
    (P.rows_pos R) (P.cols_pos R)
  have hEst : Me.OutputsWithin
      (CurrentAdditive.DeterministicETHPhysicalFixedBackend.matrix
        (CurrentAdditive.DeterministicETHPhysicalFixedBackend.square I)) out Te := by
    change Me.OutputsWithin (squareWord (paddedTable C (N L) P R)) out Te at hMe
    change Me.OutputsWithin
      (CurrentAdditive.DeterministicETHPhysicalFixedBackend.matrix
        (CurrentAdditive.DeterministicETHPhysicalFixedBackend.square
          (rectangleInstance (P.table R)
            (budget (Paper2.LookupSeed.exponent L+1) (h L) k)))) out Te
    rw [matrix_square_eq C (N L) P R
      (budget (Paper2.LookupSeed.exponent L+1) (h L) k)]
    exact hMe
  have hBack := CurrentAdditive.DeterministicETHPhysicalFixedBackend.machine_outputs
    Me k (by dsimp [k]; omega) I hI out Te hEst z hz
  rw [hbit] at hBack
  have hComp := BitMachineComposition.composition_outputsWithin
    producer (CurrentAdditive.DeterministicETHPhysicalFixedBackend.machine Me k)
    hproducer hBack
  simpa only [machine, k, I, out] using hComp

#print axioms indexed_t10_fixed_physical_main

end CurrentAdditive.DeterministicETHPhysicalFixedIndexedMain
