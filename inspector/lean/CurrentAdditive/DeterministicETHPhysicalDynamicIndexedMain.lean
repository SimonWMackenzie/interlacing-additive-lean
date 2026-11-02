import CurrentAdditive.DeterministicETHPhysicalDynamicBackend
import CurrentAdditive.DeterministicETHPhysicalFixedMain
import CurrentAdditive.DeterministicETHIndexedSeedEndpoint
import CurrentAdditive.DeterministicETHPhysicalFixedIndexedMain

/-! One fixed physical decision machine for the growing-error ETH route.
The rectangle carries the dynamic midpoint numerator in its ordinary public
threshold field; no formula-dependent machine is selected. -/

namespace CurrentAdditive.DeterministicETHPhysicalDynamicIndexedMain

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open CurrentAdditive.DeterministicETHPhysicalSquare
open CurrentAdditive.DeterministicETHPhysicalDynamicBackend
open CurrentAdditive.DeterministicETHPhysicalFixedIndexedMain
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open CurrentAdditive.DeterministicParameters
open CurrentAdditive.DeterministicAdmissibility
open CurrentAdditive.DeterministicIteration
open CurrentAdditive.DeterministicEndpointAssembly
open CurrentAdditive.DeterministicETHConcreteIteration
open CurrentAdditive.DeterministicETHNumberedPresentation
open CurrentAdditive.IndexedExecutableStepRecovery
open CurrentAdditive.IndexedSemanticIteration
open CurrentAdditive.IndexedStagePresentation
open CurrentAdditive.DeterministicETHIndexedSeedEndpoint
open CurrentAdditive.DeterministicETHDecision
open CurrentAdditive.DeterministicETHEstimator
open CurrentAdditive.DeterministicETHGapNo
open CurrentAdditive.DeterministicETHEncodedTable
open Paper2.Unit4Shell.T10Finite
open Paper2
open Workspace.Types.CommComplexity
open scoped Classical

set_option maxRecDepth 2048

noncomputable def machine (producer Me : BitMachine.Machine) : BitMachine.Machine :=
  BitMachineComposition.composition producer
    (CurrentAdditive.DeterministicETHPhysicalDynamicBackend.machine Me)

noncomputable def clock (I : Instance) (out : List Bool)
    (tproducer Te : ℕ) : ℕ :=
  tproducer + 2*(encodeInstance I).length+2 +
    CurrentAdditive.DeterministicETHPhysicalDynamicBackend.clock I out Te

theorem decision_of_rectangle
    (producer Me : BitMachine.Machine)
    (input : List Bool) (tproducer Te B k : ℕ)
    {P : Prop} [Decidable P]
    {r c : ℕ} (F : Fin r → Fin c → Bool)
    (hr : 0 < r) (hc : 0 < c)
    (out : List Bool) (z : ℝ)
    (hproducer : producer.OutputsWithin input
      (encodeInstance (rectangleInstance F (2*B+k))) tproducer)
    (hMe : Me.OutputsWithin
      (CurrentAdditive.DeterministicETHPhysicalFixedBackend.matrix
        (CurrentAdditive.DeterministicETHPhysicalFixedBackend.square
          (rectangleInstance F (2*B+k)))) out Te)
    (hz : Paper2.AModel.decodeDyadic out = some z)
    (hy : P → z < (B:ℝ)+(k:ℝ)/2)
    (hn : ¬P → (B:ℝ)+(k:ℝ)/2 < z) :
    (machine producer Me).OutputsWithin input [decide P]
      (clock (rectangleInstance F (2*B+k)) out tproducer Te) := by
  let I := rectangleInstance F (2*B+k)
  have hi : I.Valid := rectangleInstance_valid F (2*B+k) hr hc
  have hback := CurrentAdditive.DeterministicETHPhysicalDynamicBackend.machine_outputs
    Me I hi out Te hMe z hz
  have hthreshold : (I.threshold:ℝ)/2 = (B:ℝ)+(k:ℝ)/2 := by
    dsimp [I, rectangleInstance]
    push_cast
    ring
  have hbit : decide (z < (I.threshold:ℝ)/2) = decide P := by
    by_cases hp : P
    · have hlt : z < (I.threshold:ℝ)/2 := by rw [hthreshold]; exact hy hp
      simp [hp, hlt]
    · have hnot : ¬z < (I.threshold:ℝ)/2 := by
        rw [hthreshold]
        exact not_lt_of_ge (le_of_lt (hn hp))
      simp [hp, hnot]
  rw [hbit] at hback
  have hcomp := BitMachineComposition.composition_outputsWithin
    producer (CurrentAdditive.DeterministicETHPhysicalDynamicBackend.machine Me)
    hproducer hback
  simpa only [machine, clock, I] using hcomp

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))
  (Φ : ValidFormula) (L : ℕ)
  [NeZero (t10Graph D B Φ).vertices]
  [NeZero (s L)] [NeZero (s L-3)] [NeZero (q₁ L)]
  [NeZero (q₂ L)] [NeZero (w L)] [NeZero (Q L)]

theorem indexed_t10_eth_physical_main
    (cs a C₁ C₀ : ℕ)
    (hsparse : Φ.val.clauses.length ≤ cs * Φ.val.variables)
    (hgraphlarge : CurrentAdditive.DeterministicETHSourceBridge.graphPolynomialCutoff
      D B cs ≤ Φ.val.variables)
    (hparamlarge : sourceCutoffSize B.degreeBound (sourceGap D B) ≤
      Φ.val.variables)
    (hL : L = publicLog (max (t10Graph D B Φ).vertices Φ.val.variables)
      B.degreeBound (sourceGap D B))
    (T : Schedule (Fin (t10Graph D B Φ).vertices)
      (Fin (t10Graph D B Φ).edges.length) L)
    (inputs : ∀ R : Stage (N L),
      StepInputs (V := Fin (t10Graph D B Φ).vertices)
        (E := Fin (t10Graph D B Φ).edges.length) L R T)
    (numberings : ∀ R : Stage (N L), ExplicitNumberings R)
    (ha : 1 ≤ a) (hC₀ : 2*C₁+2 ≤ C₀)
    (hlarge : 2^(max (32*(C₀*(D.sizeExponent+4))+16) (8*a)) ≤
      Φ.val.variables)
    (hresource : ResourceContract
      (indexedActualConstruction (t10Graph D B Φ).vertices
        (t10Graph D B Φ).edges.length L T inputs)
      (CanonicalEdgeTape.graphEdge (t10Graph D B Φ)
        (t10Graph_valid D B Φ)) (N L) (2^a) C₁)
    (est : List Bool → List Bool)
    (hest : EventuallyAccurate est (1/(4*(a:ℝ))))
    (hthreshold : hest.2.choose ≤ Φ.val.variables^2)
    (producer Me : BitMachine.Machine) (tproducer Te : ℕ)
    (hproducer :
      let G := CanonicalEdgeTape.graphEdge (t10Graph D B Φ)
        (t10Graph_valid D B Φ)
      let C := indexedActualConstruction (t10Graph D B Φ).vertices
        (t10Graph D B Φ).edges.length L T inputs
      let P := indexedActualNumberedTables (t10Graph D B Φ).vertices
        (t10Graph D B Φ).edges.length L T inputs numberings
      let k := CurrentAdditive.DeterministicEndpointNumeric.ethIterations a Φ.val.variables
      let R := state C G k
      let B₀ := budget (Paper2.LookupSeed.exponent L+1) (h L) k
      producer.OutputsWithin (EncodedCNF.encode Φ.val)
        (encodeInstance (rectangleInstance (P.table R) (2*B₀+k))) tproducer)
    (hMe :
      let G := CanonicalEdgeTape.graphEdge (t10Graph D B Φ)
        (t10Graph_valid D B Φ)
      let C := indexedActualConstruction (t10Graph D B Φ).vertices
        (t10Graph D B Φ).edges.length L T inputs
      let P := indexedActualNumberedTables (t10Graph D B Φ).vertices
        (t10Graph D B Φ).edges.length L T inputs numberings
      let k := CurrentAdditive.DeterministicEndpointNumeric.ethIterations a Φ.val.variables
      let R := state C G k
      Me.OutputsWithin (squareWord (paddedTable C (N L) P R))
        (est (squareWord (paddedTable C (N L) P R))) Te) :
    let G := CanonicalEdgeTape.graphEdge (t10Graph D B Φ)
      (t10Graph_valid D B Φ)
    let C := indexedActualConstruction (t10Graph D B Φ).vertices
      (t10Graph D B Φ).edges.length L T inputs
    let P := indexedActualNumberedTables (t10Graph D B Φ).vertices
      (t10Graph D B Φ).edges.length L T inputs numberings
    let k := CurrentAdditive.DeterministicEndpointNumeric.ethIterations a Φ.val.variables
    let R := state C G k
    let B₀ := budget (Paper2.LookupSeed.exponent L+1) (h L) k
    let I := rectangleInstance (P.table R) (2*B₀+k)
    let out := est (squareWord (paddedTable C (N L) P R))
    (machine producer Me).OutputsWithin (EncodedCNF.encode Φ.val)
      [decide (EncodedCNF.Satisfiable Φ.val)]
      (clock I out tproducer Te) := by
  let G := CanonicalEdgeTape.graphEdge (t10Graph D B Φ)
    (t10Graph_valid D B Φ)
  let C := indexedActualConstruction (t10Graph D B Φ).vertices
    (t10Graph D B Φ).edges.length L T inputs
  let P := indexedActualNumberedTables (t10Graph D B Φ).vertices
    (t10Graph D B Φ).edges.length L T inputs numberings
  let k := CurrentAdditive.DeterministicEndpointNumeric.ethIterations a Φ.val.variables
  let R := state C G k
  let B₀ := budget (Paper2.LookupSeed.exponent L+1) (h L) k
  let I := rectangleInstance (P.table R) (2*B₀+k)
  let out := est (squareWord (paddedTable C (N L) P R))
  obtain ⟨z, hz, hy, hn, _⟩ :=
    indexed_t10_eth_midpoint D B Φ L cs a C₁ C₀ hsparse
      hgraphlarge hparamlarge hL T inputs numberings ha hC₀ hlarge
      hresource est hest hthreshold
  have hEst : Me.OutputsWithin
      (CurrentAdditive.DeterministicETHPhysicalFixedBackend.matrix
        (CurrentAdditive.DeterministicETHPhysicalFixedBackend.square I)) out Te := by
    change Me.OutputsWithin (squareWord (paddedTable C (N L) P R)) out Te at hMe
    change Me.OutputsWithin
      (CurrentAdditive.DeterministicETHPhysicalFixedBackend.matrix
        (CurrentAdditive.DeterministicETHPhysicalFixedBackend.square
          (rectangleInstance (P.table R) (2*B₀+k)))) out Te
    rw [matrix_square_eq C (N L) P R (2*B₀+k)]
    exact hMe
  have hRun := decision_of_rectangle producer Me
    (EncodedCNF.encode Φ.val) tproducer Te B₀ k
    (P := EncodedCNF.Satisfiable Φ.val)
    (P.table R) (P.rows_pos R) (P.cols_pos R)
    out z hproducer hEst hz hy hn
  simpa only [I, out] using hRun

#print axioms decision_of_rectangle
#print axioms indexed_t10_eth_physical_main

end CurrentAdditive.DeterministicETHPhysicalDynamicIndexedMain
