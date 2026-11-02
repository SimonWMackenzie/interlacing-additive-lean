import CurrentAdditive.DeterministicETHPhysicalSquare

/-! Once a physical producer prints the exact encoded rectangle, the fixed
square postprocessor and any fixed polynomial-time estimator form one physical
machine. This records both serialization handoffs and their composition
charges; it does not supply the rectangle producer. -/

namespace CurrentAdditive.DeterministicETHPhysicalEstimator

open EthInapproximability.CurrentPaper
open CurrentAdditive.DeterministicETHPhysicalSquare
open CurrentAdditive.DeterministicETHEncodedTable
open CurrentAdditive.DeterministicEndpointAssembly

theorem padded_estimator_outputs
    {Graph State : Type}
    (C : CurrentAdditive.DeterministicIteration.Construction Graph State)
    (N : ℕ) (P : TablePresentation C N) (R : State) (b : ℕ)
    (producer : BitMachine.Machine) (input : List Bool) (tproducer : ℕ)
    (hproducer : producer.OutputsWithin input
      (EncodedCommunication.encodeInstance (rectangleInstance (P.table R) b))
      tproducer)
    (est : List Bool → List Bool) (hpoly : BitMachine.Polytime est) :
    ∃ (M : BitMachine.Machine) (Ce Ee : ℕ),
      M.OutputsWithin input
        (est (squareWord (paddedTable C N P R)))
        (tproducer +
          2 * (EncodedCommunication.encodeInstance
            (rectangleInstance (P.table R) b)).length + 2 +
          (Paper2.ASquare.Post.fullBound (P.rows R) (P.cols R) b +
            2 * (EncodedCommunication.encodeInstance
              (Paper2.ASquare.squareInstance
                (rectangleInstance (P.table R) b))).length + 2 +
            3 * ((EncodedCommunication.encodeInstance
              (Paper2.ASquare.squareInstance
                (rectangleInstance (P.table R) b))).length + 1)) +
          2 * (squareWord (paddedTable C N P R)).length + 2 +
          Ce * ((squareWord (paddedTable C N P R)).length + 1)^Ee) := by
  obtain ⟨Me, Ce, Ee, hMe⟩ := hpoly
  let M := BitMachineComposition.composition
    (BitMachineComposition.composition producer squareMatrixMachine) Me
  refine ⟨M, Ce, Ee, ?_⟩
  have hpost := paddedTable_outputs C N P R b
  have hfirst := BitMachineComposition.composition_outputsWithin
    producer squareMatrixMachine hproducer hpost
  have hlast := BitMachineComposition.composition_outputsWithin
    (BitMachineComposition.composition producer squareMatrixMachine) Me
    hfirst (hMe (squareWord (paddedTable C N P R)))
  simpa only [M] using hlast

#print axioms padded_estimator_outputs

/-- The machine is fixed before any graph, stage, table or input is chosen.
Only the actual rectangle-producing machine and the estimator determine it. -/
theorem uniform_padded_estimator_outputs
    (producer : BitMachine.Machine)
    (est : List Bool → List Bool) (hpoly : BitMachine.Polytime est) :
    ∃ (M : BitMachine.Machine) (Ce Ee : ℕ),
      ∀ {Graph State : Type}
        (C : CurrentAdditive.DeterministicIteration.Construction Graph State)
        (N : ℕ) (P : TablePresentation C N) (R : State) (b : ℕ)
        (input : List Bool) (tproducer : ℕ),
        producer.OutputsWithin input
          (EncodedCommunication.encodeInstance (rectangleInstance (P.table R) b))
          tproducer →
        M.OutputsWithin input
          (est (squareWord (paddedTable C N P R)))
          (tproducer +
            2 * (EncodedCommunication.encodeInstance
              (rectangleInstance (P.table R) b)).length + 2 +
            (Paper2.ASquare.Post.fullBound (P.rows R) (P.cols R) b +
              2 * (EncodedCommunication.encodeInstance
                (Paper2.ASquare.squareInstance
                  (rectangleInstance (P.table R) b))).length + 2 +
              3 * ((EncodedCommunication.encodeInstance
                (Paper2.ASquare.squareInstance
                  (rectangleInstance (P.table R) b))).length + 1)) +
            2 * (squareWord (paddedTable C N P R)).length + 2 +
            Ce * ((squareWord (paddedTable C N P R)).length + 1)^Ee) := by
  obtain ⟨Me, Ce, Ee, hMe⟩ := hpoly
  let M := BitMachineComposition.composition
    (BitMachineComposition.composition producer squareMatrixMachine) Me
  refine ⟨M, Ce, Ee, ?_⟩
  intro Graph State C N P R b input tproducer hproducer
  have hpost := paddedTable_outputs C N P R b
  have hfirst := BitMachineComposition.composition_outputsWithin
    producer squareMatrixMachine hproducer hpost
  have hlast := BitMachineComposition.composition_outputsWithin
    (BitMachineComposition.composition producer squareMatrixMachine) Me
    hfirst (hMe (squareWord (paddedTable C N P R)))
  simpa only [M] using hlast

#print axioms uniform_padded_estimator_outputs

end CurrentAdditive.DeterministicETHPhysicalEstimator
