import EthInapproximability.CurrentPaper.OuterLevel0Prep
import EthInapproximability.CurrentPaper.NextDimsEmbedTN

/-! Lane owner:b-weighted-level-7, unit 2, segment 2c, piece 8: at level 0 the admitted
persistent writer 18 of owner-4's `readyProgram` exit bank holds the `NextDimsMachineTN` input
`nv = 4 * bins P0 * |V|`. Proof replays owner-5's `writer28` argument. -/

namespace EthInapproximability.CurrentPaper.Level0DimsInputs2

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Ready
open OuterLevel0Prep

noncomputable section

set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

variable (M : BitMachine.Machine)
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Writer 18 holds unary `nv = 4 * bins P0 * |V|`. -/
theorem writer18 (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool)
    (hf : level0Facts M G n c F Q P) :
    G4 (level0RowsBank M G n c F Q P) (Sum.inl (wc 18)) =
      List.replicate (4 * Parameters.bins (P0 G n c) * Fintype.card V) true := by
  have h := ready_writer M G n c F Q P hf (.inl (.inl 18)) (by decide)
  have h' : G4 (level0RowsBank M G n c F Q P) (Sum.inl (wc 18)) = _ := h
  rw [h']
  show MatrixWeightedOrderPreparation.sourceBank _ _ _ _ 18 = _
  rw [WeightedLevel0Target.sb_other _ _ _ _ 18 (by decide)]
  simp [MatrixWeightedEntryController.persistentBank]
  rfl

#print axioms writer18

end
end EthInapproximability.CurrentPaper.Level0DimsInputs2
