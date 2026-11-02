import EthInapproximability.CurrentPaper.OuterLevel0Prep
import EthInapproximability.CurrentPaper.NextDimsEmbedT

/-! Lane owner:b-weighted-level-7, unit 2, segment 2c, piece 6: at level 0, the admitted
persistent writer cells 16, 17, 27 of owner-4's `readyProgram` exit bank (the same bank
owner-5's prep hands to the round) hold the dims-machine inputs `t = bins P0 * familySize P0`,
`rows P0`, `columns P0` (writer 28 = `bins P0` is owner-5 `writer28`). Proofs replay owner-5's
`writer28` argument (owner-4 `ready_writer`, `sb_other`, `persistentBank`). -/

namespace EthInapproximability.CurrentPaper.Level0DimsInputs

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

/-- Writer 16 holds unary `bins P0 * familySize P0` (= `stagePrefixRows = s * L`). -/
theorem writer16 (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool)
    (hf : level0Facts M G n c F Q P) :
    G4 (level0RowsBank M G n c F Q P) (Sum.inl (wc 16)) =
      List.replicate (Parameters.bins (P0 G n c) * EffectiveIteration.familySize (P0 G n c)) true := by
  have h := ready_writer M G n c F Q P hf (.inl (.inl 16)) (by decide)
  have h' : G4 (level0RowsBank M G n c F Q P) (Sum.inl (wc 16)) = _ := h
  rw [h']
  show MatrixWeightedOrderPreparation.sourceBank _ _ _ _ 16 = _
  rw [WeightedLevel0Target.sb_other _ _ _ _ 16 (by decide)]
  simp [MatrixWeightedEntryController.persistentBank]
  rfl

/-- Writer 17 holds unary `rows P0`. -/
theorem writer17 (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool)
    (hf : level0Facts M G n c F Q P) :
    G4 (level0RowsBank M G n c F Q P) (Sum.inl (wc 17)) =
      List.replicate (P0 G n c).rows true := by
  have h := ready_writer M G n c F Q P hf (.inl (.inl 17)) (by decide)
  have h' : G4 (level0RowsBank M G n c F Q P) (Sum.inl (wc 17)) = _ := h
  rw [h']
  show MatrixWeightedOrderPreparation.sourceBank _ _ _ _ 17 = _
  rw [WeightedLevel0Target.sb_other _ _ _ _ 17 (by decide)]
  simp [MatrixWeightedEntryController.persistentBank]
  rfl

/-- Writer 27 holds unary `columns P0`. -/
theorem writer27 (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool)
    (hf : level0Facts M G n c F Q P) :
    G4 (level0RowsBank M G n c F Q P) (Sum.inl (wc 27)) =
      List.replicate (P0 G n c).columns true := by
  have h := ready_writer M G n c F Q P hf (.inl (.inl 27)) (by decide)
  have h' : G4 (level0RowsBank M G n c F Q P) (Sum.inl (wc 27)) = _ := h
  rw [h']
  show MatrixWeightedOrderPreparation.sourceBank _ _ _ _ 27 = _
  rw [WeightedLevel0Target.sb_other _ _ _ _ 27 (by decide)]
  simp [MatrixWeightedEntryController.persistentBank]
  rfl

#print axioms writer16
#print axioms writer17
#print axioms writer27

end
end EthInapproximability.CurrentPaper.Level0DimsInputs
