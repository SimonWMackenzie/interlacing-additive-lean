import EthInapproximability.CurrentPaper.SourcePairCopy
import EthInapproximability.CurrentPaper.SourceClausePairGateBase

namespace EthInapproximability.CurrentPaper.SourcePairBridge

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.CurrentPaper.SourceBooleanPrefix
open scoped Classical
set_option linter.unusedSimpArgs false

def localN : PairVertexLoopMachine.Stack := PairVertexLoopMachine.source
def localSaved : PairVertexLoopMachine.Stack := .inl (.inl (.inl 2))
def localCount : PairVertexLoopMachine.Stack := .inl (.inl (.inl 4))

def emptyPair : PairVertexLoopMachine.Stack → List Bool := fun _ => []

noncomputable def localUpdates (n : Nat) (saved count : List Bool) :
    PairVertexLoopMachine.Stack → List Bool :=
  Function.update
    (Function.update
      (Function.update emptyPair localN (List.replicate n true))
      localSaved saved)
    localCount count

theorem blank_eq_updates (n : Nat) (saved count : List Bool) :
    PairVertexLoopMachine.blank n 0 saved [] count [] =
      localUpdates n saved count := by
  funext x
  cases x with
  | inr i =>
      fin_cases i <;>
        simp [PairVertexLoopMachine.blank, localUpdates,
          localN, localSaved, localCount, emptyPair,
          PairVertexLoopMachine.source, Function.update]
  | inl y =>
      rw [PairVertexLoopMachine.blank]
      change PairUnitLift.pairBank n 0 0 saved [] count y = _
      rw [← PairGateBase.gateBlank_eq_pairBank]
      cases y with
      | inr u =>
          cases u
          rw [PairGateBase.gateBlank, bank_outside]
          · simp [localUpdates, localN, localSaved,
              localCount, emptyPair, PairGateBase.ordinalForeign,
              PairVertexLoopMachine.source, Function.update]
          · rintro ⟨k, hk⟩
            cases hk
      | inl z =>
          change bank PairGateBase.coreEmbedding
            (PairGateBase.ordinalForeign 0)
            (PrefixGateReady.blank n 0 saved [] count)
            (PairGateBase.coreEmbedding z) = _
          rw [bank_at]
          cases z with
          | inl i =>
              fin_cases i <;>
                simp [PrefixGateReady.blank,
                  PrefixGateReady.coreWords,
                  localUpdates, localN, localSaved,
                  localCount, emptyPair,
                  PairVertexLoopMachine.source, Function.update]
          | inr g =>
              simp [PrefixGateReady.blank, localUpdates,
                localN, localSaved, localCount, emptyPair,
                PairVertexLoopMachine.source, Function.update]

noncomputable def paired (S : SourcePrefixRawFrame.Stack q → List Bool)
    (n : Nat) (saved count : List Bool) : Stack q → List Bool :=
  Function.update
    (Function.update
      (Function.update (framedRaw S) pairN (List.replicate n true))
      pairSaved saved)
    pairCount count

theorem paired_projection (S : SourcePrefixRawFrame.Stack q → List Bool)
    (n : Nat) (saved count : List Bool)
    (x : PairVertexLoopMachine.Stack) :
    paired S n saved count (pairEmbedding x) =
      PairVertexLoopMachine.blank n 0 saved [] count [] x := by
  rw [blank_eq_updates]
  have hbank : bank pairEmbedding (framedRaw S) emptyPair =
      framedRaw S := by
    apply bank_eq_self
    intro y
    exact (framed_pair_empty S y).symm
  have hupdate : bank pairEmbedding (framedRaw S)
      (localUpdates n saved count) = paired S n saved count := by
    simp only [localUpdates, bank_update, hbank]
    rfl
  rw [← hupdate, bank_at]

end EthInapproximability.CurrentPaper.SourcePairBridge
