import EthInapproximability.CurrentPaper.GenericPairGatePrep

namespace EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.PairGateReady

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceBooleanPrefix
open scoped Classical

def rawIndex : PrefixSharedCore.Gate :=
  .inr (.inl (.inr (.inl (.inl 0))))
def rawOffset : PrefixSharedCore.Gate :=
  .inr (.inl (.inl 2))

theorem rawIndex_eq : rawIndex = PrefixGateOperands.gateIndexLocal := rfl
theorem rawOffset_eq : rawOffset =
    SourceClauseRowGate.gateEmbedding (.inl 2) := rfl
theorem raw_index_ne_offset : rawIndex ≠ rawOffset := by
  simp [rawIndex,rawOffset]

theorem raw_initial_update {n a : Nat} (v : Fin n) (bit : Fin a)
    (position ordinal w : Nat) (saved output count : List Bool) :
    SourceClauseRowGate.initial (vertexFrame v)
      v.val a bit.val n position ordinal w saved output count =
    Function.update
      (Function.update
        (SourceClauseRowGate.initial (vertexFrame v)
          v.val a bit.val n bit.val v.val w saved output count)
        rawIndex (List.replicate ordinal true))
      rawOffset (List.replicate position true) := by
  funext x
  by_cases ho : x = rawOffset
  · subst x
    simp only [Function.update_self]
    rfl
  by_cases hi : x = rawIndex
  · subst x
    simp only [Function.update_of_ne raw_index_ne_offset,
      Function.update_self]
    rfl
  simp [Function.update,ho,hi]
  cases x with
  | inl y => rfl
  | inr z =>
      cases z with
      | inr i => rfl
      | inl g =>
          cases g with
          | inl b =>
              fin_cases b <;>
                simp_all [rawOffset,SourceClauseRowGate.initial,
                  SourceClauseGateSlotAddress.initial,
                  SourceClauseGateSlotAddress.offsetInput,
                  MatrixAddressMachine.cfg,rawOffset]
          | inr b =>
              cases b with
              | inr c => rfl
              | inl c =>
                  cases c with
                  | inl d =>
                      fin_cases d <;>
                        simp_all [rawIndex,SourceClauseRowGate.initial,
                          SourceClauseGateSlotAddress.initial,
                          SourceClauseGateAffineAddress.initial,
                          SourceLabelAddressMachine.inputs,
                          SourceLabelAddressMachine.ambient]
                  | inr d => rfl

theorem ready_gate_at {n a : Nat} (v : Fin n) (bit : Fin a)
    (position ordinal w : Nat) (saved output count : List Bool)
    (x : SourceClauseRowGate.Stack 1) :
    PairGatePrep.ready v bit w ordinal position saved output count
      (SourceBooleanPrefix.PairGateBase.coreEmbedding
        (PrefixSharedCore.gateEmbedding x)) =
    SourceClauseRowGate.initial (vertexFrame v)
      v.val a bit.val n position ordinal w
      saved output count x := by
  rw [raw_initial_update]
  by_cases ho : x = rawOffset
  · subst x
    simp only [Function.update_self]
    change PairGatePrep.ready v bit w ordinal position saved output count
      PairGatePatch.gateOffset = _
    simp [PairGatePrep.ready]
  by_cases hi : x = rawIndex
  · subst x
    simp only [Function.update_of_ne raw_index_ne_offset,
      Function.update_self]
    change PairGatePrep.ready v bit w ordinal position saved output count
      PairGatePatch.gateIndex = _
    simp [PairGatePrep.ready,PairGatePrep.copied,
      PairGatePatch.index_ne_offset]
  have hio : SourceBooleanPrefix.PairGateBase.coreEmbedding
      (PrefixSharedCore.gateEmbedding x) ≠ PairGatePatch.gateOffset := by
    intro h
    apply ho
    exact PrefixSharedCore.gateEmbedding.injective
      (SourceBooleanPrefix.PairGateBase.coreEmbedding.injective h)
  have hii : SourceBooleanPrefix.PairGateBase.coreEmbedding
      (PrefixSharedCore.gateEmbedding x) ≠ PairGatePatch.gateIndex := by
    intro h
    apply hi
    exact PrefixSharedCore.gateEmbedding.injective
      (SourceBooleanPrefix.PairGateBase.coreEmbedding.injective h)
  rw [Function.update_of_ne ho,Function.update_of_ne hi]
  rw [PairGatePrep.ready,Function.update_of_ne hio,
    PairGatePrep.copied,Function.update_of_ne hii]
  rw [PairGatePrep.cleared,BitMachineClearBank.cleared_foreign]
  · rw [PairGatePrep.prepared,bank_at,GateReady.gate_ready]
  · intro i
    fin_cases i
    · exact Ne.symm hii
    · exact Ne.symm hio

#print axioms ready_gate_at

end EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.PairGateReady
