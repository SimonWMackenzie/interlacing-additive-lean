import EthInapproximability.CurrentPaper.GenericPairGateExecute
import EthInapproximability.CurrentPaper.GenericPrefixGateSemantic
import EthInapproximability.CurrentPaper.SourceClausePrefixSharedClear

namespace EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.PairGateCleanup

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceBooleanPrefix SourceBooleanEncoding SourceClauseEncoding EncodedCNF SourceGenericPrefix
open scoped Classical

abbrev Stack := PairUnitLift.Stack

def emitted {n a : Nat} (v : Fin n) (bit : Fin a)
    (position ordinal w : Nat) (sign : Bool) : List EncodedCNF.Clause :=
  orGate (ordinal*w+(n*a+position)) ⟨bitIndex v bit,sign⟩

noncomputable def localBank {n a : Nat} (v : Fin n) (bit : Fin a)
    (position ordinal w : Nat) (sign : Bool)
    (saved output count : List Bool) : PrefixSharedCore.Stack → List Bool :=
  fun x => PairGateExecute.finished v bit position ordinal w sign
    saved output count (PairGateBase.coreEmbedding x)

noncomputable def program :=
  fun l => stackStmt PairGateBase.coreEmbedding (PrefixSharedClear.program l)

theorem finished_ordinal {n a : Nat} (v : Fin n) (bit : Fin a)
    (position ordinal w : Nat) (sign : Bool)
    (saved output count : List Bool) :
    PairGateExecute.finished v bit position ordinal w sign saved output count
      PairUnitLift.pairOrdinalCell = List.replicate ordinal true := by
  rw [PairGateExecute.finished, bank_outside]
  · change PairGatePrep.ready v bit w ordinal position saved output count
      PairGatePatch.ordinal = _
    rw [PairGatePrep.ready,
      Function.update_of_ne PairGatePatch.ordinal_ne_offset,
      PairGatePrep.copied,
      Function.update_of_ne PairGatePatch.ordinal_ne_index]
    exact PairGatePrep.cleared_ordinal v bit w ordinal saved output count
  · rintro ⟨x, hx⟩
    cases hx

theorem final_n {n a : Nat} (v : Fin n) (bit : Fin a)
    (position ordinal w : Nat) (sign : Bool)
    (saved output count : List Bool) :
    SourceClauseRowGate.finalBank (0 : Fin 1) (vertexFrame v)
      v.val a bit.val n position ordinal w sign saved output count
      PrefixSharedCore.gateN = List.replicate n true := by
  rw [SourceClauseRowGate.finalBank,
    show PrefixSharedCore.gateN =
      SourceClauseRowGate.gateEmbedding (.inl 0) by rfl,
    bank_at]
  rw [SourceClauseGateSlotAddress.finalBank, bank_outside]
  · simp [SourceClauseGateSlotAddress.transferred,
      BitMachineBroadcast.copied,
      SourceClauseGateSlotAddress.offsetDone,
      SourceClauseGateSlotAddress.offsetOutput,
      SourceClauseGateSlotAddress.offsetSource,
      SourceClauseGateSlotAddress.temp,
      SourceClauseGateSlotAddress.targets,
      SourceClauseGateSlotAddress.affineOffset,
      MatrixAddressMachine.cfg]
  · intro ⟨x, hx⟩
    cases hx

theorem local_core {n a : Nat} (v : Fin n) (bit : Fin a)
    (position ordinal w : Nat) (sign : Bool)
    (saved output count : List Bool) (i : PrefixSharedCore.Core) :
    localBank v bit position ordinal w sign saved output count (.inl i) =
      PrefixGateReady.coreWords n v.val
        ((clauseFields (emitted v bit position ordinal w sign)).reverse ++ saved)
        output (true :: true :: true :: count) i := by
  have he : PairGateBase.coreEmbedding (.inl i) =
      PairGateExecute.gateEmbedding (PrefixSharedCore.gateCore i) := by
    simp only [PairGateExecute.gateEmbedding,
      PairGateBase.coreEmbedding, Function.Embedding.trans_apply]
    exact (SourceClauseSharedCore.left_core PrefixSharedCore.gateCore
      PrefixSharedCore.unitCore i).symm ▸ rfl
  rw [localBank, PairGateExecute.finished, he, bank_at]
  fin_cases i
  · exact final_n v bit position ordinal w sign saved output count
  · exact SourceClauseRowGate.final_row (0 : Fin 1) (vertexFrame v)
      v.val a bit.val n position ordinal w sign saved output count
      (vertexFrame_query v) (.inl ((0 : Fin 1), 1))
  · have h := SourceClauseRowGate.final_saved (0 : Fin 1) (vertexFrame v)
      v.val a bit.val n position ordinal w sign saved output count
    simpa [PrefixSharedCore.gateCore,PrefixSharedCore.gateCoreCell,
      PrefixGateClean.savedCell,PrefixGateReady.coreWords,emitted,
      GateSemantic.bitIndex_val,orGate,
      SourceClauseGatePrepare.firstClause,
      SourceClauseGatePrepare.secondClause,
      SourceClauseGatePrepare.thirdClause,
      clauseFields,List.reverse_append,List.append_assoc] using h
  · change SourceClauseRowGate.finalBank (0 : Fin 1) (vertexFrame v)
      v.val a bit.val n position ordinal w sign saved output count
      PrefixGateClean.outputCell = output
    simp only [PrefixGateClean.outputCell,
      SourceClauseRowGate.finalBank, bank_at,
      SourceClauseGateSlotAddress.final_output]
  · exact SourceClauseRowGate.final_count (0 : Fin 1) (vertexFrame v)
      v.val a bit.val n position ordinal w sign saved output count

theorem result_eq_blank {n a : Nat} (v : Fin n) (bit : Fin a)
    (position ordinal w : Nat) (sign : Bool)
    (saved output count : List Bool) :
    SourceClauseClearExcept.result PrefixSharedClear.keep
      (localBank v bit position ordinal w sign saved output count) =
    PrefixGateReady.blank n v.val
      ((clauseFields (emitted v bit position ordinal w sign)).reverse ++ saved)
      output (true :: true :: true :: count) := by
  apply PrefixSharedClear.result_eq_blank
  intro i
  exact local_core v bit position ordinal w sign saved output count i

theorem final_bank {n a : Nat} (v : Fin n) (bit : Fin a)
    (position ordinal w : Nat) (sign : Bool)
    (saved output count : List Bool) :
    bank PairGateBase.coreEmbedding
      (PairGateExecute.finished v bit position ordinal w sign saved output count)
      (SourceClauseClearExcept.result PrefixSharedClear.keep
        (localBank v bit position ordinal w sign saved output count)) =
    PairUnitLift.pairBank n v.val ordinal
      ((clauseFields (emitted v bit position ordinal w sign)).reverse ++ saved)
      output (true :: true :: true :: count) := by
  rw [result_eq_blank]
  rw [← PairGateBase.gateBlank_eq_pairBank]
  funext x
  cases x with
  | inl y =>
      change bank PairGateBase.coreEmbedding _ _
        (PairGateBase.coreEmbedding y) =
        bank PairGateBase.coreEmbedding _ _
          (PairGateBase.coreEmbedding y)
      rw [bank_at, bank_at]
  | inr z =>
      cases z
      rw [bank_outside, PairGateBase.gateBlank, bank_outside]
      · simpa [PairGateBase.ordinalForeign] using
          finished_ordinal v bit position ordinal w sign saved output count
      · rintro ⟨y, hy⟩
        cases hy
      · rintro ⟨y, hy⟩
        cases hy

theorem run {n a : Nat} (v : Fin n) (bit : Fin a)
    (position ordinal w : Nat) (sign : Bool)
    (saved output count : List Bool) :
    let F := PairGateExecute.finished v bit position ordinal w sign
      saved output count
    ∃ u ≤ PrefixSharedClear.cost
        (localBank v bit position ordinal w sign saved output count),
      ((advance program)^[u])
        (⟨some (.clear 0), ((), none), F⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, ((), none),
          PairUnitLift.pairBank n v.val ordinal
            ((clauseFields (emitted v bit position ordinal w sign)).reverse ++ saved)
            output (true :: true :: true :: count)⟩ := by
  dsimp
  let F := PairGateExecute.finished v bit position ordinal w sign
    saved output count
  let L := localBank v bit position ordinal w sign saved output count
  have hr := PrefixSharedClear.run L
  have hs := BitMachineStackRun.run PairGateBase.coreEmbedding F
    PrefixSharedClear.program
    (⟨some (.clear 0), ((), none), L⟩ :
      TM2.Cfg (fun _ : PrefixSharedCore.Stack => Bool) _ _)
    (PrefixSharedClear.cost L)
  rw [hr] at hs
  have hstart : bank PairGateBase.coreEmbedding F L = F := by
    apply bank_eq_self
    intro x
    rfl
  simp only [stackCfg, hstart] at hs
  rw [final_bank v bit position ordinal w sign saved output count] at hs
  exact ⟨PrefixSharedClear.cost L, Nat.le_refl _, by
    simpa only [program, L, F] using hs⟩

#print axioms run

end EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.PairGateCleanup
