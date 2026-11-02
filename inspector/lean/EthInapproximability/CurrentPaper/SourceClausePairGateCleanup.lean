import EthInapproximability.CurrentPaper.SourceClausePairGateExecute
import EthInapproximability.CurrentPaper.SourceClausePrefixSharedClear

namespace EthInapproximability.CurrentPaper.SourceBooleanPrefix.PairGateCleanup

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceBooleanEncoding SourceClauseEncoding EncodedCNF
open scoped Classical

abbrev Stack := PairUnitLift.Stack

noncomputable def localBank {n q : Nat} (v : Fin n) (s t ell : Fin 2)
    (saved output count : List Bool) : PrefixSharedCore.Stack → List Bool :=
  fun x => PairGateExecute.finished (q := q) v s t ell
    saved output count (PairGateBase.coreEmbedding x)

noncomputable def program :=
  fun l => stackStmt PairGateBase.coreEmbedding (PrefixSharedClear.program l)

theorem finished_ordinal {n q : Nat} (v : Fin n) (s t ell : Fin 2)
    (saved output count : List Bool) :
    PairGateExecute.finished (q := q) v s t ell saved output count
      PairUnitLift.pairOrdinalCell =
      List.replicate (pairOrdinal v s t) true := by
  rw [PairGateExecute.finished, bank_outside]
  · change PairGatePrep.ready (q := q) v
      (if ell = 0 then s else t) ell (pairOrdinal v s t)
      saved output count PairGatePatch.ordinal = _
    rw [PairGatePrep.ready,
      Function.update_of_ne PairGatePatch.ordinal_ne_offset,
      PairGatePrep.copied,
      Function.update_of_ne PairGatePatch.ordinal_ne_index]
    exact PairGatePrep.cleared_ordinal v
      (if ell = 0 then s else t) (pairOrdinal v s t)
      saved output count
  · rintro ⟨x, hx⟩
    cases hx

theorem final_n {n q : Nat} (v : Fin n) (s t ell : Fin 2)
    (saved output count : List Bool) :
    SourceClauseRowGate.finalBank (0 : Fin 1) (vertexFrame v)
      v.val 2 (if ell = 0 then s else t).val n ell.val
      (pairOrdinal v s t) (width 2 q + 1)
      (if ell = 0 then PairSignedGate.signFirst s t
        else PairSignedGate.signSecond s t)
      saved output count PrefixSharedCore.gateN =
      List.replicate n true := by
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

theorem local_core {n q : Nat} (v : Fin n) (s t ell : Fin 2)
    (saved output count : List Bool) (i : PrefixSharedCore.Core) :
    localBank (q := q) v s t ell saved output count (.inl i) =
      PrefixGateReady.coreWords n v.val
        ((clauseFields (PairSignedGate.emittedGate (q := q) v s t ell)).reverse ++ saved)
        output (true :: true :: true :: count) i := by
  have he : PairGateBase.coreEmbedding (.inl i) =
      PairGateExecute.gateEmbedding (PrefixSharedCore.gateCore i) := by
    simp only [PairGateExecute.gateEmbedding,
      PairGateBase.coreEmbedding, Function.Embedding.trans_apply]
    exact (SourceClauseSharedCore.left_core PrefixSharedCore.gateCore
      PrefixSharedCore.unitCore i).symm ▸ rfl
  rw [localBank, PairGateExecute.finished, he, bank_at]
  fin_cases i
  · exact final_n (q := q) v s t ell saved output count
  · exact SourceClauseRowGate.final_row (0 : Fin 1) (vertexFrame v)
      v.val 2 (if ell = 0 then s else t).val n ell.val
      (pairOrdinal v s t) (width 2 q + 1)
      (if ell = 0 then PairSignedGate.signFirst s t
        else PairSignedGate.signSecond s t)
      saved output count (vertexFrame_query v) (.inl ((0 : Fin 1), 1))
  · exact PairSignedGate.gate_saved (q := q) v s t ell
      saved output count
  · change SourceClauseRowGate.finalBank (0 : Fin 1) (vertexFrame v)
      v.val 2 (if ell = 0 then s else t).val n ell.val
      (pairOrdinal v s t) (width 2 q + 1)
      (if ell = 0 then PairSignedGate.signFirst s t
        else PairSignedGate.signSecond s t)
      saved output count PrefixGateClean.outputCell = output
    simp only [PrefixGateClean.outputCell,
      SourceClauseRowGate.finalBank, bank_at,
      SourceClauseGateSlotAddress.final_output]
  · exact SourceClauseRowGate.final_count (0 : Fin 1) (vertexFrame v)
      v.val 2 (if ell = 0 then s else t).val n ell.val
      (pairOrdinal v s t) (width 2 q + 1)
      (if ell = 0 then PairSignedGate.signFirst s t
        else PairSignedGate.signSecond s t)
      saved output count

theorem result_eq_blank {n q : Nat} (v : Fin n) (s t ell : Fin 2)
    (saved output count : List Bool) :
    SourceClauseClearExcept.result PrefixSharedClear.keep
      (localBank (q := q) v s t ell saved output count) =
    PrefixGateReady.blank n v.val
      ((clauseFields (PairSignedGate.emittedGate (q := q) v s t ell)).reverse ++ saved)
      output (true :: true :: true :: count) := by
  apply PrefixSharedClear.result_eq_blank
  intro i
  exact local_core (q := q) v s t ell saved output count i

theorem final_bank {n q : Nat} (v : Fin n) (s t ell : Fin 2)
    (saved output count : List Bool) :
    bank PairGateBase.coreEmbedding
      (PairGateExecute.finished (q := q) v s t ell saved output count)
      (SourceClauseClearExcept.result PrefixSharedClear.keep
        (localBank (q := q) v s t ell saved output count)) =
    PairUnitLift.pairBank n v.val (pairOrdinal v s t)
      ((clauseFields (PairSignedGate.emittedGate (q := q) v s t ell)).reverse ++ saved)
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
          finished_ordinal (q := q) v s t ell saved output count
      · rintro ⟨y, hy⟩
        cases hy
      · rintro ⟨y, hy⟩
        cases hy

theorem run {n q : Nat} (v : Fin n) (s t ell : Fin 2)
    (saved output count : List Bool) :
    let F := PairGateExecute.finished (q := q) v s t ell
      saved output count
    ∃ u ≤ PrefixSharedClear.cost
        (localBank (q := q) v s t ell saved output count),
      ((advance program)^[u])
        (⟨some (.clear 0), ((), none), F⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, ((), none),
          PairUnitLift.pairBank n v.val (pairOrdinal v s t)
            ((clauseFields (PairSignedGate.emittedGate (q := q) v s t ell)).reverse ++ saved)
            output (true :: true :: true :: count)⟩ := by
  dsimp
  let F := PairGateExecute.finished (q := q) v s t ell
    saved output count
  let L := localBank (q := q) v s t ell saved output count
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
  rw [final_bank (q := q) v s t ell saved output count] at hs
  exact ⟨PrefixSharedClear.cost L, Nat.le_refl _, by
    simpa only [program, L, F] using hs⟩

end EthInapproximability.CurrentPaper.SourceBooleanPrefix.PairGateCleanup
