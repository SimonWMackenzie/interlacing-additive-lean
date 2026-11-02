import EthInapproximability.CurrentPaper.SourceClausePairSignedGate
import EthInapproximability.CurrentPaper.SourceClausePrefixGateReady

namespace EthInapproximability.CurrentPaper.SourceBooleanPrefix.PairGateBase

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceBooleanEncoding
open scoped Classical

abbrev Stack := PairUnitLift.Stack
abbrev CoreStack := PrefixSharedCore.Stack

def coreEmbedding : CoreStack ↪ Stack := Function.Embedding.inl

def ordinalForeign (ordinal : Nat) : Stack → List Bool
  | .inl _ => []
  | .inr _ => List.replicate ordinal true

noncomputable def gateBlank (n v ordinal : Nat)
    (saved output count : List Bool) : Stack → List Bool :=
  bank coreEmbedding (ordinalForeign ordinal)
    (PrefixGateReady.blank n v saved output count)

theorem gateBlank_eq_pairBank (n v ordinal : Nat)
    (saved output count : List Bool) :
    gateBlank n v ordinal saved output count =
      PairUnitLift.pairBank n v ordinal saved output count := by
  funext x
  cases x with
  | inr i =>
      cases i
      rw [gateBlank, bank_outside]
      · rw [show (Sum.inr () : Stack) = PairUnitLift.pairOrdinalCell by rfl,
          PairUnitLift.ordinal_word]
        rfl
      · rintro ⟨k, hk⟩
        cases hk
  | inl y =>
      by_cases hy : y = PairUnitLift.ordinalCell
      · subst y
        rw [gateBlank]
        change bank coreEmbedding (ordinalForeign ordinal)
          (PrefixGateReady.blank n v saved output count)
          (coreEmbedding PairUnitLift.ordinalCell) = _
        rw [bank_at]
        change List.replicate v true =
          PairUnitLift.pairBank n v ordinal saved output count
            PairUnitLift.vertexCell
        exact (PairUnitLift.vertex_word n v ordinal saved output count).symm
      · rw [gateBlank]
        change bank coreEmbedding (ordinalForeign ordinal)
          (PrefixGateReady.blank n v saved output count)
          (coreEmbedding y) = _
        rw [bank_at]
        have hu : PairUnitLift.unitEmbedding y = (.inl y : Stack) := by
          simp [PairUnitLift.unitEmbedding, hy]
        rw [← hu, PairUnitLift.pairBank, bank_at]
        cases y with
        | inl i =>
            fin_cases i <;> simp [PrefixGateReady.blank,
              PrefixGateReady.coreWords, PairUnitLift.ordinalCell] at hy ⊢
        | inr z =>
            rfl

noncomputable def preparationProgram (bit : Fin 2) (w : Nat) :=
  fun l => stackStmt coreEmbedding
    (PrefixGateOperands.preparationProgram bit.val w l)

theorem preparation_run {n q : Nat} (v : Fin n)
    (bit : Fin 2) (ordinal : Nat)
    (saved output count : List Bool) :
    ∃ t ≤ PrefixGateOperands.preparationCost bit.val (width 2 q + 1)
      (List.replicate v.val true),
      ((advance (preparationProgram bit (width 2 q + 1)))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (SourceClauseFixedBatch.labelAt
            (PrefixGateOperands.constantSize bit.val (width 2 q + 1)) 0)),
          ((), ((), none)),
          PairUnitLift.pairBank n v.val ordinal saved output count⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, ((), ((), none)),
          bank coreEmbedding (ordinalForeign ordinal)
            (PrefixGateReady.prepared (q := q) v bit
              saved output count)⟩ := by
  obtain ⟨t, ht, hrun⟩ := PrefixGateReady.prepared_run (q := q) v bit
    saved output count
  have h := BitMachineStackRun.run coreEmbedding
    (ordinalForeign ordinal)
    (PrefixGateOperands.preparationProgram bit.val (width 2 q + 1))
    (⟨some (BitMachineRawSequence.leftLabel
      (SourceClauseFixedBatch.labelAt
        (PrefixGateOperands.constantSize bit.val (width 2 q + 1)) 0)),
      ((), ((), none)), PrefixGateReady.blank n v.val saved output count⟩ :
      TM2.Cfg (fun _ : CoreStack => Bool) _ _) t
  rw [hrun] at h
  refine ⟨t, ht, ?_⟩
  have hb : bank coreEmbedding (ordinalForeign ordinal)
      (PrefixGateReady.blank n v.val saved output count) =
      PairUnitLift.pairBank n v.val ordinal saved output count :=
    gateBlank_eq_pairBank n v.val ordinal saved output count
  simp only [stackCfg, hb] at h
  simpa only [preparationProgram] using h

end EthInapproximability.CurrentPaper.SourceBooleanPrefix.PairGateBase
