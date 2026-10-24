import EthInapproximability.CurrentPaper.SourceClausePrefixLoopMachine

namespace EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixLoopCallback

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceBooleanEncoding SourceClauseEncoding EncodedCNF
open scoped Classical

private def labelOf {L V : Type*}
    (_ : L → TM2.Stmt (fun _ : PrefixLoopMachine.CoreStack => Bool) L V)
    (l : L) : L := l

noncomputable def start (q : ℕ) :=
  labelOf (PrefixFullCallback.program q) <|
  BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (SourceClauseFixedBatch.labelAt
              (PrefixUnitClean.constantSize (width 2 q + 1) 0) 0)))))

noncomputable def initial :=
  (((PrefixFirstTwoCycles.unitControl,
      PrefixFirstTwoCycles.gateControl),
      PrefixFirstTwoCycles.gateControl),
      PrefixFirstTwoCycles.unitControl)

noncomputable def program (q : ℕ) :=
  PrefixLoopMachine.program (PrefixFullCallback.program q) (start q) initial

theorem blank_bank (n v : ℕ) (saved saved' output count count' fuelWord : List Bool) :
    bank PrefixLoopMachine.core
      (PrefixLoopMachine.blank n v saved output count fuelWord)
      (PrefixGateReady.blank n v saved' output count') =
    PrefixLoopMachine.blank n v saved' output count' fuelWord := by
  funext k
  cases k with
  | inl j =>
    exact bank_at PrefixLoopMachine.core _ _ j
  | inr i =>
    rw [bank_outside PrefixLoopMachine.core _ _ (.inr i) (by
      intro h
      obtain ⟨j, hj⟩ := h
      cases hj)]
    rfl

theorem run {n q : ℕ} (v : Fin n) (saved output count fuelWord : List Bool) :
    ∃ t ≤ PrefixFullCallback.cost (q := q) v saved output count,
      ((advance (program q))^[t])
        (⟨some (.inl (start q)), (initial, none),
          PrefixLoopMachine.blank n v.val saved output count fuelWord⟩ :
          PrefixLoopMachine.Config _ _) =
        ⟨some (.inr .increment), (initial, none),
          PrefixLoopMachine.blank n v.val
            ((clauseFields (chain (base n q (atLeastOrdinal v))
              (atLeastPayload v))).reverse ++ saved)
            output (List.replicate 8 true ++ count) fuelWord⟩ := by
  obtain ⟨t, ht, h⟩ := PrefixFullCallback.run (q := q) v saved output count
  let C : TM2.Cfg (fun _ : PrefixLoopMachine.CoreStack => Bool) _ _ :=
    ⟨some (start q), initial, PrefixGateReady.blank n v.val saved output count⟩
  have hhalt : (((advance (PrefixFullCallback.program q))^[t]) C).l = none := by
    simpa only [C, start, initial] using congrArg TM2.Cfg.l h
  obtain ⟨u, hu, hr⟩ := BitMachineStackEmbedding.outputs
    PrefixLoopMachine.core
    (PrefixLoopMachine.blank n v.val saved output count fuelWord)
    Sum.inl (fun x => (x, none)) Prod.fst
    (by intro x; rfl) (some (.inr .increment))
    (PrefixFullCallback.program q) (program q)
    (by intro l; rfl) C t hhalt
  refine ⟨u, le_trans hu ht, ?_⟩
  change ((advance (PrefixFullCallback.program q))^[t]) C =
    ⟨none, initial, PrefixGateReady.blank n v.val
      ((clauseFields (chain (base n q (atLeastOrdinal v))
        (atLeastPayload v))).reverse ++ saved)
      output (List.replicate 8 true ++ count)⟩ at h
  rw [h] at hr
  simpa only [program, C, start, initial,
    BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg, blank_bank] using hr

#print axioms run

end EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixLoopCallback
