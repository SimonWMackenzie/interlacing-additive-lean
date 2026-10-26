import EthInapproximability.CurrentPaper.GenericPrefixAtLeastClock
import EthInapproximability.CurrentPaper.SourceClausePrefixLoopMachine

namespace EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.AtLeastLoopCallback

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceBooleanPrefix SourceBooleanEncoding SourceClauseEncoding EncodedCNF
open scoped Classical

noncomputable def callback (a q : Nat) := AtLeastCircuit.atLeastCircuit a q

noncomputable def program (a q : Nat) :=
  PrefixLoopMachine.program (callback a q).program
    (callback a q).start (callback a q).initial

theorem blank_bank (n v : Nat)
    (saved saved' output count count' fuelWord : List Bool) :
    bank PrefixLoopMachine.core
      (PrefixLoopMachine.blank n v saved output count fuelWord)
      (PrefixGateReady.blank n v saved' output count') =
    PrefixLoopMachine.blank n v saved' output count' fuelWord := by
  funext k
  cases k with
  | inl j => exact bank_at PrefixLoopMachine.core _ _ j
  | inr i =>
      rw [bank_outside PrefixLoopMachine.core _ _ (.inr i) (by
        intro h
        obtain ⟨j,hj⟩ := h
        cases hj)]
      rfl

theorem run {n a q : Nat} (v : Fin n)
    (saved output count fuelWord : List Bool) :
    ∃ t ≤ AtLeastClock.cost (a := a) (q := q) v saved output count,
      ((advance (program a q))^[t])
        (⟨some (.inl (callback a q).start),
          ((callback a q).initial, none),
          PrefixLoopMachine.blank n v.val saved output count fuelWord⟩ :
          PrefixLoopMachine.Config _ _) =
        ⟨some (.inr .increment), ((callback a q).initial, none),
          PrefixLoopMachine.blank n v.val
            ((clauseFields (chain
              (SourceGenericPrefix.base n a q v.val)
              (SourceGenericPrefix.atLeastPayload (a := a) v))).reverse ++ saved)
            output (List.replicate (3*a+2) true ++ count) fuelWord⟩ := by
  obtain ⟨t,ht,h⟩ := AtLeastClock.source_bounded (a := a) (q := q)
    v saved output count
  let A := callback a q
  let C : TM2.Cfg (fun _ : PrefixLoopMachine.CoreStack => Bool) _ _ :=
    ⟨some A.start,A.initial,PrefixGateReady.blank n v.val saved output count⟩
  have hhalt : (((advance A.program)^[t]) C).l = none := by
    simpa only [C,A,callback] using congrArg TM2.Cfg.l h
  obtain ⟨u,hu,hr⟩ := BitMachineStackEmbedding.outputs
    PrefixLoopMachine.core
    (PrefixLoopMachine.blank n v.val saved output count fuelWord)
    Sum.inl (fun x => (x,none)) Prod.fst
    (by intro x; rfl) (some (.inr .increment))
    A.program (program a q) (by intro l; rfl) C t hhalt
  refine ⟨u,le_trans hu ht,?_⟩
  change ((advance A.program)^[t]) C =
    ⟨none,A.initial,PrefixGateReady.blank n v.val
      ((clauseFields (chain
        (SourceGenericPrefix.base n a q v.val)
        (SourceGenericPrefix.atLeastPayload (a := a) v))).reverse ++ saved)
      output (List.replicate (3*a+2) true ++ count)⟩ at h
  rw [h] at hr
  simpa only [program,C,A,callback,
    BitMachineStackEmbedding.cfg,BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg,blank_bank] using hr

#print axioms run

end EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.AtLeastLoopCallback
