import EthInapproximability.CurrentPaper.SourceGenericPairVertex
import EthInapproximability.CurrentPaper.SourceClausePairVertexLoopMachine

namespace EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.PairVertexLoopCallback

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceBooleanPrefix SourceBooleanEncoding SourceClauseEncoding EncodedCNF
open SourceGenericPairEnumeration SourceBooleanPrefix.PairMachineComposition
open scoped Classical

noncomputable def routine (a q : Nat) : Routine := vertexRoutine a q

noncomputable def program (a q : Nat) :=
  PairVertexLoopMachine.program (routine a q).program
    (routine a q).start (routine a q).initial

theorem blank_bank (n v : Nat)
    (saved saved' output count count' fuelWord : List Bool) :
    bank PairVertexLoopMachine.core
      (PairVertexLoopMachine.blank n v saved output count fuelWord)
      (PairUnitLift.pairBank n v 0 saved' output count') =
    PairVertexLoopMachine.blank n v saved' output count' fuelWord := by
  funext k
  cases k with
  | inl j => exact bank_at PairVertexLoopMachine.core _ _ j
  | inr i =>
      rw [bank_outside PairVertexLoopMachine.core _ _ (.inr i) (by
        intro h
        obtain ⟨j,hj⟩ := h
        cases hj)]
      rfl

theorem run {n a : Nat} (q : Nat) (v : Fin n)
    (saved output count fuelWord : List Bool) :
    ∃ u ≤ vertexCost a q v saved output count,
      ((advance (program a q))^[u])
        (⟨some (.inl (routine a q).start),
          ((routine a q).initial,none),
          PairVertexLoopMachine.blank n v.val
            saved output count fuelWord⟩ :
          PairVertexLoopMachine.Config (routine a q).Label
            (routine a q).Control) =
        ⟨some (.inr .increment),
          ((routine a q).initial,none),
          PairVertexLoopMachine.blank n v.val
            ((clauseFields (vertexChains a q v)).reverse ++ saved)
            output (List.replicate (8*(a*a)) true ++ count)
            fuelWord⟩ := by
  let R := routine a q
  obtain ⟨t,ht,h⟩ := vertex_run q v saved output count
  let C : TM2.Cfg (fun _ : PairVertexLoopMachine.CoreStack => Bool)
      R.Label R.Control :=
    ⟨some R.start,R.initial,
      PairUnitLift.pairBank n v.val 0 saved output count⟩
  have hhalt : (((advance R.program)^[t]) C).l = none := by
    simpa only [R,routine,C] using congrArg TM2.Cfg.l h
  obtain ⟨u,hu,hr⟩ := BitMachineStackEmbedding.outputs
    PairVertexLoopMachine.core
    (PairVertexLoopMachine.blank n v.val saved output count fuelWord)
    Sum.inl (fun x => (x,none)) Prod.fst
    (by intro x; rfl) (some (.inr .increment))
    R.program (program a q) (by intro l; rfl) C t hhalt
  refine ⟨u,hu.trans ht,?_⟩
  have h' : ((advance R.program)^[t]) C =
      ⟨none,R.initial,
        PairUnitLift.pairBank n v.val 0
          ((clauseFields (vertexChains a q v)).reverse ++ saved)
          output (List.replicate (8*(a*a)) true ++ count)⟩ := by
    simpa only [R,routine,C] using h
  rw [h'] at hr
  simpa only [program,R,routine,C,
    BitMachineStackEmbedding.cfg,BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg,blank_bank] using hr

#print axioms run

end EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.PairVertexLoopCallback
