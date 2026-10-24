import EthInapproximability.CurrentPaper.GenericPrefixLoopSource

namespace EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.PrefixLoopEndpoint

open Turing BitMachineEncoding
open SourceBooleanPrefix SourceBooleanEncoding SourceClauseEncoding EncodedCNF
open scoped Classical

theorem atLeast_run (n a q : Nat) (saved output count : List Bool) :
    ∃ t ≤ 2*n+2+AtLeastLoop.tailCost n a q saved output count 0 n,
      ((advance (AtLeastLoopCallback.program a q))^[t])
        (⟨some (.inr .copyScan),
          ((AtLeastLoopCallback.callback a q).initial,none),
          PrefixLoopMachine.blank n 0 saved output count []⟩ :
          PrefixLoopMachine.Config _ _) =
        ⟨none,((AtLeastLoopCallback.callback a q).initial,none),
          PrefixLoopMachine.blank n n
            ((clauseFields (SourceGenericPrefix.atLeastChains n a q)).reverse ++ saved)
            output (List.replicate ((3*a+2)*n) true ++ count) []⟩ := by
  obtain ⟨t,ht,hr⟩ := AtLeastLoop.run n a q saved output count
  exact ⟨t,ht,by simpa only [PrefixLoopSource.atLeast_fields] using hr⟩

theorem pair_run (n a q : Nat) (saved output count : List Bool) :
    ∃ t ≤ 2*n+2+PairVertexLoop.tailCost n a q saved output count 0 n,
      ((advance (PairVertexLoopCallback.program a q))^[t])
        (⟨some (.inr .copyScan),
          ((PairVertexLoopCallback.routine a q).initial,none),
          PairVertexLoopMachine.blank n 0 saved output count []⟩ :
          PairVertexLoopMachine.Config
            (PairVertexLoopCallback.routine a q).Label
            (PairVertexLoopCallback.routine a q).Control) =
        ⟨none,((PairVertexLoopCallback.routine a q).initial,none),
          PairVertexLoopMachine.blank n n
            ((clauseFields (SourceGenericPrefix.pairChains n a q)).reverse ++ saved)
            output (List.replicate ((8*(a*a))*n) true ++ count) []⟩ := by
  obtain ⟨t,ht,hr⟩ := PairVertexLoop.run n a q saved output count
  exact ⟨t,ht,by simpa only [PrefixLoopSource.pair_fields] using hr⟩

#print axioms atLeast_run
#print axioms pair_run

end EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.PrefixLoopEndpoint
