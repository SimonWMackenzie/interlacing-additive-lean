import EthInapproximability.CurrentPaper.GenericPrefixComposite

namespace EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.PrefixCompositeEndpoint

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceBooleanPrefix SourceBooleanEncoding SourceClauseEncoding EncodedCNF
open PrefixCopy PrefixTransferFrame
open scoped Classical

private theorem fields_append (xs ys : List Clause) :
    clauseFields (xs ++ ys) = clauseFields xs ++ clauseFields ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [clauseFields,ih,List.append_assoc]

def sourceFields (n a q : Nat) : List Bool :=
  clauseFields (SourceGenericPrefix.atLeastChains n a q ++
    SourceGenericPrefix.pairChains n a q)

theorem final_pair_projection (n a q : Nat)
    (saved count : List Bool) (x : PairVertexLoopMachine.Stack) :
    PrefixComposite.finalBank n a q saved [] count
      (PrefixCopy.pairEmbedding x) =
    PairVertexLoopMachine.blank n n
      ((sourceFields n a q).reverse ++ saved) []
      (List.replicate ((3*a+2+8*(a*a))*n) true ++ count) [] x := by
  rw [PrefixComposite.finalBank,bank_at]
  have hs :
      (clauseFields (SourceGenericPrefix.pairChains n a q)).reverse ++
          PrefixComposite.atSaved n a q saved =
        (sourceFields n a q).reverse ++ saved := by
    simp only [PrefixComposite.atSaved,sourceFields,fields_append,
      List.reverse_append,List.append_assoc]
  have hc : List.replicate ((8*(a*a))*n) true ++
      PrefixComposite.atCount n a count =
      List.replicate ((3*a+2+8*(a*a))*n) true ++ count := by
    unfold PrefixComposite.atCount
    rw [← List.append_assoc,← List.replicate_add]
    congr 1
    ring
  rw [hs,hc]

theorem final_at_preserved (n a q : Nat)
    (saved count : List Bool) (x : PrefixLoopMachine.Stack) :
    PrefixComposite.finalBank n a q saved [] count
      (PrefixCopy.atEmbedding x) =
    PrefixComposite.atBank n a q saved [] count x := by
  rw [PrefixComposite.finalBank,bank_outside]
  · exact paired_at _ _ _ _ x
  · rintro ⟨y,hy⟩
    cases hy

theorem final_scratch_empty (n a q : Nat)
    (saved count : List Bool) :
    PrefixComposite.finalBank n a q saved [] count PrefixCopy.scratch = [] := by
  rw [PrefixComposite.finalBank,bank_outside]
  · exact paired_scratch _ _ _ _
  · rintro ⟨y,hy⟩
    cases hy

theorem run_source (n a q : Nat) (saved count : List Bool) :
    ∃ T ≤ PrefixComposite.cost n a q saved [] count,
      ((advance (PrefixComposite.program a q))^[T])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel (.inr .copyScan))),
          ((((AtLeastLoopCallback.callback a q).initial,none),
            ((none,none),none)),
            ((PairVertexLoopCallback.routine a q).initial,none)),
          framedAt (PrefixLoopMachine.blank n 0 saved [] count [])⟩ :
          TM2.Cfg (fun _ : PrefixCopy.Stack => Bool) _ _) =
        ⟨none,
          ((((AtLeastLoopCallback.callback a q).initial,none),
            ((none,none),none)),
            ((PairVertexLoopCallback.routine a q).initial,none)),
          PrefixComposite.finalBank n a q saved [] count⟩ :=
  PrefixComposite.run n a q saved [] count rfl

#print axioms run_source
#print axioms final_pair_projection

end EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.PrefixCompositeEndpoint
