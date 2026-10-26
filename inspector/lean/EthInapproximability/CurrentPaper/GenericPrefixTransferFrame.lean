import EthInapproximability.CurrentPaper.GenericPrefixCopy
import EthInapproximability.CurrentPaper.SourcePairTarget

namespace EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.PrefixTransferFrame

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceBooleanPrefix PrefixCopy
open scoped Classical

def emptyForeign : PrefixCopy.Stack → List Bool := fun _ => []

noncomputable def framedAt (B : PrefixLoopMachine.Stack → List Bool) :
    PrefixCopy.Stack → List Bool :=
  bank PrefixCopy.atEmbedding emptyForeign B

def atN : PrefixCopy.Stack := PrefixCopy.atEmbedding PrefixLoopMachine.source
def atSaved : PrefixCopy.Stack := PrefixCopy.atEmbedding (.inl (.inl 2))
def atCount : PrefixCopy.Stack := PrefixCopy.atEmbedding (.inl (.inl 4))
def pairN : PrefixCopy.Stack :=
  PrefixCopy.pairEmbedding PairVertexLoopMachine.source
def pairSaved : PrefixCopy.Stack :=
  PrefixCopy.pairEmbedding (.inl (.inl (.inl 2)))
def pairCount : PrefixCopy.Stack :=
  PrefixCopy.pairEmbedding (.inl (.inl (.inl 4)))

noncomputable def paired (B : PrefixLoopMachine.Stack → List Bool)
    (n : Nat) (saved count : List Bool) : PrefixCopy.Stack → List Bool :=
  Function.update
    (Function.update
      (Function.update (framedAt B) pairN (List.replicate n true))
      pairSaved saved)
    pairCount count

theorem framed_at (B : PrefixLoopMachine.Stack → List Bool)
    (x : PrefixLoopMachine.Stack) :
    framedAt B (PrefixCopy.atEmbedding x) = B x := by
  exact bank_at PrefixCopy.atEmbedding emptyForeign B x

theorem framed_pair_empty (B : PrefixLoopMachine.Stack → List Bool)
    (x : PairVertexLoopMachine.Stack) :
    framedAt B (PrefixCopy.pairEmbedding x) = [] := by
  rw [framedAt,bank_outside]
  · rfl
  · rintro ⟨y,hy⟩
    cases hy

theorem framed_scratch_empty (B : PrefixLoopMachine.Stack → List Bool) :
    framedAt B PrefixCopy.scratch = [] := by
  rw [framedAt,bank_outside]
  · rfl
  · rintro ⟨y,hy⟩
    cases hy

theorem paired_at (B : PrefixLoopMachine.Stack → List Bool)
    (n : Nat) (saved count : List Bool) (x : PrefixLoopMachine.Stack) :
    paired B n saved count (PrefixCopy.atEmbedding x) = B x := by
  have hn : PrefixCopy.atEmbedding x ≠ pairN := by
    intro h; cases h
  have hs : PrefixCopy.atEmbedding x ≠ pairSaved := by
    intro h; cases h
  have hc : PrefixCopy.atEmbedding x ≠ pairCount := by
    intro h; cases h
  rw [paired,Function.update_of_ne hc,Function.update_of_ne hs,
    Function.update_of_ne hn]
  exact framed_at B x

theorem paired_projection (B : PrefixLoopMachine.Stack → List Bool)
    (n : Nat) (saved count : List Bool)
    (x : PairVertexLoopMachine.Stack) :
    paired B n saved count (PrefixCopy.pairEmbedding x) =
      PairVertexLoopMachine.blank n 0 saved [] count [] x := by
  rw [SourcePairBridge.blank_eq_updates]
  have hbank : bank PrefixCopy.pairEmbedding (framedAt B)
      SourcePairBridge.emptyPair = framedAt B := by
    apply bank_eq_self
    intro y
    exact (framed_pair_empty B y).symm
  have hupdate : bank PrefixCopy.pairEmbedding (framedAt B)
      (SourcePairBridge.localUpdates n saved count) =
      paired B n saved count := by
    simp only [SourcePairBridge.localUpdates,bank_update,hbank]
    rfl
  rw [← hupdate,bank_at]

theorem paired_scratch (B : PrefixLoopMachine.Stack → List Bool)
    (n : Nat) (saved count : List Bool) :
    paired B n saved count PrefixCopy.scratch = [] := by
  have hn : PrefixCopy.scratch ≠ pairN := by
    simp [PrefixCopy.scratch,pairN,PrefixCopy.pairEmbedding]
  have hs : PrefixCopy.scratch ≠ pairSaved := by
    simp [PrefixCopy.scratch,pairSaved,PrefixCopy.pairEmbedding]
  have hc : PrefixCopy.scratch ≠ pairCount := by
    simp [PrefixCopy.scratch,pairCount,PrefixCopy.pairEmbedding]
  rw [paired,Function.update_of_ne hc,Function.update_of_ne hs,
    Function.update_of_ne hn]
  exact framed_scratch_empty B

#print axioms paired_projection

end EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.PrefixTransferFrame
