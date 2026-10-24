import EthInapproximability.CurrentPaper.GenericPrefixAmbientCopy

namespace EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.PrefixAmbientSeed

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceBooleanPrefix PrefixAmbientCopy PrefixTransferFrame
open scoped Classical

def rawVertex {q : Nat} : PrefixAmbientCopy.Stack q :=
  rawEmbedding q (.inr SourceClauseRowWriterOperands.vertex)
def rawSaved {q : Nat} : PrefixAmbientCopy.Stack q :=
  rawEmbedding q (.inr SourceClauseRowWriterCleanup.savedCell)
def rawCount {q : Nat} : PrefixAmbientCopy.Stack q :=
  rawEmbedding q (.inr SourceClauseRowWriterCleanup.countCell)
def workN {q : Nat} : PrefixAmbientCopy.Stack q :=
  workEmbedding q atN
def workSaved {q : Nat} : PrefixAmbientCopy.Stack q :=
  workEmbedding q pairSaved
def workCount {q : Nat} : PrefixAmbientCopy.Stack q :=
  workEmbedding q pairCount

noncomputable def initial {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool) :
    PrefixAmbientCopy.Stack q → List Bool :=
  bank (rawEmbedding q) (fun _ => []) U

noncomputable def seed {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool) (n : Nat) :
    PrefixAmbientCopy.Stack q → List Bool :=
  Function.update (initial U) workN (List.replicate n true)

theorem initial_raw {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (x : SourceCSPFirstRowController.Stack q) :
    initial U (rawEmbedding q x) = U x :=
  bank_at (rawEmbedding q) (fun _ => []) U x

theorem initial_work {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (x : PrefixCopy.Stack) :
    initial U (workEmbedding q x) = [] := by
  rw [initial,bank_outside (rawEmbedding q) (fun _ => []) U
    (workEmbedding q x) (by rintro ⟨y,hy⟩; cases hy)]

theorem initial_scratch {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool) :
    initial U (scratch q) = [] := by
  rw [initial,bank_outside (rawEmbedding q) (fun _ => []) U
    (scratch q) (by rintro ⟨y,hy⟩; cases hy)]

theorem blank_other (n : Nat) (x : PrefixLoopMachine.Stack)
    (hx : x ≠ PrefixLoopMachine.source) :
    PrefixLoopMachine.blank n 0 [] [] [] [] x = [] := by
  cases x with
  | inr i => fin_cases i <;> rfl
  | inl y =>
    cases y with
    | inr z => rfl
    | inl i =>
      fin_cases i <;>
        simp_all [PrefixLoopMachine.source,PrefixLoopMachine.blank,
          PrefixGateReady.blank,PrefixGateReady.coreWords]

theorem framed_other (n : Nat) (x : PrefixCopy.Stack)
    (hx : x ≠ atN) :
    framedAt (PrefixLoopMachine.blank n 0 [] [] [] []) x = [] := by
  by_cases h : ∃ y, PrefixCopy.atEmbedding y = x
  · obtain ⟨y,rfl⟩ := h
    rw [framed_at]
    exact blank_other n y (by
      intro he
      exact hx (congrArg PrefixCopy.atEmbedding he))
  · rw [framedAt,bank_outside _ _ _ x h]
    rfl

theorem seed_work {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (n : Nat) (x : PrefixCopy.Stack) :
    seed U n (workEmbedding q x) =
      framedAt (PrefixLoopMachine.blank n 0 [] [] [] []) x := by
  by_cases hx : x = atN
  · subst x
    simp only [seed,workN,Function.update_self]
    change List.replicate n true =
      framedAt (PrefixLoopMachine.blank n 0 [] [] [] [])
        (PrefixCopy.atEmbedding PrefixLoopMachine.source)
    rw [framed_at]
    rfl
  · have hwork : workEmbedding q x ≠ workN := by
      intro h
      exact hx ((workEmbedding q).injective h)
    rw [seed,Function.update_of_ne hwork,initial_work]
    exact (framed_other n x hx).symm

theorem seed_raw {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (n : Nat) (x : SourceCSPFirstRowController.Stack q) :
    seed U n (rawEmbedding q x) = U x := by
  have h : rawEmbedding q x ≠ workN := by
    intro he
    cases he
  rw [seed,Function.update_of_ne h,initial_raw]

#print axioms seed_work
#print axioms seed_raw

end EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.PrefixAmbientSeed
