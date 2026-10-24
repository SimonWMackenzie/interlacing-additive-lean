import EthInapproximability.CurrentPaper.SourceClausePrefixLoopPolynomial
import EthInapproximability.CurrentPaper.SourceCSPEntryWrapper
import EthInapproximability.CurrentPaper.SourceCSPPositiveHeader

/-!
An isolated physical bank for preparing the at-least prefix from one raw CSP
input. The three components are disjoint: the untouched row-wrapper input,
the actual guarded header/count/cap machine, and the finite-control prefix
loop. The last cell is a reusable physical copy scratch stack.
-/

namespace EthInapproximability.CurrentPaper.SourcePrefixRawFrame

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.CurrentPaper.SourceBooleanPrefix
open scoped Classical

abbrev Stack (q : Nat) :=
  SourceCSPEntryWrapper.Ambient q ⊕
    (SourceCSPPositiveHeader.Stack ⊕
      (PrefixLoopMachine.Stack ⊕ Fin 1))

def entryEmbedding {q : Nat} : SourceCSPEntryWrapper.Ambient q ↪ Stack q :=
  ⟨Sum.inl, Sum.inl_injective⟩

def headerEmbedding {q : Nat} : SourceCSPPositiveHeader.Stack ↪ Stack q where
  toFun k := .inr (.inl k)
  inj' := by intro x y h; exact Sum.inl.inj (Sum.inr.inj h)

def prefixEmbedding {q : Nat} : PrefixLoopMachine.Stack ↪ Stack q where
  toFun k := .inr (.inr (.inl k))
  inj' := by intro x y h; exact Sum.inl.inj (Sum.inr.inj (Sum.inr.inj h))

def scratch {q : Nat} : Stack q := .inr (.inr (.inr 0))

def headerInput : SourceCSPPositiveHeader.Stack :=
  .inl (.inl (.inl (.inr 0)))

def entryInput {q : Nat} : SourceCSPEntryWrapper.Ambient q :=
  .inl (.inl (.inl headerInput))

def headerVertex {q : Nat} : Stack q := headerEmbedding (.inr 6)
def prefixVertex {q : Nat} : Stack q :=
  prefixEmbedding PrefixLoopMachine.source

def prefixSaved {q : Nat} : Stack q :=
  prefixEmbedding (.inl (.inl 2))
def prefixCount {q : Nat} : Stack q :=
  prefixEmbedding (.inl (.inl 4))

def entrySaved {q : Nat} : Stack q :=
  entryEmbedding (SourceCSPEntryWrapper.stash 0)
def entryCount {q : Nat} : Stack q :=
  entryEmbedding (SourceCSPEntryWrapper.stash 2)

noncomputable def initial (q : Nat) (input : List Bool) : Stack q → List Bool :=
  Sum.elim (SourceCSPEntryWrapper.initial q input [] [] []).stk
    (fun _ => [])

theorem initial_entry (q : Nat) (input : List Bool)
    (k : SourceCSPEntryWrapper.Ambient q) :
    initial q input (entryEmbedding k) =
      (SourceCSPEntryWrapper.initial q input [] [] []).stk k := by
  rfl

theorem initial_header (q : Nat) (input : List Bool)
    (k : SourceCSPPositiveHeader.Stack) :
    initial q input (headerEmbedding k) = [] := by
  rfl

theorem initial_prefix (q : Nat) (input : List Bool)
    (k : PrefixLoopMachine.Stack) :
    initial q input (prefixEmbedding k) = [] := by
  rfl

theorem initial_scratch (q : Nat) (input : List Bool) :
    initial q input scratch = [] := by
  rfl

theorem entry_raw_input (q : Nat) (input : List Bool) :
    initial q input (entryEmbedding entryInput) = input := by
  rw [initial_entry]
  rw [SourceCSPEntryWrapper.initial_exact]
  change (bank SourceCSPEntryWrapper.firstEmbedding
      (SourceCSPEntryWrapper.foreign q [] [] [])
      (SourceCSPFirstRowController.initial 2 q input).stk)
      (SourceCSPEntryWrapper.firstEmbedding (.inl (.inl headerInput))) = input
  rw [bank_at]
  change (SourceCSPSecondPassGlobalLift.initial 2 q input).stk
    (.inl (.inl headerInput)) = input
  rw [SourceCSPSecondPassGlobalLift.initial_left]
  rfl

theorem initial_stash_blank (q : Nat) (input : List Bool) (i : Fin 4) :
    initial q input (entryEmbedding (SourceCSPEntryWrapper.stash i)) = [] := by
  rw [initial_entry, SourceCSPEntryWrapper.initial_exact]
  change bank SourceCSPEntryWrapper.firstEmbedding
    (SourceCSPEntryWrapper.foreign q [] [] [])
    (SourceCSPFirstRowController.initial 2 q input).stk (.inr i) = []
  rw [bank_outside]
  · fin_cases i <;> rfl
  · rintro ⟨k, hk⟩
    cases k with
    | inl g => cases hk
    | inr k => cases hk

theorem positive_header_initial_source (input : List Bool) :
    SourceCSPPositiveHeader.initial input headerInput = input := by
  rfl

theorem positive_header_initial_other (input : List Bool)
    (k : SourceCSPPositiveHeader.Stack) (hk : k ≠ headerInput) :
    SourceCSPPositiveHeader.initial input k = [] := by
  rcases k with ⟨k⟩ | ⟨k⟩
  · rcases k with ⟨k⟩ | ⟨k⟩
    · rcases k with ⟨k⟩ | ⟨k⟩
      · rcases k with ⟨k⟩ | ⟨k⟩
        · fin_cases k <;> rfl
        · fin_cases k <;> simp [headerInput, SourceCSPPositiveHeader.initial,
            SourceCSPInputFrame.initial, SourceCSPHeaderCheck.parserInitial,
            SourceCSPRowController.contents] at hk ⊢
      · fin_cases k <;> rfl
    · fin_cases k <;> rfl
  · fin_cases k <;> rfl

theorem prefix_blank_source (n : Nat) :
    PrefixLoopMachine.blank n 0 [] [] [] [] PrefixLoopMachine.source =
      List.replicate n true := by
  rfl

theorem prefix_blank_other (n : Nat) (k : PrefixLoopMachine.Stack)
    (hk : k ≠ PrefixLoopMachine.source) :
    PrefixLoopMachine.blank n 0 [] [] [] [] k = [] := by
  cases k with
  | inl c =>
    cases c with
    | inl i =>
      fin_cases i <;>
        simp [PrefixLoopMachine.source, PrefixLoopMachine.blank,
          PrefixGateReady.blank, PrefixGateReady.coreWords] at hk ⊢
    | inr r =>
      cases r with
      | inl i => rfl
      | inr i => rfl
  | inr i => fin_cases i <;> rfl

end EthInapproximability.CurrentPaper.SourcePrefixRawFrame
