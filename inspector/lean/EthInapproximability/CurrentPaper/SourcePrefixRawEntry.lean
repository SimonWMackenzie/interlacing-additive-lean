import EthInapproximability.CurrentPaper.SourcePrefixRawStash

namespace EthInapproximability.CurrentPaper.SourcePrefixRawEntry

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourcePrefixRawFrame
open scoped Classical

theorem initial_stashes (q : Nat) (input saved count : List Bool) :
    (SourceCSPEntryWrapper.initial q input saved [] count).stk =
      Function.update
        (Function.update
          (SourceCSPEntryWrapper.initial q input [] [] []).stk
          (SourceCSPEntryWrapper.stash 0) saved)
        (SourceCSPEntryWrapper.stash 2) count := by
  funext k
  rw [SourceCSPEntryWrapper.initial_exact,
    SourceCSPEntryWrapper.initial_exact]
  cases k with
  | inl j =>
    have h0 : (Sum.inl j : SourceCSPEntryWrapper.Ambient q) ≠
        SourceCSPEntryWrapper.stash 0 := by
      simp [SourceCSPEntryWrapper.stash]
    have h2 : (Sum.inl j : SourceCSPEntryWrapper.Ambient q) ≠
        SourceCSPEntryWrapper.stash 2 := by
      simp [SourceCSPEntryWrapper.stash]
    simp only [Function.update_of_ne h0, Function.update_of_ne h2]
    by_cases h : ∃ x, SourceCSPEntryWrapper.firstEmbedding x =
        (Sum.inl j : SourceCSPEntryWrapper.Ambient q)
    · obtain ⟨x, hx⟩ := h
      rw [← hx, bank_at, bank_at]
    · rw [bank_outside _ _ _ _ h, bank_outside _ _ _ _ h]
      rfl
  | inr i =>
    have hout : ∀ (a c : List Bool) (j : Fin 4),
        bank SourceCSPEntryWrapper.firstEmbedding
          (SourceCSPEntryWrapper.foreign q a [] c)
          (SourceCSPFirstRowController.initial 2 q input).stk
          (.inr j) = SourceCSPEntryWrapper.foreign q a [] c (.inr j) := by
      intro a c j
      rw [bank_outside]
      · rintro ⟨x, hx⟩
        cases x with
        | inl g => cases hx
        | inr k => cases hx
    fin_cases i <;>
      simp [SourceCSPEntryWrapper.stash,
        SourceCSPEntryWrapper.foreign, hout]

end EthInapproximability.CurrentPaper.SourcePrefixRawEntry
