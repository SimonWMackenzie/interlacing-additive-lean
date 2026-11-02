import CurrentAdditive.FieldSearchTailFreeBank

/-! The unselected shadow location for the printer modulus remains empty.
The live modulus location is the search counter on stack 0. -/

namespace CurrentAdditive.FieldSearchCompletion

open EthInapproximability.CurrentPaper
open CurrentAdditive.FiniteFieldMachine
open CurrentAdditive.FiniteFieldMachine.FieldSearchPrinterHandoff

def shadowFreeSharedBank (d n : Nat) (search : SearchStack → List Bool) :
    Stack → List Bool :=
  Sum.elim search (fun k => if k = printerModulus then [] else printerStartBank d 0 n k)

theorem shadowFree_search_bank_replace (d n : Nat)
    (before after : SearchStack → List Bool) :
    BitMachineStackEmbedding.bank searchSlots
      (shadowFreeSharedBank d n before) after =
      shadowFreeSharedBank d n after := by
  funext j
  rcases j with k | k
  · exact BitMachineStackEmbedding.bank_at searchSlots
      (shadowFreeSharedBank d n before) after k
  · rw [BitMachineStackEmbedding.bank_outside searchSlots
      (shadowFreeSharedBank d n before) after (.inr k)]
    · rfl
    · rintro ⟨i, hi⟩
      cases hi

theorem shadowFree_printer_bank_ready (d n tail : Nat)
    (htail : tail < 2 ^ d) (search : SearchStack → List Bool)
    (h0 : search 0 =
      CurrentAdditive.FieldMachineHelper.TrialCounterMachine.counterWord d tail) :
    (fun k => shadowFreeSharedBank d n search (printerSlots k)) =
      printerStartBank d tail n := by
  funext k
  by_cases hk : k = printerModulus
  · subst k
    change search 0 = printerStartBank d tail n printerModulus
    rw [h0, printerStart_modulus]
    exact CurrentAdditive.FieldMachineHelper.TrialTailPrinterBridge.counterWord_eq_printer_modulus
      d tail htail
  · simpa [shadowFreeSharedBank, printerSlots, printerSlot, hk] using
      (printerStart_nonmod_tail_free d n tail k hk).symm

theorem shadowFree_printer_bank_embedding (d n tail : Nat)
    (htail : tail < 2 ^ d) (search : SearchStack → List Bool)
    (h0 : search 0 =
      CurrentAdditive.FieldMachineHelper.TrialCounterMachine.counterWord d tail) :
    BitMachineStackEmbedding.bank printerSlots
      (shadowFreeSharedBank d n search) (printerStartBank d tail n) =
        shadowFreeSharedBank d n search := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro k
  exact congrFun (shadowFree_printer_bank_ready d n tail htail search h0).symm k

#print axioms shadowFree_search_bank_replace
#print axioms shadowFree_printer_bank_embedding

end CurrentAdditive.FieldSearchCompletion
