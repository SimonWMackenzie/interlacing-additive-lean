import CurrentAdditive.FieldSearchPrinterHandoff

/-! The printer's foreign stacks can be initialized from public d,n alone.
Only the visible modulus slot depends on the selected tail, and that slot is
aliased to the search machine's physical candidate counter. -/

namespace CurrentAdditive.FieldSearchCompletion

open CurrentAdditive.FiniteFieldMachine
open CurrentAdditive.FiniteFieldMachine.FieldSearchPrinterHandoff

theorem printerStart_nonmod_tail_free (d n tail : Nat)
    (k : PrinterStack) (hk : k ≠ printerModulus) :
    printerStartBank d tail n k = printerStartBank d 0 n k := by
  fin_cases k <;> first | exact (hk rfl).elim | rfl

def tailFreeSharedBank (d n : Nat) (search : SearchStack → List Bool) :
    Stack → List Bool :=
  Sum.elim search (printerStartBank d 0 n)

theorem tailFree_printer_bank_ready (d n tail : Nat)
    (htail : tail < 2 ^ d) (search : SearchStack → List Bool)
    (h0 : search 0 =
      CurrentAdditive.FieldMachineHelper.TrialCounterMachine.counterWord d tail) :
    (fun k => tailFreeSharedBank d n search (printerSlots k)) =
      printerStartBank d tail n := by
  funext k
  by_cases hk : k = printerModulus
  · subst k
    change search 0 = printerStartBank d tail n printerModulus
    rw [h0, printerStart_modulus]
    exact CurrentAdditive.FieldMachineHelper.TrialTailPrinterBridge.counterWord_eq_printer_modulus
      d tail htail
  · simpa [tailFreeSharedBank, printerSlots, printerSlot, hk] using
      (printerStart_nonmod_tail_free d n tail k hk).symm

theorem tailFree_printer_bank_embedding (d n tail : Nat)
    (htail : tail < 2 ^ d) (search : SearchStack → List Bool)
    (h0 : search 0 =
      CurrentAdditive.FieldMachineHelper.TrialCounterMachine.counterWord d tail) :
    EthInapproximability.CurrentPaper.BitMachineStackEmbedding.bank printerSlots
      (tailFreeSharedBank d n search) (printerStartBank d tail n) =
        tailFreeSharedBank d n search := by
  apply EthInapproximability.CurrentPaper.BitMachineStackEmbedding.bank_eq_self
  intro k
  exact congrFun (tailFree_printer_bank_ready d n tail htail search h0).symm k

#print axioms printerStart_nonmod_tail_free
#print axioms tailFree_printer_bank_ready
#print axioms tailFree_printer_bank_embedding

end CurrentAdditive.FieldSearchCompletion
