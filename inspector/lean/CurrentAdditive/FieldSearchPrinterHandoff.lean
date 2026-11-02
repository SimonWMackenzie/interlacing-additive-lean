import CurrentAdditive.FieldListOutputMachine
import CurrentAdditive.TrialTailPrinterBridge
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-! The successful trial search's candidate-counter stack is physically
shared with the field printer's lower-modulus bank. This register alias needs
no reversal, copy, or uncharged data transformation. The global search run
and whole-program phase composition are separate theorems. -/

namespace CurrentAdditive.FiniteFieldMachine.FieldSearchPrinterHandoff

open EthInapproximability.CurrentPaper
open CurrentAdditive.FiniteFieldMachine

abbrev SearchStack := Fin 12
abbrev PrinterStack := FieldListOutputMachine.Stack
abbrev Stack := SearchStack ⊕ PrinterStack

def printerModulus : PrinterStack := .inl (.inl SeedCallbackMachine.modulus)

def searchSlots : SearchStack ↪ Stack where
  toFun := Sum.inl
  inj' := by intro a b h; exact Sum.inl.inj h

def printerSlot (k : PrinterStack) : Stack :=
  if k = printerModulus then .inl 0 else .inr k

theorem printerSlot_injective : Function.Injective printerSlot := by
  intro a b h
  by_cases ha : a = printerModulus
  · by_cases hb : b = printerModulus
    · exact ha.trans hb.symm
    · simp [printerSlot, ha, hb] at h
  · by_cases hb : b = printerModulus
    · simp [printerSlot, ha, hb] at h
    · simpa [printerSlot, ha, hb] using h

def printerSlots : PrinterStack ↪ Stack where
  toFun := printerSlot
  inj' := printerSlot_injective

def printerStartBank (d tail n : Nat) : PrinterStack → List Bool :=
  (FieldListOutputMachine.cfg none FieldListOutputMachine.initial
    (FieldListOutputMachine.mapStart d tail n).stk []).stk

theorem printerStart_modulus (d tail n : Nat) :
    printerStartBank d tail n printerModulus =
      SamplerMachine.encodeWord
        (HornerNatBridge.lowerWord d
          (CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d tail)) := by
  rfl

def sharedBank (d tail n : Nat) (search : SearchStack → List Bool) :
    Stack → List Bool :=
  Sum.elim search (printerStartBank d tail n)

theorem search_bank (d tail n : Nat) (search : SearchStack → List Bool)
    (k : SearchStack) :
    sharedBank d tail n search (searchSlots k) = search k := by rfl

theorem search_bank_embedding (d tail n : Nat)
    (search : SearchStack → List Bool) :
    BitMachineStackEmbedding.bank searchSlots
      (sharedBank d tail n search) search = sharedBank d tail n search := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro k
  exact (search_bank d tail n search k).symm

theorem search_bank_replace (d tail n : Nat)
    (old current : SearchStack → List Bool) :
    BitMachineStackEmbedding.bank searchSlots
      (sharedBank d tail n old) current = sharedBank d tail n current := by
  funext k
  rcases k with k | k
  · exact BitMachineStackEmbedding.bank_at searchSlots
      (sharedBank d tail n old) current k
  · have hout : ¬ ∃ i : SearchStack, searchSlots i = (.inr k : Stack) := by
      rintro ⟨i, h⟩
      cases h
    rw [BitMachineStackEmbedding.bank_outside searchSlots
      (sharedBank d tail n old) current (.inr k) hout]
    rfl

/-- Once the search succeeds with its checked candidate word on stack 0,
every printer stack reads exactly the input bank used by the checked packed
list run. The modulus bank is an alias of search stack 0; all other printer
stacks were initialized independently and remain foreign to the search. -/
theorem printer_bank_ready (d tail n : Nat) (htail : tail < 2 ^ d)
    (search : SearchStack → List Bool)
    (h0 : search 0 =
      CurrentAdditive.FieldMachineHelper.TrialCounterMachine.counterWord d tail) :
    (fun k => sharedBank d tail n search (printerSlots k)) =
      printerStartBank d tail n := by
  funext k
  by_cases hk : k = printerModulus
  · subst k
    change search 0 = printerStartBank d tail n printerModulus
    rw [h0, printerStart_modulus]
    exact CurrentAdditive.FieldMachineHelper.TrialTailPrinterBridge.counterWord_eq_printer_modulus
      d tail htail
  · change sharedBank d tail n search (printerSlot k) = _
    simp only [printerSlot, if_neg hk, sharedBank, Sum.elim_inr]

theorem printer_bank_embedding (d tail n : Nat) (htail : tail < 2 ^ d)
    (search : SearchStack → List Bool)
    (h0 : search 0 =
      CurrentAdditive.FieldMachineHelper.TrialCounterMachine.counterWord d tail) :
    BitMachineStackEmbedding.bank printerSlots
      (sharedBank d tail n search) (printerStartBank d tail n) =
        sharedBank d tail n search := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro k
  exact congrFun (printer_bank_ready d tail n htail search h0).symm k

end CurrentAdditive.FiniteFieldMachine.FieldSearchPrinterHandoff
