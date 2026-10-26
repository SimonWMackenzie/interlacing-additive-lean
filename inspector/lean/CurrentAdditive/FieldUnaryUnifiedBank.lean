import CurrentAdditive.FieldUnaryUnifiedMachine

/-! The physical initializer's final ambient bank agrees with the field
search/printer's shadow-free starting bank. -/

namespace CurrentAdditive.FieldSearchCompletion.FieldUnaryUnifiedMachine

open EthInapproximability.CurrentPaper
open CurrentAdditive.FiniteFieldMachine
open CurrentAdditive.FiniteFieldMachine.FieldSearchPrinterHandoff

set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

def initialStack (d n : Nat) : Stack → List Bool :=
  Sum.elim
    (fun i : Fin 5 => if i = 0 then List.replicate d true
      else if i = 1 then List.replicate n true else [])
    (fun _ => [])

def initialConfig (d n : Nat) : Config :=
  ⟨some (.prep .scanD), prepEmbed none, initialStack d n⟩

def pairSource : PrinterStack := .inl (.inl SeedCallbackMachine.source)
def lengthSource : PrinterStack := .inl (.inl SeedCallbackMachine.lengthSource)

def visibleBank (d n : Nat) :
    CurrentAdditive.FiniteFieldMachine.FieldSearchPrinterHandoff.Stack → List Bool :=
  Sum.elim
    (fun i : SearchStack =>
      if i = 0 then List.replicate d false
      else if i = 1 then [false]
      else if i = 2 then List.replicate (d-1) true
      else if i = 8 then List.replicate (d/2) true
      else [])
    (fun k : PrinterStack =>
      if k = pairSource then List.replicate (2*d) false
      else if k = lengthSource then List.replicate n true
      else [])

def preparedStack (d n : Nat) : Stack → List Bool :=
  Sum.elim
    (fun i : Fin 5 => if i = 0 then List.replicate d true
      else if i = 1 then List.replicate n true else [])
    (visibleBank d n)

theorem prep_initial_projection (d n : Nat) (i : Prep.Stack) :
    (Prep.initial d n).stk i = initialStack d n (prepSlots i) := by
  fin_cases i <;>
    simp [Prep.initial, CurrentAdditive.FieldSearchCompletion.FieldUnaryBankPrep.cfg,
      CurrentAdditive.FieldSearchCompletion.FieldUnaryBankPrep.bank,
      initialStack, prepSlots, prepSlot, searchSlots, printerSlots, printerSlot,
      printerModulus, SeedCallbackMachine.source, SeedCallbackMachine.lengthSource,
      SeedCallbackMachine.modulus, SeedCallbackMachine.inner]

theorem initial_eq_frame (d n : Nat) :
    initialConfig d n =
      BitMachineStackEmbedding.cfg prepSlots (initialStack d n)
        Label.prep prepEmbed (some (.field (.search (.outer .initial))))
        (Prep.initial d n) := by
  have hb : BitMachineStackEmbedding.bank prepSlots (initialStack d n)
      (Prep.initial d n).stk = initialStack d n := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro i
    exact prep_initial_projection d n i
  change (⟨some (.prep .scanD), prepEmbed none, initialStack d n⟩ : Config) =
    ⟨some (.prep .scanD), prepEmbed none,
      BitMachineStackEmbedding.bank prepSlots (initialStack d n)
        (Prep.initial d n).stk⟩
  exact congrArg (fun S : Stack → List Bool =>
    (⟨some (.prep .scanD), prepEmbed none, S⟩ : Config)) hb.symm

theorem prep_prepared_projection (d n : Nat) (i : Prep.Stack) :
    (Prep.prepared d n).stk i = preparedStack d n (prepSlots i) := by
  fin_cases i <;>
    simp [Prep.prepared, CurrentAdditive.FieldSearchCompletion.FieldUnaryBankPrep.cfg,
      CurrentAdditive.FieldSearchCompletion.FieldUnaryBankPrep.bank,
      preparedStack, visibleBank, prepSlots, prepSlot, searchSlots,
      printerSlots, printerSlot, pairSource, lengthSource, printerModulus,
      SeedCallbackMachine.source, SeedCallbackMachine.lengthSource,
      SeedCallbackMachine.modulus, SeedCallbackMachine.inner]

theorem prepared_eq_frame (d n : Nat) :
    BitMachineStackEmbedding.bank prepSlots (initialStack d n)
      (Prep.prepared d n).stk = preparedStack d n := by
  funext j
  by_cases h : ∃ i, prepSlots i = j
  · obtain ⟨i, rfl⟩ := h
    rw [BitMachineStackEmbedding.bank_at]
    exact prep_prepared_projection d n i
  · rw [BitMachineStackEmbedding.bank_outside prepSlots _ _ j h]
    rcases j with i | k
    · fin_cases i <;> rfl
    · rcases k with i | k
      · fin_cases i <;> first
          | rfl
          | exact False.elim (h (by decide))
      · fin_cases k <;>
          simp_all [initialStack, preparedStack, visibleBank, pairSource,
            lengthSource, prepSlots, prepSlot, printerSlots, printerSlot,
            printerModulus, SeedCallbackMachine.source,
            SeedCallbackMachine.lengthSource, SeedCallbackMachine.modulus,
            SeedCallbackMachine.inner]
        all_goals
          have h8 := h 8
          have h9 := h 9
          simp at h8 h9

theorem visible_eq_shadowFree (d n : Nat) :
    visibleBank d n = shadowFreeSharedBank d n
      (CurrentAdditive.FieldSearchCompletion.initialBank d) := by
  funext k
  rcases k with i | k
  · fin_cases i <;>
      simp [visibleBank, shadowFreeSharedBank,
        CurrentAdditive.FieldSearchCompletion.initialBank,
        CurrentAdditive.FieldMachineHelper.TrialSearchControllerMachine.bank,
        CurrentAdditive.FieldMachineHelper.TrialCounterMachine.counterWord]
  · fin_cases k <;> rfl

end CurrentAdditive.FieldSearchCompletion.FieldUnaryUnifiedMachine
