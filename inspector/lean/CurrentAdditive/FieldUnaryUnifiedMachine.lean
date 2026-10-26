import CurrentAdditive.FieldUnaryBankPrepRun
import CurrentAdditive.FieldSearchShadowFreeCompletion
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-! One fixed finite TM2 program: unary bank preparation, then the actual
first-passing field search, then the packed field-list printer. -/

namespace CurrentAdditive.FieldSearchCompletion.FieldUnaryUnifiedMachine

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.FiniteFieldMachine.FieldSearchPrinterHandoff

namespace Prep
export CurrentAdditive.FieldSearchCompletion.FieldUnaryBankPrep
  (Stack Label Control program initial prepared run_prepare)
end Prep
namespace Field
open CurrentAdditive.FiniteFieldMachine.UnifiedFieldListMachine
end Field

abbrev Stack := Fin 5 ⊕ CurrentAdditive.FiniteFieldMachine.FieldSearchPrinterHandoff.Stack

def prepSlot (i : Prep.Stack) : Stack :=
  ![(.inl 0), (.inl 1), (.inl 2), (.inl 3),
    (.inr (searchSlots 0)), (.inr (searchSlots 1)),
    (.inr (searchSlots 2)), (.inr (searchSlots 8)),
    (.inr (printerSlots (.inl (.inl CurrentAdditive.FiniteFieldMachine.SeedCallbackMachine.source)))),
    (.inr (printerSlots (.inl (.inl CurrentAdditive.FiniteFieldMachine.SeedCallbackMachine.lengthSource)))),
    (.inl 4)] i

theorem prepSlot_injective : Function.Injective prepSlot := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    simp_all [prepSlot, searchSlots, printerSlots, printerSlot, printerModulus,
      CurrentAdditive.FiniteFieldMachine.SeedCallbackMachine.source,
      CurrentAdditive.FiniteFieldMachine.SeedCallbackMachine.lengthSource,
      CurrentAdditive.FiniteFieldMachine.SeedCallbackMachine.modulus,
      CurrentAdditive.FiniteFieldMachine.SeedCallbackMachine.inner]

def prepSlots : Prep.Stack ↪ Stack where
  toFun := prepSlot
  inj' := prepSlot_injective

def fieldSlots : CurrentAdditive.FiniteFieldMachine.FieldSearchPrinterHandoff.Stack ↪ Stack where
  toFun := Sum.inr
  inj' := by intro a b h; exact Sum.inr.inj h

inductive Label where
  | prep (l : Prep.Label)
  | field (l : CurrentAdditive.FiniteFieldMachine.UnifiedFieldListMachine.Label)
  deriving Fintype

abbrev Control := Prep.Control × CurrentAdditive.FiniteFieldMachine.UnifiedFieldListMachine.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def fieldInitialControl : CurrentAdditive.FiniteFieldMachine.UnifiedFieldListMachine.Control :=
  CurrentAdditive.FiniteFieldMachine.UnifiedFieldListMachine.searchEmbed initialRegisters

def prepEmbed (s : Prep.Control) : Control := (s, fieldInitialControl)
def fieldEmbed (s : CurrentAdditive.FiniteFieldMachine.UnifiedFieldListMachine.Control) :
    Control := (none, s)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .prep l => BitMachineStackEmbedding.stmt prepSlots Label.prep prepEmbed
      Prod.fst (some (.field (.search (.outer .initial))))
      (Prep.program l)
  | .field l => BitMachineStackEmbedding.stmt fieldSlots Label.field fieldEmbed
      Prod.snd none
      (CurrentAdditive.FiniteFieldMachine.UnifiedFieldListMachine.program l)

def stackDecEq : DecidableEq Stack :=
  @instDecidableEqSum (Fin 5)
    CurrentAdditive.FiniteFieldMachine.FieldSearchPrinterHandoff.Stack
    (inferInstanceAs (DecidableEq (Fin 5)))
    (@instDecidableEqSum SearchStack PrinterStack
      (inferInstanceAs (DecidableEq SearchStack))
      CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.stackDecEq)

def run (t : Nat) (q : Config) : Config :=
  ((@advance Stack Label Control stackDecEq program)^[t]) q

theorem run_eq_any (D : DecidableEq Stack) (t : Nat) (q : Config) :
    run t q = ((@advance Stack Label Control D program)^[t]) q := by
  have h : stackDecEq = D := Subsingleton.elim _ _
  unfold run
  rw [h]

theorem run_add (t u : Nat) (q : Config) :
    run (t + u) q = run u (run t q) := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply]

end CurrentAdditive.FieldSearchCompletion.FieldUnaryUnifiedMachine
