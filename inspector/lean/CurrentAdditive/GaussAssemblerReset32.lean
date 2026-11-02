import CurrentAdditive.GaussPivotPrepared32

/-!
Before Bank4 state assembly, clear the twelve Fin16 non-source banks that
earlier pivot-list workers may have touched. Sources 4--7 are preserved.
The reset is a fixed TM2 program and charges every discarded bit.
-/

namespace CurrentAdditive.GaussAssemblerReset32

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding

abbrev Stack := Fin 32
abbrev Label := Fin 13 ⊕ Unit
abbrev Control := Unit × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def bank : Fin 12 ↪ Stack where
  toFun j := ![0,1,2,3,8,9,10,11,12,13,14,15] j
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => if h : l.val < 12 then
      BitMachineClearBank.clearStep (bank ⟨l.val,h⟩) (.inl l)
        (.inl ⟨l.val+1, by omega⟩)
    else BitMachineClearBank.finishStep id (.inr ())
  | .inr () => .halt

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

def clock (S : Stack → List Bool) : Nat :=
  (∑ j : Fin 12, (S (bank j)).length) + 13

theorem physical_reset (S : Stack → List Bool) :
    run (clock S) ⟨some (.inl 0),((),none),S⟩ =
      ⟨some (.inr ()),((),none),BitMachineClearBank.cleared bank S⟩ := by
  have hsteps : ∀ j : Fin 12,
      program (.inl j.castSucc) =
        BitMachineClearBank.clearStep (bank j)
          (.inl j.castSucc) (.inl j.succ) := by
    intro j
    have hs : (⟨j.val+1, by omega⟩ : Fin 13) = j.succ := by
      apply Fin.ext
      rfl
    simp [program,bank,hs]
  have hfinish : program (.inl (Fin.last 12)) =
      BitMachineClearBank.finishStep id (.inr ()) := by
    simp [program]
  have h := BitMachineClearBank.clear_bank_run
    program id (.inr ()) 12 bank bank.injective Sum.inl
    hsteps hfinish () S
  simpa [run,clock] using h

theorem source_preserved (S : Stack → List Bool) (j : Fin 4) :
    (BitMachineClearBank.cleared bank S)
      (⟨j.val+4, by omega⟩ : Stack) =
      S (⟨j.val+4, by omega⟩ : Stack) := by
  apply BitMachineClearBank.cleared_foreign bank S _
  intro q hq
  fin_cases j <;> fin_cases q <;> simp_all [bank]

theorem cleared (S : Stack → List Bool) (j : Fin 12) :
    (BitMachineClearBank.cleared bank S) (bank j) = [] :=
  BitMachineClearBank.cleared_bank bank S j

#print axioms physical_reset
#print axioms source_preserved
#print axioms cleared

end CurrentAdditive.GaussAssemblerReset32
