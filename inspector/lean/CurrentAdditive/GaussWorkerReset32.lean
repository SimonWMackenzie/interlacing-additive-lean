import CurrentAdditive.GaussPivotHeader32
import EthInapproximability.CurrentPaper.BitMachineClearBank

/-!
The two physical length writers share ambient banks 8--15. This fixed TM2
reset discards every bit in those eight banks and leaves all other Gauss
state/context banks untouched; its clock charges the removed bits.
-/

namespace CurrentAdditive.GaussWorkerReset32

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding

abbrev Stack := Fin 32
abbrev Label := Fin 9 ⊕ Unit
abbrev Control := Unit × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def bank : Fin 8 ↪ Stack where
  toFun j := ⟨j.val+8, by omega⟩
  inj' := by
    intro a b h
    have hv := congrArg Fin.val h
    change a.val+8 = b.val+8 at hv
    exact Fin.ext (by omega)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => if h : l.val < 8 then
      BitMachineClearBank.clearStep (bank ⟨l.val,h⟩) (.inl l)
        (.inl ⟨l.val+1, by omega⟩)
    else BitMachineClearBank.finishStep id (.inr ())
  | .inr () => .halt

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

def clock (S : Stack → List Bool) : Nat :=
  (∑ j : Fin 8, (S (bank j)).length) + 9

theorem physical_reset (S : Stack → List Bool) :
    run (clock S) ⟨some (.inl 0), ((),none),S⟩ =
      ⟨some (.inr ()), ((),none),
        BitMachineClearBank.cleared bank S⟩ := by
  have hsteps : ∀ j : Fin 8,
      program (.inl j.castSucc) =
        BitMachineClearBank.clearStep (bank j)
          (.inl j.castSucc) (.inl j.succ) := by
    intro j
    have hs : (⟨j.val+1, by omega⟩ : Fin 9) = j.succ := by
      apply Fin.ext
      rfl
    simp [program, bank, hs]
  have hfinish : program (.inl (Fin.last 8)) =
      BitMachineClearBank.finishStep id (.inr ()) := by
    simp [program]
  have h := BitMachineClearBank.clear_bank_run
    program id (.inr ()) 8 bank bank.injective Sum.inl
    hsteps hfinish () S
  simpa [run, clock] using h

theorem reset_empty (S : Stack → List Bool) (j : Fin 8) :
    (BitMachineClearBank.cleared bank S) (bank j) = [] :=
  BitMachineClearBank.cleared_bank bank S j

theorem reset_preserves (S : Stack → List Bool) (k : Stack)
    (hk : k.val < 8 ∨ 16 ≤ k.val) :
    (BitMachineClearBank.cleared bank S) k = S k := by
  apply BitMachineClearBank.cleared_foreign bank S k
  intro j hj
  have hv := congrArg Fin.val hj
  have hlt := j.isLt
  change j.val+8 = k.val at hv
  omega

#print axioms physical_reset
#print axioms reset_empty
#print axioms reset_preserves

end CurrentAdditive.GaussWorkerReset32
