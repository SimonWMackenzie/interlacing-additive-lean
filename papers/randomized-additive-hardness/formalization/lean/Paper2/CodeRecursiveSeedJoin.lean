import Paper2.CodeRecursiveSeedRow
import EthInapproximability.CurrentPaper.BitMachineClearBank

/-! Fixed seed preparation through the literal next-round bank. -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

namespace Paper2.CodeRecursiveSeedJoin

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.CodeRecursiveLoop Paper2.CodeRecursiveSeedPrep
open Paper2.CodeRecursiveSeedRow

inductive ClearLabel where
  | clear | done
  deriving DecidableEq, Fintype

def clearProgram : ClearLabel →
    TM2.Stmt (fun _ : Stack => Bool) ClearLabel (Unit × Option Bool)
  | .clear => BitMachineClearBank.clearStep 63 .clear .done
  | .done => halt

theorem clear_run (S : Stack → List Bool) :
    ((advance clearProgram)^[(S 63).length+2])
      (⟨some .clear, ((),none), S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) ClearLabel (Unit × Option Bool)) =
      ⟨none, ((),none), Function.update S 63 []⟩ := by
  have h := BitMachineClearBank.clear_one_run
    clearProgram 63 .clear .done rfl () S
  rw [show (S 63).length+2 = 1+((S 63).length+1) by omega,
    Function.iterate_add_apply, h]
  rfl

def seedClean (n s q₁ q₂ w Q p : Nat) (fuel : List Bool) :
    Stack → List Bool :=
  Function.update
    (CodeRecursiveSeedRow.afterRow n s q₁ q₂ w Q p fuel)
    63 []

theorem after_row_raw_p (n s q₁ q₂ w Q p : Nat) (fuel : List Bool) :
    CodeRecursiveSeedRow.afterRow n s q₁ q₂ w Q p fuel 63 =
      List.replicate p true := by
  simp [CodeRecursiveSeedRow.afterRow, afterCountCopy,
    afterTicket, publicBase]

theorem clear_seed_run (n s q₁ q₂ w Q p : Nat) (fuel : List Bool) :
    ((advance clearProgram)^[p+2])
      (⟨some .clear, ((),none),
        CodeRecursiveSeedRow.afterRow n s q₁ q₂ w Q p fuel⟩ :
        TM2.Cfg (fun _ : Stack => Bool) ClearLabel (Unit × Option Bool)) =
      ⟨none, ((),none), seedClean n s q₁ q₂ w Q p fuel⟩ := by
  simpa only [seedClean, after_row_raw_p, List.length_replicate]
    using clear_run
      (CodeRecursiveSeedRow.afterRow n s q₁ q₂ w Q p fuel)

abbrev PrepControl := CodeAtomCountInput.Control × Option Bool
abbrev PrepLabel := BitMachineRawSequence.Label
  CodeAtomCountInput.Label BitMachineCopy.Label

def p₁ := BitMachineRawSequence.program
  CodeRecursiveSeedPrep.program CodeRecursiveSeedRow.program
  CodeRecursiveSeedRow.Label.init ((((),none),()),none) none

def b₁ (p : Nat) := ((2*p+8)+(2*p+2)+1)+(p+2)+1

theorem p₁_run (n s q₁ q₂ w Q p : Nat) (fuel : List Bool) :
    ∃ t ≤ b₁ p,
      ((advance p₁)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                CodeAtomCountInput.InitLabel.write)))),
          (((((),none),()),none),none),
          publicBase n s q₁ q₂ w Q p fuel⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, (((((),none),()),none),none),
          CodeRecursiveSeedRow.afterRow n s q₁ q₂ w Q p fuel⟩ := by
  obtain ⟨ta,hta,ha⟩ := CodeRecursiveSeedPrep.run_exact
    n s q₁ q₂ w Q p fuel
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    CodeRecursiveSeedPrep.program CodeRecursiveSeedRow.program
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          CodeAtomCountInput.InitLabel.write))) .init
    ((((),none),()),none) ((((),none),()),none) none none
    (publicBase n s q₁ q₂ w Q p fuel)
    (afterCountCopy n s q₁ q₂ w Q p fuel)
    (CodeRecursiveSeedRow.afterRow n s q₁ q₂ w Q p fuel)
    ta (p+2) ha (CodeRecursiveSeedRow.run_exact n s q₁ q₂ w Q p fuel)
  exact ⟨t, by dsimp [b₁]; omega, hr⟩

def program := BitMachineRawSequence.program p₁ clearProgram
  ClearLabel.clear ((((((),none),()),none),none)) ((),none)

def clock (p : Nat) := b₁ p + (p+2)+1

theorem run_exact (n s q₁ q₂ w Q p : Nat) (fuel : List Bool) :
    ∃ t ≤ clock p,
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel
                  CodeAtomCountInput.InitLabel.write))))),
          ((((((),none),()),none),none),((),none)),
          publicBase n s q₁ q₂ w Q p fuel⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, ((((((),none),()),none),none),((),none)),
          seedClean n s q₁ q₂ w Q p fuel⟩ := by
  obtain ⟨ta,hta,ha⟩ := p₁_run n s q₁ q₂ w Q p fuel
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    p₁ clearProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            CodeAtomCountInput.InitLabel.write)))) .clear
    (((((),none),()),none),none) (((((),none),()),none),none)
    ((),none) ((),none)
    (publicBase n s q₁ q₂ w Q p fuel)
    (CodeRecursiveSeedRow.afterRow n s q₁ q₂ w Q p fuel)
    (seedClean n s q₁ q₂ w Q p fuel)
    ta (p+2) ha (clear_seed_run n s q₁ q₂ w Q p fuel)
  exact ⟨t, by dsimp [clock]; omega, hr⟩

#print axioms run_exact

end Paper2.CodeRecursiveSeedJoin
