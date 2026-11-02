import Paper2.CodeRowsArmA

/-! A fixed-word TM2 instruction expander. It is used only with the literal
branch header and the absolute constants 512, 510, 511. Its statement size is
large but independent of every runtime input. -/

namespace Paper2.CodeRowsLiteralPrefix

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorSerialization
open Paper2.CodeRowsArmA

inductive Label where
  | write | accept
  deriving DecidableEq, Fintype

def pushBits : List Bool → TM2.Stmt (fun _ : FinalBank => Bool) Label Unit →
    TM2.Stmt (fun _ : FinalBank => Bool) Label Unit
  | [], next => next
  | bit :: rest, next => push 29 (fun _ => bit) (pushBits rest next)

theorem stepAux_pushBits (bits : List Bool)
    (bank : FinalBank → List Bool) :
    TM2.stepAux (pushBits bits (goto (fun _ => Label.accept))) () bank =
      ⟨some .accept, (), Function.update bank 29
        (bits.reverse ++ bank 29)⟩ := by
  induction bits generalizing bank with
  | nil => simp [pushBits]
  | cons bit rest ih =>
      simp only [pushBits, TM2.stepAux]
      rw [ih]
      congr 1
      funext i
      by_cases hi : i = (29 : FinalBank)
      · subst i
        simp [Function.update, List.reverse_cons,
          List.append_assoc]
      · simp [Function.update, hi]

def branchPrefix : List Bool :=
  [true,false,false] ++ unary 512 ++ unary 510 ++ unary 511

def program : Label → TM2.Stmt (fun _ : FinalBank => Bool) Label Unit
  | .write => pushBits branchPrefix.reverse (goto (fun _ => .accept))
  | .accept => halt

theorem run (bank : FinalBank → List Bool) :
    ((advance program)^[2])
      (⟨some .write, (), bank⟩ :
        TM2.Cfg (fun _ : FinalBank => Bool) Label Unit) =
      ⟨none, (), Function.update bank 29
        (branchPrefix ++ bank 29)⟩ := by
  simp only [Function.iterate_succ_apply, Function.iterate_zero,
    id_eq, advance, TM2.step, program]
  rw [stepAux_pushBits]
  simp [branchPrefix]

end Paper2.CodeRowsLiteralPrefix
