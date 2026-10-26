import Paper2.CodeCopiesMachine
import Paper2.CodeConstructorMachine
import EthInapproximability.CurrentPaper.BitMachineStackRun
import EthInapproximability.CurrentPaper.BitMachineRawSequence
import Mathlib.Tactic

/-! Paper A v12, Appendix D: physical construction of the columns-first
sample syntax. These framing lemmas preserve the whole surrounding bank;
they do not supply generated syntax as a machine instruction. -/

namespace Paper2.CodeSampleFrames

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSerialization

variable {K : Type} [DecidableEq K]

def copiesProgram (ι : Fin 5 ↪ K) :=
  fun l => BitMachineStackEmbedding.stackStmt ι (CodeCopiesMachine.program l)

theorem copies_run (ι : Fin 5 ↪ K) (S : K → List Bool)
    (m : Nat) (c : Code)
    (h0 : S (ι 0) = unary m) (h1 : S (ι 1) = encodeCode c)
    (h2 : S (ι 2) = []) (h3 : S (ι 3) = []) (h4 : S (ι 4) = []) :
    ((advance (copiesProgram ι))^[CodeCopiesMachine.clock m c])
      (⟨some CodeCopiesMachine.Label.initialize, none, S⟩ :
        TM2.Cfg (fun _ : K => Bool) _ _) =
      ⟨none, none, Function.update (Function.update S (ι 0) [])
        (ι 2) (encodeCode (copies m c))⟩ := by
  have hi : BitMachineStackEmbedding.bank ι S
      (CodeCopiesMachine.initial (unary m) (encodeCode c)).stk = S := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro i
    fin_cases i <;> simp [CodeCopiesMachine.initial, CodeCopiesMachine.cfg,
      CodeCopiesMachine.contents, h0, h1, h2, h3, h4]
  have hf : (CodeCopiesMachine.cfg none none [] (encodeCode c)
      (encodeCode (copies m c)) [] []).stk =
      Function.update (Function.update
        (CodeCopiesMachine.initial (unary m) (encodeCode c)).stk
        (0 : Fin 5) []) (2 : Fin 5) (encodeCode (copies m c)) := by
    funext i
    fin_cases i <;> rfl
  have h := BitMachineStackRun.run ι S CodeCopiesMachine.program
    (CodeCopiesMachine.initial (unary m) (encodeCode c))
    (CodeCopiesMachine.clock m c)
  rw [← CodeCopiesMachine.run, CodeCopiesMachine.run_copies] at h
  simpa only [copiesProgram, BitMachineStackEmbedding.stackCfg, hi, hf,
    BitMachineStackEmbedding.bank_update] using h

def appendProgram (ι : Fin 8 ↪ K) :=
  fun l => BitMachineStackEmbedding.stackStmt ι (CodeConstructorMachine.program l)

theorem append_run (ι : Fin 8 ↪ K) (S : K → List Bool)
    (left right : Code)
    (h0 : S (ι 0) = encodeCode left) (h1 : S (ι 1) = encodeCode right)
    (h6 : S (ι 6) = []) (h7 : S (ι 7) = []) :
    ((advance (appendProgram ι))^[CodeConstructorMachine.appendClock
        (encodeCode left) (encodeCode right)])
      (⟨some CodeConstructorMachine.Label.appendRightCopy, none, S⟩ :
        TM2.Cfg (fun _ : K => Bool) _ _) =
      ⟨none, none, Function.update S (ι 6) (encodeCode (.append left right))⟩ := by
  let words : Fin 6 → List Bool := fun j => S (ι ⟨j.val, by omega⟩)
  have hw0 : words 0 = encodeCode left := h0
  have hw1 : words 1 = encodeCode right := h1
  have hi : BitMachineStackEmbedding.bank ι S
      (CodeConstructorMachine.cfg (some .appendRightCopy) none words [] []).stk = S := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro i
    fin_cases i <;> simp [CodeConstructorMachine.cfg,
      CodeConstructorMachine.contents, words, h6, h7]
  have hf : (CodeConstructorMachine.cfg none none words
      ([false,true,true] ++ words 0 ++ words 1) []).stk =
      Function.update
        (CodeConstructorMachine.cfg (some .appendRightCopy) none words [] []).stk
        (6 : Fin 8) (encodeCode (.append left right)) := by
    funext i
    fin_cases i <;> simp [CodeConstructorMachine.cfg,
      CodeConstructorMachine.contents, encodeCode, hw0, hw1]
  have h := BitMachineStackRun.run ι S CodeConstructorMachine.program
    (CodeConstructorMachine.cfg (some .appendRightCopy) none words [] [])
    (CodeConstructorMachine.appendClock (words 0) (words 1))
  rw [← CodeConstructorMachine.run, CodeConstructorMachine.run_append_words] at h
  simp only [BitMachineStackEmbedding.stackCfg] at h
  rw [hi, hf, BitMachineStackEmbedding.bank_update, hi] at h
  simpa only [appendProgram, hw0, hw1] using h

#print axioms copies_run
#print axioms append_run

end Paper2.CodeSampleFrames
