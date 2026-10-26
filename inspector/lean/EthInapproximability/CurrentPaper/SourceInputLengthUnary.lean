import EthInapproximability.CurrentPaper.BitMachineCopy
import EthInapproximability.CurrentPaper.BitMachineRawSequence
import EthInapproximability.CurrentPaper.BitMachineStackRun

/-!
# A physical unary length budget preserving the original bit input

The input is first copied by the existing exact Boolean-stack copy program.
The copy is consumed one bit at a time while one unary cell is produced per
bit. The original input remains available for canonical header parsing.
-/

namespace EthInapproximability.CurrentPaper.SourceInputLengthUnary

open Turing BitMachineEncoding BitMachineStackEmbedding

inductive CountLabel where
  | scan
  deriving DecidableEq, Fintype

def countProgram : CountLabel →
    TM2.Stmt (fun _ : Fin 2 => Bool) CountLabel (Option Bool)
  | .scan => .pop 0 (fun _ b => b)
      (.branch Option.isSome
        (.push 1 (fun _ => true) (.goto (fun _ => .scan)))
        .halt)

def countContents (word unary : List Bool) : Fin 2 → List Bool := ![word, unary]

def countRun (t : Nat)
    (c : TM2.Cfg (fun _ : Fin 2 => Bool) CountLabel (Option Bool)) :=
  ((advance countProgram)^[t]) c

theorem count_run_succ (t : Nat)
    (c : TM2.Cfg (fun _ : Fin 2 => Bool) CountLabel (Option Bool)) :
    countRun (t + 1) c = countRun t (advance countProgram c) :=
  Function.iterate_succ_apply _ _ _

theorem count_step_cons (v : Option Bool) (b : Bool)
    (word unary : List Bool) :
    advance countProgram
      (⟨some .scan, v, countContents (b :: word) unary⟩ :
        TM2.Cfg (fun _ : Fin 2 => Bool) CountLabel (Option Bool)) =
      ⟨some .scan, some b, countContents word (true :: unary)⟩ := by
  simp [advance, TM2.step, countProgram, TM2.stepAux, countContents]
  funext k
  fin_cases k <;> simp

theorem count_step_nil (v : Option Bool) (unary : List Bool) :
    advance countProgram
      (⟨some .scan, v, countContents [] unary⟩ :
        TM2.Cfg (fun _ : Fin 2 => Bool) CountLabel (Option Bool)) =
      ⟨none, none, countContents [] unary⟩ := by
  simp [advance, TM2.step, countProgram, TM2.stepAux, countContents]

theorem count_run (word unary : List Bool) (v : Option Bool) :
    countRun (word.length + 1)
      (⟨some .scan, v, countContents word unary⟩ :
        TM2.Cfg (fun _ : Fin 2 => Bool) CountLabel (Option Bool)) =
      ⟨none, none, countContents []
        (List.replicate word.length true ++ unary)⟩ := by
  induction word generalizing v unary with
  | nil =>
      simpa only [List.length_nil, Nat.zero_add, List.replicate_zero,
        List.nil_append, countRun] using count_step_nil v unary
  | cons b word ih =>
      rw [List.length_cons, count_run_succ, count_step_cons]
      rw [ih]
      have hsucc : List.replicate (word.length + 1) true =
          true :: List.replicate word.length true := by
        rw [show word.length + 1 = 1 + word.length by omega,
          List.replicate_add]
        rfl
      have hcomm : List.replicate word.length true ++ [true] =
          true :: List.replicate word.length true := by
        rw [← List.replicate_one, ← List.replicate_add, hsucc]
      rw [hsucc]
      have heq : List.replicate word.length true ++ (true :: unary) =
          true :: (List.replicate word.length true ++ unary) := by
        calc
          List.replicate word.length true ++ (true :: unary) =
              (List.replicate word.length true ++ [true]) ++ unary := by
                simp only [List.singleton_append, List.append_assoc]
          _ = true :: (List.replicate word.length true ++ unary) := by
                rw [hcomm]
                rfl
      rw [heq]
      simp only [List.cons_append]

abbrev Stack := Fin 4
abbrev Label := BitMachineRawSequence.Label BitMachineCopy.Label CountLabel
abbrev Control := Option Bool × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def copyEmbedding : Fin 3 ↪ Stack where
  toFun k := ⟨k.val, by omega⟩
  inj' := by intro i j h; exact Fin.ext (Fin.mk.inj h)

def countEmbedding : Fin 2 ↪ Stack where
  toFun k := if k = 0 then 1 else 3
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

def contents (source work scratch unary : List Bool) : Stack → List Bool :=
  ![source, work, scratch, unary]

def copyProgram (l : BitMachineCopy.Label) :=
  stackStmt copyEmbedding (BitMachineCopy.program l)

def unaryProgram (l : CountLabel) :=
  stackStmt countEmbedding (countProgram l)

def program := BitMachineRawSequence.program copyProgram unaryProgram
  .scan (none : Option Bool) (none : Option Bool)

theorem copy_initial (word : List Bool) :
    bank copyEmbedding (contents word [] [] [])
      (BitMachineCopy.cfg (some .scan) none word [] []).stk =
      contents word [] [] [] := by
  apply bank_eq_self
  intro k
  fin_cases k <;> rfl

theorem copy_final (word : List Bool) :
    bank copyEmbedding (contents word [] [] [])
      (BitMachineCopy.cfg none none word word []).stk =
      contents word word [] [] := by
  funext k
  fin_cases k
  · change bank copyEmbedding _ _ (copyEmbedding 0) = _
    rw [bank_at]; rfl
  · change bank copyEmbedding _ _ (copyEmbedding 1) = _
    rw [bank_at]; rfl
  · change bank copyEmbedding _ _ (copyEmbedding 2) = _
    rw [bank_at]; rfl
  · rw [bank_outside]
    · rfl
    · intro ⟨j, hj⟩; fin_cases j <;> simp [copyEmbedding] at hj

theorem count_initial (word : List Bool) :
    bank countEmbedding (contents word word [] [])
      (⟨some .scan, none, countContents word []⟩ :
        TM2.Cfg (fun _ : Fin 2 => Bool) CountLabel (Option Bool)).stk =
      contents word word [] [] := by
  apply bank_eq_self
  intro k
  fin_cases k <;> rfl

theorem count_final (word : List Bool) :
    bank countEmbedding (contents word word [] [])
      (⟨none, none, countContents [] (List.replicate word.length true)⟩ :
        TM2.Cfg (fun _ : Fin 2 => Bool) CountLabel (Option Bool)).stk =
      contents word [] [] (List.replicate word.length true) := by
  funext k
  fin_cases k
  · rw [bank_outside]
    · rfl
    · intro ⟨j, hj⟩; fin_cases j <;> simp [countEmbedding] at hj
  · change bank countEmbedding _ _ (countEmbedding 0) = _
    rw [bank_at]; rfl
  · rw [bank_outside]
    · rfl
    · intro ⟨j, hj⟩; fin_cases j <;> simp [countEmbedding] at hj
  · change bank countEmbedding _ _ (countEmbedding 1) = _
    rw [bank_at]; rfl

theorem length_run (word : List Bool) :
    ∃ t ≤ 3 * word.length + 4,
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
          (none, none), contents word [] [] []⟩ : Config) =
        ⟨none, (none, none),
          contents word [] [] (List.replicate word.length true)⟩ := by
  have hc := BitMachineCopy.run_correct none word []
  have hc' := BitMachineStackRun.run copyEmbedding (contents word [] [] [])
    BitMachineCopy.program (BitMachineCopy.cfg (some .scan) none word [] [])
    (2 * word.length + 2)
  rw [show ((advance BitMachineCopy.program)^[2 * word.length + 2])
      (BitMachineCopy.cfg (some .scan) none word [] []) = _ from hc] at hc'
  simp only [stackCfg, copy_initial, copy_final, List.append_nil] at hc'
  have hl := count_run word [] none
  have hl' := BitMachineStackRun.run countEmbedding (contents word word [] [])
    countProgram
    (⟨some .scan, none, countContents word []⟩ :
      TM2.Cfg (fun _ : Fin 2 => Bool) CountLabel (Option Bool))
    (word.length + 1)
  rw [show ((advance countProgram)^[word.length + 1])
      (⟨some .scan, none, countContents word []⟩ :
        TM2.Cfg (fun _ : Fin 2 => Bool) CountLabel (Option Bool)) = _ from hl] at hl'
  simp only [stackCfg, List.append_nil] at hl'
  rw [count_initial, count_final] at hl'
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs copyProgram unaryProgram
    .scan .scan (none : Option Bool) none (none : Option Bool) none
    (contents word [] [] []) (contents word word [] [])
    (contents word [] [] (List.replicate word.length true))
    (2 * word.length + 2) (word.length + 1) hc' hl'
  exact ⟨t, by omega, hr⟩

end EthInapproximability.CurrentPaper.SourceInputLengthUnary
