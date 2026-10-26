import EthInapproximability.CurrentPaper.SourceClauseRowTruthCopy

/-!
# Preserved physical copy of one validated unary row query

The query word is the exact checker-certified coordinate `.inl (j,1)`.
This local copy leaves the entire row frame, including the truth table and
input suffix, unchanged and places a unary query vertex in a work stack.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseRowQueryCopy

open Turing BitMachineEncoding BitMachineStackEmbedding

abbrev Stack (q : ℕ) := SourceCSPRowQueryFrame.Stack q ⊕ Fin 2

def embedding {q : ℕ} (j : Fin q) : Fin 3 ↪ Stack q where
  toFun
    | 0 => .inl (.inl (j, 1))
    | 1 => .inr 0
    | _ => .inr 1
  inj' := by intro i k h; fin_cases i <;> fin_cases k <;> simp_all

def initial {q : ℕ} (row : SourceCSPRowQueryFrame.Stack q → List Bool) :
    Stack q → List Bool := Sum.elim row (fun _ => [])

noncomputable def finalBank {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (bits : List Bool) : Stack q → List Bool :=
  bank (embedding j) (initial row) (BitMachineCopy.cfg none none bits bits []).stk

def program {q : ℕ} (j : Fin q) (l : BitMachineCopy.Label) :=
  stackStmt (embedding j) (BitMachineCopy.program l)

theorem initial_bank {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (bits : List Bool) (h : row (.inl (j, 1)) = bits) :
    bank (embedding j) (initial row)
      (BitMachineCopy.cfg (some .scan) none bits [] []).stk = initial row := by
  apply bank_eq_self
  intro k
  fin_cases k
  · exact h.symm
  · rfl
  · rfl

theorem copy_run {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (bits : List Bool) (h : row (.inl (j, 1)) = bits) :
    ((advance (program j))^[2 * bits.length + 2])
      (⟨some BitMachineCopy.Label.scan, none, initial row⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, finalBank j row bits⟩ := by
  have hb := BitMachineCopy.run_correct none bits []
  simp only [List.append_nil] at hb
  have he := BitMachineStackRun.run (embedding j) (initial row)
    BitMachineCopy.program
    (BitMachineCopy.cfg (some .scan) none bits [] [])
    (2 * bits.length + 2)
  rw [show ((advance BitMachineCopy.program)^[2 * bits.length + 2])
    (BitMachineCopy.cfg (some .scan) none bits [] []) = _ from hb] at he
  simp only [stackCfg, initial_bank j row bits h] at he
  exact he

theorem row_preserved {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (bits : List Bool) (hbits : row (.inl (j, 1)) = bits)
    (k : SourceCSPRowQueryFrame.Stack q) :
    finalBank j row bits (.inl k) = row k := by
  by_cases h : k = .inl (j, 1)
  · subst k
    change finalBank j row bits ((embedding j) 0) = _
    rw [finalBank, bank_at]
    exact hbits.symm
  · rw [finalBank, bank_outside]
    · rfl
    · intro ⟨i, hi⟩
      fin_cases i <;> simp_all [embedding]

theorem copied_bits {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (bits : List Bool) :
    finalBank j row bits (.inr 0) = bits := by
  change finalBank j row bits ((embedding j) 1) = bits
  rw [finalBank, bank_at]
  rfl

theorem scratch_empty {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (bits : List Bool) :
    finalBank j row bits (.inr 1) = [] := by
  change finalBank j row bits ((embedding j) 2) = []
  rw [finalBank, bank_at]
  rfl

end EthInapproximability.CurrentPaper.SourceClauseRowQueryCopy
