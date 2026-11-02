import EthInapproximability.CurrentPaper.SourceCSPRowQueryUnary
import EthInapproximability.CurrentPaper.BitMachineCopy
import EthInapproximability.CurrentPaper.BitMachineStackRun

/-!
# Preserved physical copy of one validated row truth table

The source is the parser/checker's actual `.inr 2` table stack. The two work
stacks are disjoint from the row frame, so the row-loop suffix, query words,
cap, status, and table are all preserved. The copy is charged literally.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseRowTruthCopy

open Turing BitMachineEncoding BitMachineStackEmbedding

abbrev Stack (q : ℕ) := SourceCSPRowQueryFrame.Stack q ⊕ Fin 2

def embedding {q : ℕ} : Fin 3 ↪ Stack q where
  toFun
    | 0 => .inl (.inr 2)
    | 1 => .inr 0
    | _ => .inr 1
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

def initial {q : ℕ} (row : SourceCSPRowQueryFrame.Stack q → List Bool) :
    Stack q → List Bool :=
  Sum.elim row (fun _ => [])

noncomputable def finalBank {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (bits : List Bool) : Stack q → List Bool :=
  bank embedding (initial row) (BitMachineCopy.cfg none none bits bits []).stk

def program {q : ℕ} (l : BitMachineCopy.Label) :=
  stackStmt (embedding (q := q)) (BitMachineCopy.program l)

theorem initial_bank {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (bits : List Bool) (h : row (.inr 2) = bits) :
    bank embedding (initial row)
      (BitMachineCopy.cfg (some .scan) none bits [] []).stk = initial row := by
  apply bank_eq_self
  intro k
  fin_cases k
  · exact h.symm
  · rfl
  · rfl

theorem copy_run {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (bits : List Bool) (h : row (.inr 2) = bits) :
    ((advance program)^[2 * bits.length + 2])
      (⟨some BitMachineCopy.Label.scan, none, initial row⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, finalBank row bits⟩ := by
  have hb := BitMachineCopy.run_correct none bits []
  simp only [List.append_nil] at hb
  have he := BitMachineStackRun.run embedding (initial row)
    BitMachineCopy.program
    (BitMachineCopy.cfg (some .scan) none bits [] [])
    (2 * bits.length + 2)
  rw [show ((advance BitMachineCopy.program)^[2 * bits.length + 2])
    (BitMachineCopy.cfg (some .scan) none bits [] []) = _ from hb] at he
  simp only [stackCfg, initial_bank row bits h, finalBank] at he
  exact he

theorem row_preserved {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (bits : List Bool) (hbits : row (.inr 2) = bits)
    (k : SourceCSPRowQueryFrame.Stack q) :
    finalBank row bits (.inl k) = row k := by
  by_cases h : k = .inr 2
  · subst k
    change finalBank row bits (embedding 0) = _
    rw [finalBank, bank_at]
    exact hbits.symm
  · rw [finalBank, bank_outside]
    · rfl
    · intro ⟨i, hi⟩
      fin_cases i <;> simp_all [embedding]

theorem copied_bits {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (bits : List Bool) :
    finalBank row bits (.inr 0) = bits := by
  change finalBank row bits (embedding 1) = bits
  rw [finalBank, bank_at]
  rfl

theorem scratch_empty {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (bits : List Bool) :
    finalBank row bits (.inr 1) = [] := by
  change finalBank row bits (embedding 2) = []
  rw [finalBank, bank_at]
  rfl

end EthInapproximability.CurrentPaper.SourceClauseRowTruthCopy
