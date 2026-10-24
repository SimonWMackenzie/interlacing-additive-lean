import EthInapproximability.CurrentPaper.SourceClauseRowUnitMachine
import EthInapproximability.CurrentPaper.SourceCSPRowQueryFrame

/-!
# Unit-clause writer framed beneath a validated source row

The row bank is disjoint from the new address and writer banks. The same
finite unit-clause program can therefore run without changing any parsed
query, table, source suffix, or status stack. Supplying these unary operands
from a row-loop callback is a later caller's responsibility.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseRowUnitFrame

open Turing BitMachineEncoding BitMachineStackEmbedding

abbrev Stack (q : Nat) :=
  SourceCSPRowQueryFrame.Stack q ⊕ SourceClauseRowUnitMachine.Stack

def embedding (q : Nat) : SourceClauseRowUnitMachine.Stack ↪ Stack q :=
  Function.Embedding.inr

noncomputable def initial {q : Nat}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k w ell : Nat) (saved output count : List Bool) :
    Stack q → List Bool :=
  Sum.elim row (SourceClauseRowUnitMachine.initial n r a q k w ell
    saved output count)

noncomputable def finalBank {q : Nat}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k w ell : Nat) (sign : Bool)
    (saved output count : List Bool) : Stack q → List Bool :=
  Sum.elim row (SourceClauseRowUnitMachine.finalBank n r a q k w ell sign
    saved output count)

noncomputable def program (q : Nat) (sign : Bool)
    (l : SourceClauseRowUnitMachine.Label) :=
  stackStmt (embedding q) (SourceClauseRowUnitMachine.program sign l)

theorem run {q : Nat}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k w ell : Nat) (sign : Bool)
    (saved output count : List Bool) :
    ∃ t ≤ SourceClauseRowUnitMachine.cost n r a q k w ell,
      ((advance (program q sign))^[t])
        (⟨some SourceClauseRowUnitMachine.startLabel,
          SourceClauseRowUnitMachine.startControl,
          initial row n r a k w ell saved output count⟩ :
          TM2.Cfg (fun _ : Stack q => Bool)
            SourceClauseRowUnitMachine.Label
            SourceClauseRowUnitMachine.Control) =
        ⟨none, SourceClauseRowUnitMachine.startControl,
          finalBank row n r a k w ell sign saved output count⟩ := by
  obtain ⟨t, ht, hr⟩ := SourceClauseRowUnitMachine.run n r a q k w ell sign
    saved output count
  let c : TM2.Cfg (fun _ : SourceClauseRowUnitMachine.Stack => Bool)
      SourceClauseRowUnitMachine.Label SourceClauseRowUnitMachine.Control :=
    ⟨some SourceClauseRowUnitMachine.startLabel,
      SourceClauseRowUnitMachine.startControl,
      SourceClauseRowUnitMachine.initial n r a q k w ell
        saved output count⟩
  have he := BitMachineStackRun.run (embedding q)
    (initial row n r a k w ell saved output count)
    (SourceClauseRowUnitMachine.program sign) c t
  have hstart : bank (embedding q)
      (initial row n r a k w ell saved output count) c.stk =
      initial row n r a k w ell saved output count := by
    apply bank_eq_self
    intro i
    rfl
  have hend : bank (embedding q)
      (initial row n r a k w ell saved output count)
      (SourceClauseRowUnitMachine.finalBank n r a q k w ell sign
        saved output count) =
      finalBank row n r a k w ell sign saved output count := by
    funext i
    cases i with
    | inl j =>
        rw [bank_outside]
        · rfl
        · rintro ⟨u, hu⟩
          cases hu
    | inr j => exact bank_at (embedding q) _ _ j
  rw [show ((advance (SourceClauseRowUnitMachine.program sign))^[t]) c = _
    from by simpa only [c] using hr] at he
  simp only [stackCfg, hstart, hend] at he
  exact ⟨t, ht, by simpa only [program, c] using he⟩

theorem final_row {q : Nat}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k w ell : Nat) (sign : Bool)
    (saved output count : List Bool)
    (x : SourceCSPRowQueryFrame.Stack q) :
    finalBank row n r a k w ell sign saved output count (.inl x) = row x := rfl

theorem final_saved {q : Nat}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k w ell : Nat) (sign : Bool)
    (saved output count : List Bool) :
    finalBank row n r a k w ell sign saved output count
      (.inr SourceClauseRowUnitMachine.savedSlot) =
      (EncodedCNF.encodeClause
        (SourceClauseUnitMachine.unitClause
          (SourceClauseRowUnitMachine.p n r a q k w ell) sign)).reverse ++
        saved :=
  SourceClauseRowUnitMachine.final_saved n r a q k w ell sign
    saved output count

theorem final_output {q : Nat}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k w ell : Nat) (sign : Bool)
    (saved output count : List Bool) :
    finalBank row n r a k w ell sign saved output count
      (.inr SourceClauseRowUnitMachine.outputSlot) = output :=
  SourceClauseRowUnitMachine.final_output n r a q k w ell sign
    saved output count

theorem final_count {q : Nat}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k w ell : Nat) (sign : Bool)
    (saved output count : List Bool) :
    finalBank row n r a k w ell sign saved output count
      (.inr SourceClauseRowUnitMachine.countSlot) = true :: count :=
  SourceClauseRowUnitMachine.final_count n r a q k w ell sign
    saved output count

end EthInapproximability.CurrentPaper.SourceClauseRowUnitFrame
