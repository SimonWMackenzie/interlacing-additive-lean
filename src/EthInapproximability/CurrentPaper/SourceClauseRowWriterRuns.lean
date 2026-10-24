import EthInapproximability.CurrentPaper.SourceClauseRowWriterCore

/-!
# Actual gate and unit runs in the shared physical writer bank

These are lifts of the existing instruction tables, not endpoint-only
identities. They permit an alternating row schedule to use one reverse payload
and one unary clause count, with the checked row untouched.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseRowWriterRuns

open Turing BitMachineEncoding BitMachineStackEmbedding
open scoped Classical

noncomputable def gateProgram {q : ℕ} (j : Fin q) (sign : Bool) :=
  fun l => stackStmt (SourceClauseRowWriterCore.gateEmbedding (q := q))
    (SourceClauseRowIndexedGate.program j sign l)

noncomputable def unitProgram (q : ℕ) (sign : Bool) :=
  fun l => stackStmt (SourceClauseRowWriterCore.unitEmbedding (q := q))
    (SourceClauseRowUnitFrame.program q sign l)

theorem gate_run {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (sign : Bool)
    (saved output count : List Bool)
    (foreign : SourceClauseRowWriterCore.Stack q → List Bool)
    (h : row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    ∃ T ≤ SourceClauseRowIndexedGate.cost q n r a k
        (row (.inl (j, 1))).length s t w sign,
      ((advance (gateProgram j sign))^[T])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)))),
          ((SourceClauseRowIndexedGate.slotControl, ((), none)),
            SourceClauseRowIndexedGate.gateControl),
          bank SourceClauseRowWriterCore.gateEmbedding foreign
            (SourceClauseRowIndexedGate.initial j row n r a k s t w
              saved output count)⟩) =
        ⟨none,
          ((SourceClauseRowIndexedGate.slotControl, ((), none)),
            SourceClauseRowIndexedGate.gateControl),
          bank SourceClauseRowWriterCore.gateEmbedding foreign
            (SourceClauseRowIndexedGate.finalBank j row n r a k s t w sign
              saved output count)⟩ := by
  obtain ⟨T, hT, hr⟩ := SourceClauseRowIndexedGate.run j row n r a k
    s t w sign saved output count h
  have he := BitMachineStackRun.run
    (SourceClauseRowWriterCore.gateEmbedding (q := q)) foreign
    (SourceClauseRowIndexedGate.program j sign)
    (⟨some (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)))),
      ((SourceClauseRowIndexedGate.slotControl, ((), none)),
        SourceClauseRowIndexedGate.gateControl),
      SourceClauseRowIndexedGate.initial j row n r a k s t w
        saved output count⟩) T
  rw [hr] at he
  exact ⟨T, hT, he⟩

theorem unit_run {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k w ell : ℕ) (sign : Bool)
    (saved output count : List Bool)
    (foreign : SourceClauseRowWriterCore.Stack q → List Bool) :
    ∃ T ≤ SourceClauseRowUnitMachine.cost n r a q k w ell,
      ((advance (unitProgram q sign))^[T])
        (⟨some SourceClauseRowUnitMachine.startLabel,
          SourceClauseRowUnitMachine.startControl,
          bank SourceClauseRowWriterCore.unitEmbedding foreign
            (SourceClauseRowUnitFrame.initial row n r a k w ell
              saved output count)⟩) =
        ⟨none, SourceClauseRowUnitMachine.startControl,
          bank SourceClauseRowWriterCore.unitEmbedding foreign
            (SourceClauseRowUnitFrame.finalBank row n r a k w ell sign
              saved output count)⟩ := by
  obtain ⟨T, hT, hr⟩ := SourceClauseRowUnitFrame.run row n r a k
    w ell sign saved output count
  have he := BitMachineStackRun.run
    (SourceClauseRowWriterCore.unitEmbedding (q := q)) foreign
    (SourceClauseRowUnitFrame.program q sign)
    (⟨some SourceClauseRowUnitMachine.startLabel,
      SourceClauseRowUnitMachine.startControl,
      SourceClauseRowUnitFrame.initial row n r a k w ell
        saved output count⟩) T
  rw [hr] at he
  exact ⟨T, hT, he⟩

theorem gate_to_unit_core {q : ℕ}
    (foreign : SourceClauseRowWriterCore.Stack q → List Bool)
    (S : SourceClauseRowWriterCore.Gate q → List Bool)
    (c : SourceClauseRowWriterCore.Core q) :
    bank SourceClauseRowWriterCore.gateEmbedding foreign S
      (SourceClauseRowWriterCore.unitEmbedding
        (SourceClauseRowWriterCore.unitCore c)) =
      S (SourceClauseRowWriterCore.gateCore c) := by
  exact SourceClauseSharedCore.left_bank_right_core
    SourceClauseRowWriterCore.gateCore SourceClauseRowWriterCore.unitCore
    foreign S c

theorem unit_to_gate_core {q : ℕ}
    (foreign : SourceClauseRowWriterCore.Stack q → List Bool)
    (S : SourceClauseRowWriterCore.UnitBank q → List Bool)
    (c : SourceClauseRowWriterCore.Core q) :
    bank SourceClauseRowWriterCore.unitEmbedding foreign S
      (SourceClauseRowWriterCore.gateEmbedding
        (SourceClauseRowWriterCore.gateCore c)) =
      S (SourceClauseRowWriterCore.unitCore c) := by
  exact SourceClauseSharedCore.right_bank_left_core
    SourceClauseRowWriterCore.gateCore SourceClauseRowWriterCore.unitCore
    foreign S c

end EthInapproximability.CurrentPaper.SourceClauseRowWriterRuns
