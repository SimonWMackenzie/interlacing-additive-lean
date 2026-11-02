import EthInapproximability.CurrentPaper.SourceClauseRowWriterGateReady

/-!
# One fully staged physical row-literal OR gate

The staged bank is extensionally the existing indexed-gate machine's actual
initial bank. We therefore inline its instruction table after the charged
operand/query staging sequence. The endpoint contains the machine-produced
three clauses and incremented unary count, not a supplied gate result.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseRowWriterGateRun

open Turing BitMachineEncoding BitMachineStackEmbedding
open scoped Classical

noncomputable def embedding {q : ℕ} :
    SourceClauseRowWriterCore.Gate q ↪ SourceClauseRowWriterOperands.Stack q where
  toFun := SourceClauseRowWriterOperands.gateCell
  inj' := by
    intro x y h
    exact SourceClauseRowWriterCore.gateEmbedding.injective
      (Sum.inl.inj h)

theorem prepared_bank {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (saved output count : List Bool)
    (h : row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    bank (embedding (q := q))
      (SourceClauseRowWriterStageEcho.prepared j row n r a k s t w
        saved output count)
      (SourceClauseRowIndexedGate.initial j row n r a k s t w
        saved output count) =
    SourceClauseRowWriterStageEcho.prepared j row n r a k s t w
      saved output count := by
  apply bank_eq_self
  intro x
  simpa only [embedding] using
    (SourceClauseRowWriterGateReady.gate_initial_bank
      j row n r a k s t w saved output count h x).symm

noncomputable def gateProgram {q : ℕ} (j : Fin q) (sign : Bool) :=
  fun l => stackStmt (embedding (q := q))
    (SourceClauseRowIndexedGate.program j sign l)

noncomputable def program {q : ℕ} (j : Fin q)
    (a k s t w : ℕ) (sign : Bool) :=
  BitMachineRawSequence.program
    (SourceClauseRowWriterStageEcho.program j a k s t w)
    (gateProgram j sign)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer))))
    ((((((), none), ((), none)), ()), ((), none)))
    ((SourceClauseRowIndexedGate.slotControl, ((), none)),
      SourceClauseRowIndexedGate.gateControl)

def stageCost {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) :=
  (((2 * n + 3) + (2 * r + 3) + 1) +
    (SourceClauseFixedBatch.costPrefix
      (SourceClauseRowWriterOperands.gateSizes a q k s t w) 8 + 1) + 1) +
    (2 * (row (.inl (j, 1))).length + 3) + 1

noncomputable def result {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (sign : Bool)
    (saved output count : List Bool) :=
  bank (embedding (q := q))
    (SourceClauseRowWriterStageEcho.prepared j row n r a k s t w
      saved output count)
    (SourceClauseRowIndexedGate.finalBank j row n r a k s t w sign
      saved output count)

theorem run {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (sign : Bool)
    (saved output count : List Bool)
    (h : row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    ∃ T ≤ stageCost j row n r a k s t w +
        SourceClauseRowIndexedGate.cost q n r a k
          (row (.inl (j, 1))).length s t w sign + 1,
      ((advance (program j a k s t w sign))^[T])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                SourceClausePreservingBroadcast.Label.scan)))),
          (((((((), none), ((), none)), ()), ((), none))),
            ((SourceClauseRowIndexedGate.slotControl, ((), none)),
              SourceClauseRowIndexedGate.gateControl)),
          SourceClauseRowWriterBlank.bank row n r saved output count⟩) =
        ⟨none,
          (((((((), none), ((), none)), ()), ((), none))),
            ((SourceClauseRowIndexedGate.slotControl, ((), none)),
              SourceClauseRowIndexedGate.gateControl)),
          result j row n r a k s t w sign saved output count⟩ := by
  obtain ⟨ts, hts, hs⟩ := SourceClauseRowWriterStageEcho.run
    j row n r a k s t w saved output count h
  obtain ⟨tg, htg, hg⟩ := SourceClauseRowIndexedGate.run
    j row n r a k s t w sign saved output count h
  have hlift := BitMachineStackRun.run (embedding (q := q))
    (SourceClauseRowWriterStageEcho.prepared j row n r a k s t w
      saved output count)
    (SourceClauseRowIndexedGate.program j sign)
    (⟨some (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)))),
      ((SourceClauseRowIndexedGate.slotControl, ((), none)),
        SourceClauseRowIndexedGate.gateControl),
      SourceClauseRowIndexedGate.initial j row n r a k s t w
        saved output count⟩) tg
  rw [hg] at hlift
  simp only [stackCfg,
    prepared_bank j row n r a k s t w saved output count h] at hlift
  obtain ⟨T, hT, hrun⟩ := BitMachineRawSequence.runs
    (SourceClauseRowWriterStageEcho.program j a k s t w)
    (gateProgram j sign)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          SourceClausePreservingBroadcast.Label.scan)))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer))))
    ((((((), none), ((), none)), ()), ((), none)))
    ((((((), none), ((), none)), ()), ((), none)))
    ((SourceClauseRowIndexedGate.slotControl, ((), none)),
      SourceClauseRowIndexedGate.gateControl)
    ((SourceClauseRowIndexedGate.slotControl, ((), none)),
      SourceClauseRowIndexedGate.gateControl)
    (SourceClauseRowWriterBlank.bank row n r saved output count)
    (SourceClauseRowWriterStageEcho.prepared j row n r a k s t w
      saved output count)
    (result j row n r a k s t w sign saved output count)
    ts tg hs hlift
  exact ⟨T, by simpa [stageCost] using Nat.le_trans hT (by omega), hrun⟩

theorem final_count {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (sign : Bool)
    (saved output count : List Bool) :
    result j row n r a k s t w sign saved output count
      (SourceClauseRowWriterOperands.gateCell
        SourceClauseRowGateCleanup.countCell) =
      true :: true :: true :: count := by
  change (bank (embedding (q := q))
    (SourceClauseRowWriterStageEcho.prepared j row n r a k s t w
      saved output count)
    (SourceClauseRowIndexedGate.finalBank j row n r a k s t w sign
      saved output count))
    (embedding SourceClauseRowGateCleanup.countCell) = _
  rw [bank_at]
  exact SourceClauseRowIndexedGate.final_count
    j row n r a k s t w sign saved output count

theorem final_saved {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (sign : Bool)
    (saved output count : List Bool) :
    let p := SourceClauseRowSlotAddress.slot n r a q k * w + (n * a + t)
    result j row n r a k s t w sign saved output count
      (SourceClauseRowWriterOperands.gateCell
        SourceClauseRowGateCleanup.savedCell) =
      (EncodedCNF.encodeClause
        (SourceClauseGatePrepare.thirdClause p
          ⟨(row (.inl (j, 1))).length * a + s, sign⟩)).reverse ++
      (EncodedCNF.encodeClause (SourceClauseGatePrepare.secondClause p)).reverse ++
      (EncodedCNF.encodeClause
        (SourceClauseGatePrepare.firstClause p
          ⟨(row (.inl (j, 1))).length * a + s, sign⟩)).reverse ++ saved := by
  change (bank (embedding (q := q))
    (SourceClauseRowWriterStageEcho.prepared j row n r a k s t w
      saved output count)
    (SourceClauseRowIndexedGate.finalBank j row n r a k s t w sign
      saved output count))
    (embedding SourceClauseRowGateCleanup.savedCell) = _
  rw [bank_at]
  exact SourceClauseRowIndexedGate.final_saved
    j row n r a k s t w sign saved output count

theorem final_row {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (sign : Bool)
    (saved output count : List Bool)
    (h : row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true)
    (x : SourceCSPRowQueryFrame.Stack q) :
    result j row n r a k s t w sign saved output count
      (SourceClauseRowWriterOperands.gateCell
        (SourceClauseRowGateCleanup.rowCell x)) = row x := by
  change (bank (embedding (q := q))
    (SourceClauseRowWriterStageEcho.prepared j row n r a k s t w
      saved output count)
    (SourceClauseRowIndexedGate.finalBank j row n r a k s t w sign
      saved output count))
    (embedding (SourceClauseRowGateCleanup.rowCell x)) = _
  rw [bank_at]
  exact SourceClauseRowIndexedGate.final_row
    j row n r a k s t w sign saved output count h x

end EthInapproximability.CurrentPaper.SourceClauseRowWriterGateRun
