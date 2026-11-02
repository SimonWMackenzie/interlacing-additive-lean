import EthInapproximability.CurrentPaper.SourceClausePrefixUnitAddress
import EthInapproximability.CurrentPaper.SourceClauseUnitMachine
import EthInapproximability.CurrentPaper.BitMachineBroadcast

/-!
Physical prefix address followed by an actual counted unit-clause writer.
The full bank is retained; no arithmetic or final clause is an input.
-/

namespace EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixUnitRun

open Turing BitMachineEncoding BitMachineStackEmbedding

abbrev Stack := PrefixUnitAddress.Stack ⊕ SourceClauseUnitMachine.Stack

def addressEmbedding : PrefixUnitAddress.Stack ↪ Stack := Function.Embedding.inl
def unitEmbedding : SourceClauseUnitMachine.Stack ↪ Stack := Function.Embedding.inr

noncomputable def source : Stack := .inl PrefixUnitAddress.binarySource
def temp : Stack := .inl SourceClauseGateSlotAddress.temp
def target : Stack := .inr SourceClauseUnitMachine.source
def targets : List Stack := [target]

inductive CopyLabel where
  | scan | restore | finish
  deriving DecidableEq, Fintype

noncomputable def copyProgram : CopyLabel → TM2.Stmt (fun _ : Stack => Bool) CopyLabel
    (Unit × Option Bool)
  | .scan => BitMachineBroadcast.scanStep source temp .scan .restore
  | .restore => BitMachineBroadcast.restoreStep temp targets .restore .finish
  | .finish => .halt

noncomputable def initial (n ordinal w ell : ℕ)
    (saved output count : List Bool) : Stack → List Bool :=
  Sum.elim (PrefixUnitAddress.initial n ordinal w ell)
    (SourceClauseUnitMachine.initial [] saved output count)

noncomputable def addressed (n ordinal w ell : ℕ)
    (saved output count : List Bool) : Stack → List Bool :=
  Sum.elim (PrefixUnitAddress.finalBank n ordinal w ell)
    (SourceClauseUnitMachine.initial [] saved output count)

noncomputable def copied (n ordinal w ell : ℕ)
    (saved output count : List Bool) : Stack → List Bool :=
  BitMachineBroadcast.copied source temp targets
    (ordinal * w + (2 * n + ell)).bits
    (addressed n ordinal w ell saved output count)

noncomputable def finished (n ordinal w ell : ℕ) (sign : Bool)
    (saved output count : List Bool) : Stack → List Bool :=
  bank unitEmbedding (copied n ordinal w ell saved output count)
    (SourceClauseUnitMachine.finished
      (SourceClauseUnitMachine.unitClause
        (ordinal * w + (2 * n + ell)) sign)
      saved output count)

abbrev AddressLabel := BitMachineRawSequence.Label
  (BitMachineRawSequence.Label MatrixAddressMachine.Label
    SourceClauseGateSlotAddress.CopyLabel)
  SourceLabelAddressMachine.Label

abbrev UnitLabel := BitMachineRawSequence.Label
  SourceClauseUnitMachine.CopyLabel SourceClauseCountedStream.Label

noncomputable def addressProgram (l : AddressLabel) :=
  stackStmt addressEmbedding (PrefixUnitAddress.program l)

noncomputable def unitProgram (sign : Bool) (l : UnitLabel) :=
  stackStmt unitEmbedding (SourceClauseUnitMachine.program sign l)

noncomputable def program (sign : Bool) :=
  BitMachineRawSequence.program
    (BitMachineRawSequence.program addressProgram copyProgram
      CopyLabel.scan
      ((false, ((), none)),
        (false, (SourceLabelAddressMachine.counter.initial, none)))
      ((), none))
    (unitProgram sign)
    (BitMachineRawSequence.leftLabel SourceClauseUnitMachine.CopyLabel.scan)
    (((false, ((), none)),
        (false, (SourceLabelAddressMachine.counter.initial, none))), ((), none))
    (((), none), (none, ()))

theorem address_initial (n ordinal w ell : ℕ)
    (saved output count : List Bool) :
    bank addressEmbedding (initial n ordinal w ell saved output count)
      (PrefixUnitAddress.initial n ordinal w ell) =
      initial n ordinal w ell saved output count := by
  apply bank_eq_self
  intro k
  rfl

theorem address_final (n ordinal w ell : ℕ)
    (saved output count : List Bool) :
    bank addressEmbedding (initial n ordinal w ell saved output count)
      (PrefixUnitAddress.finalBank n ordinal w ell) =
      addressed n ordinal w ell saved output count := by
  funext k
  cases k with
  | inl x => exact bank_at addressEmbedding _ _ x
  | inr x =>
      rw [bank_outside]
      · rfl
      · intro ⟨y, h⟩; cases h

theorem address_run (n ordinal w ell : ℕ)
    (saved output count : List Bool) :
    ∃ T ≤ PrefixUnitAddress.cost n ordinal w ell,
      ((advance addressProgram)^[T])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)),
          ((false, ((), none)),
            (false, (SourceLabelAddressMachine.counter.initial, none))),
          initial n ordinal w ell saved output count⟩) =
        ⟨none,
          ((false, ((), none)),
            (false, (SourceLabelAddressMachine.counter.initial, none))),
          addressed n ordinal w ell saved output count⟩ := by
  obtain ⟨T, hT, hr⟩ := PrefixUnitAddress.run n ordinal w ell
  have hlift := BitMachineStackRun.run addressEmbedding
    (initial n ordinal w ell saved output count)
    PrefixUnitAddress.program
    (⟨some (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)),
      ((false, ((), none)),
        (false, (SourceLabelAddressMachine.counter.initial, none))),
      PrefixUnitAddress.initial n ordinal w ell⟩) T
  rw [hr] at hlift
  simp only [stackCfg, address_initial, address_final] at hlift
  exact ⟨T, hT, by simpa only [addressProgram] using hlift⟩

theorem addressed_source (n ordinal w ell : ℕ)
    (saved output count : List Bool) :
    addressed n ordinal w ell saved output count source =
      (ordinal * w + (2 * n + ell)).bits := by
  exact PrefixUnitAddress.final_binary n ordinal w ell

theorem addressed_temp (n ordinal w ell : ℕ)
    (saved output count : List Bool) :
    addressed n ordinal w ell saved output count temp = [] := by
  change PrefixUnitAddress.finalBank n ordinal w ell
    SourceClauseGateSlotAddress.temp = []
  rw [PrefixUnitAddress.finalBank, bank_outside]
  · simp [PrefixUnitAddress.transferred,
      SourceClauseGateSlotAddress.transferred,
      BitMachineBroadcast.copied, SourceClauseGateSlotAddress.temp,
      SourceClauseGateSlotAddress.offsetSource]
  · intro ⟨x, h⟩
    cases h

theorem copy_run (n ordinal w ell : ℕ)
    (saved output count : List Bool) :
    let p := ordinal * w + (2 * n + ell)
    ((advance copyProgram)^[2 * p.bits.length + 3])
      (⟨some CopyLabel.scan, ((), none),
        addressed n ordinal w ell saved output count⟩) =
      ⟨none, ((), none), copied n ordinal w ell saved output count⟩ := by
  dsimp only
  let p := ordinal * w + (2 * n + ell)
  have h := BitMachineBroadcast.broadcast_run copyProgram source temp
    (by simp [source, temp, PrefixUnitAddress.binarySource,
      SourceClauseGateSlotAddress.temp,
      SourceClauseGateSlotAddress.gateEmbedding])
    targets (by simp [targets])
    (by simp [source, targets, target])
    (by simp [temp, targets, target])
    .scan .restore .finish rfl rfl () none p.bits
    (addressed n ordinal w ell saved output count)
    (addressed_source n ordinal w ell saved output count)
    (addressed_temp n ordinal w ell saved output count)
  rw [show 2 * p.bits.length + 3 = (2 * p.bits.length + 2) + 1 by omega,
    Function.iterate_succ_apply']
  change advance copyProgram
    (BitMachineBroadcast.run copyProgram (2 * p.bits.length + 2)
      (⟨some .scan, ((), none),
        addressed n ordinal w ell saved output count⟩)) = _
  rw [h]
  simp [advance, TM2.step, copyProgram, copied, p]

theorem unit_ready (n ordinal w ell : ℕ)
    (saved output count : List Bool) :
    let p := ordinal * w + (2 * n + ell)
    bank unitEmbedding (copied n ordinal w ell saved output count)
      (SourceClauseUnitMachine.initial p.bits saved output count) =
      copied n ordinal w ell saved output count := by
  dsimp only
  apply bank_eq_self
  intro k
  cases k with
  | inl x =>
      fin_cases x <;>
        simp [copied, BitMachineBroadcast.copied, unitEmbedding,
          SourceClauseUnitMachine.source, source, temp,
          targets, target, addressed, SourceClauseUnitMachine.initial]
  | inr x =>
      simp [copied, BitMachineBroadcast.copied, unitEmbedding,
        SourceClauseUnitMachine.source, source, temp,
        targets, target, addressed, SourceClauseUnitMachine.initial]

theorem unit_run (n ordinal w ell : ℕ) (sign : Bool)
    (saved output count : List Bool) :
    let p := ordinal * w + (2 * n + ell)
    ∃ T ≤ 5 * p.bits.length + 13,
      ((advance (unitProgram sign))^[T])
        (⟨some (BitMachineRawSequence.leftLabel SourceClauseUnitMachine.CopyLabel.scan),
          (((), none), (none, ())),
          copied n ordinal w ell saved output count⟩) =
        ⟨none, (((), none), (none, ())),
          finished n ordinal w ell sign saved output count⟩ := by
  dsimp only
  let p := ordinal * w + (2 * n + ell)
  obtain ⟨T, hT, hr⟩ := SourceClauseUnitMachine.unit_run
    p sign saved output count
  have hlift := BitMachineStackRun.run unitEmbedding
    (copied n ordinal w ell saved output count)
    (SourceClauseUnitMachine.program sign)
    (⟨some (BitMachineRawSequence.leftLabel SourceClauseUnitMachine.CopyLabel.scan),
      (((), none), (none, ())),
      SourceClauseUnitMachine.initial p.bits saved output count⟩) T
  rw [hr] at hlift
  simp only [stackCfg] at hlift
  rw [unit_ready] at hlift
  exact ⟨T, hT, by simpa only [unitProgram, finished] using hlift⟩

noncomputable def cost (n ordinal w ell : ℕ) : ℕ :=
  let p := ordinal * w + (2 * n + ell)
  PrefixUnitAddress.cost n ordinal w ell +
    (2 * p.bits.length + 3) + 1 + (5 * p.bits.length + 13) + 1

noncomputable def startControl :
    (((Bool × (Unit × Option Bool)) × SourceLabelAddressMachine.Control) ×
      (Unit × Option Bool)) ×
      ((Unit × Option Bool) × SourceClauseCountedStream.Control) :=
  ((((false, ((), none)),
      (false, (SourceLabelAddressMachine.counter.initial, none))),
    ((), none)), (((), none), (none, ())))

theorem run (n ordinal w ell : ℕ) (sign : Bool)
    (saved output count : List Bool) :
    ∃ T ≤ cost n ordinal w ell,
      ((advance (program sign))^[T])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                MatrixAddressMachine.Label.outer)))),
          startControl,
          initial n ordinal w ell saved output count⟩) =
        ⟨none,
          startControl,
          finished n ordinal w ell sign saved output count⟩ := by
  let p := ordinal * w + (2 * n + ell)
  obtain ⟨ta, hta, ha⟩ := address_run n ordinal w ell saved output count
  have hc := copy_run n ordinal w ell saved output count
  obtain ⟨tab, htab, hab⟩ := BitMachineRawSequence.runs
    addressProgram copyProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer))
    CopyLabel.scan
    ((false, ((), none)),
      (false, (SourceLabelAddressMachine.counter.initial, none)))
    ((false, ((), none)),
      (false, (SourceLabelAddressMachine.counter.initial, none)))
    ((), none) ((), none)
    (initial n ordinal w ell saved output count)
    (addressed n ordinal w ell saved output count)
    (copied n ordinal w ell saved output count)
    ta (2 * p.bits.length + 3) ha hc
  obtain ⟨tu, htu, hu⟩ := unit_run n ordinal w ell sign
    saved output count
  obtain ⟨T, hT, hr⟩ := BitMachineRawSequence.runs
    (BitMachineRawSequence.program addressProgram copyProgram
      CopyLabel.scan
      ((false, ((), none)),
        (false, (SourceLabelAddressMachine.counter.initial, none)))
      ((), none))
    (unitProgram sign)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          MatrixAddressMachine.Label.outer)))
    (BitMachineRawSequence.leftLabel SourceClauseUnitMachine.CopyLabel.scan)
    (((false, ((), none)),
        (false, (SourceLabelAddressMachine.counter.initial, none))), ((), none))
    (((false, ((), none)),
        (false, (SourceLabelAddressMachine.counter.initial, none))), ((), none))
    (((), none), (none, ())) (((), none), (none, ()))
    (initial n ordinal w ell saved output count)
    (copied n ordinal w ell saved output count)
    (finished n ordinal w ell sign saved output count)
    tab tu hab hu
  exact ⟨T, by dsimp [cost, p] at *; omega,
    by simpa only [program, startControl] using hr⟩

def savedKey : Stack := .inr (.inr (.inl 3))
def outputKey : Stack := .inr (.inr (.inl 4))
def countKey : Stack := .inr (.inr (.inr ()))

theorem final_saved (n ordinal w ell : ℕ) (sign : Bool)
    (saved output count : List Bool) :
    finished n ordinal w ell sign saved output count savedKey =
      (EncodedCNF.encodeClause (SourceClauseUnitMachine.unitClause
        (ordinal * w + (2 * n + ell)) sign)).reverse ++ saved := by
  rw [finished, show savedKey = unitEmbedding (.inr (.inl 3)) by rfl,
    bank_at]
  rfl

theorem final_count (n ordinal w ell : ℕ) (sign : Bool)
    (saved output count : List Bool) :
    finished n ordinal w ell sign saved output count countKey =
      true :: count := by
  rw [finished, show countKey = unitEmbedding (.inr (.inr ())) by rfl,
    bank_at]
  rfl

theorem final_output (n ordinal w ell : ℕ) (sign : Bool)
    (saved output count : List Bool) :
    finished n ordinal w ell sign saved output count outputKey = output := by
  rw [finished, show outputKey = unitEmbedding (.inr (.inl 4)) by rfl,
    bank_at]
  rfl

end EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixUnitRun
