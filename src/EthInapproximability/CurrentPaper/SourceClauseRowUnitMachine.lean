import EthInapproximability.CurrentPaper.SourceClauseRowUnitAddress
import EthInapproximability.CurrentPaper.SourceClauseUnitMachine

/-!
# Physical source-row opening or closing unit clause

The address controller starts from unary `n,a,r,k,w,ell`. Its binary output
is physically transferred to the frozen counted unit-clause writer. The
writer, not an initial clause value, produces the repeated signed literal,
reverse accumulator update, and unary count increment.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseRowUnitMachine

open Turing BitMachineEncoding BitMachineStackEmbedding

abbrev Stack := SourceClauseRowUnitAddress.Stack ⊕ SourceClauseUnitMachine.Stack

def addressEmbedding : SourceClauseRowUnitAddress.Stack ↪ Stack :=
  Function.Embedding.inl
def unitEmbedding : SourceClauseUnitMachine.Stack ↪ Stack :=
  Function.Embedding.inr

noncomputable def binarySource : Stack :=
  .inl SourceClauseRowUnitAddress.binarySource
def binaryTemp : Stack :=
  .inl (SourceClauseRowUnitAddress.labelEmbedding (.inl 3))
def unitTarget : Stack := .inr SourceClauseUnitMachine.source

abbrev p (n r a q k w ell : Nat) :=
  SourceClauseRowUnitAddress.address n r a q k w ell

inductive CopyLabel where
  | scan | restore | finish
  deriving DecidableEq, Fintype

noncomputable def copyProgram : CopyLabel →
    TM2.Stmt (fun _ : Stack => Bool) CopyLabel (Unit × Option Bool)
  | .scan => BitMachineBroadcast.scanStep binarySource binaryTemp .scan .restore
  | .restore => BitMachineBroadcast.restoreStep binaryTemp [unitTarget]
      .restore .finish
  | .finish => .halt

noncomputable def initial (n r a q k w ell : Nat)
    (saved output count : List Bool) : Stack → List Bool :=
  Sum.elim (SourceClauseRowUnitAddress.initial n r a q k w ell)
    (SourceClauseUnitMachine.initial [] saved output count)

noncomputable def addressDone (n r a q k w ell : Nat)
    (saved output count : List Bool) : Stack → List Bool :=
  Sum.elim (SourceClauseRowUnitAddress.addressed n r a q k w ell)
    (SourceClauseUnitMachine.initial [] saved output count)

noncomputable def copied (n r a q k w ell : Nat)
    (saved output count : List Bool) : Stack → List Bool :=
  BitMachineBroadcast.copied binarySource binaryTemp [unitTarget]
    (p n r a q k w ell).bits
    (addressDone n r a q k w ell saved output count)

noncomputable def finalBank (n r a q k w ell : Nat) (sign : Bool)
    (saved output count : List Bool) : Stack → List Bool :=
  bank unitEmbedding (copied n r a q k w ell saved output count)
    (SourceClauseUnitMachine.finished
      (SourceClauseUnitMachine.unitClause (p n r a q k w ell) sign)
      saved output count)

noncomputable def addressProgram (l : SourceClauseRowUnitAddress.Label) :=
  stackStmt addressEmbedding (SourceClauseRowUnitAddress.program l)

def unitProgram (sign : Bool)
    (l : BitMachineRawSequence.Label SourceClauseUnitMachine.CopyLabel
      SourceClauseCountedStream.Label) :=
  stackStmt unitEmbedding (SourceClauseUnitMachine.program sign l)

abbrev UnitLabel := BitMachineRawSequence.Label
  SourceClauseUnitMachine.CopyLabel SourceClauseCountedStream.Label
abbrev UnitControl := (Unit × Option Bool) × SourceClauseCountedStream.Control

abbrev PreLabel := BitMachineRawSequence.Label
  SourceClauseRowUnitAddress.Label CopyLabel
abbrev PreControl := SourceClauseRowUnitAddress.Control × (Unit × Option Bool)

noncomputable def preProgram := BitMachineRawSequence.program
  addressProgram copyProgram CopyLabel.scan
  (((((false, ((), none)), false), false), (((), none), ((), none))),
    (false, (SourceLabelAddressMachine.counter.initial, none)))
  ((), none)

abbrev Label := BitMachineRawSequence.Label PreLabel UnitLabel
abbrev Control := PreControl × UnitControl

noncomputable def addressControl : SourceClauseRowUnitAddress.Control :=
  (((((false, ((), none)), false), false), (((), none), ((), none))),
    (false, (SourceLabelAddressMachine.counter.initial, none)))
noncomputable def preControl : PreControl := (addressControl, ((), none))
noncomputable def startControl : Control :=
  (preControl, (((), none), (none, ())))
def startLabel : Label :=
  BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          MatrixAddressMachine.Label.outer))))))

noncomputable def program (sign : Bool) := BitMachineRawSequence.program
  preProgram (unitProgram sign)
  (BitMachineRawSequence.leftLabel SourceClauseUnitMachine.CopyLabel.scan)
  preControl
  (((), none), (none, ()))

noncomputable def cost (n r a q k w ell : Nat) : Nat :=
  SourceClauseRowUnitAddress.cost n r a q k w ell +
    (2 * (p n r a q k w ell).bits.length + 3) +
    (5 * (p n r a q k w ell).bits.length + 13) + 2

def savedSlot : Stack := .inr (.inr (.inl 3))
def outputSlot : Stack := .inr (.inr (.inl 4))
def countSlot : Stack := .inr (.inr (.inr ()))

theorem final_saved (n r a q k w ell : Nat) (sign : Bool)
    (saved output count : List Bool) :
    finalBank n r a q k w ell sign saved output count savedSlot =
      (EncodedCNF.encodeClause
        (SourceClauseUnitMachine.unitClause (p n r a q k w ell) sign)).reverse ++
        saved := by
  change finalBank n r a q k w ell sign saved output count
    (unitEmbedding (.inr (.inl 3))) = _
  rw [finalBank, bank_at]
  rfl

theorem final_output (n r a q k w ell : Nat) (sign : Bool)
    (saved output count : List Bool) :
    finalBank n r a q k w ell sign saved output count outputSlot = output := by
  change finalBank n r a q k w ell sign saved output count
    (unitEmbedding (.inr (.inl 4))) = _
  rw [finalBank, bank_at]
  rfl

theorem final_count (n r a q k w ell : Nat) (sign : Bool)
    (saved output count : List Bool) :
    finalBank n r a q k w ell sign saved output count countSlot =
      true :: count := by
  change finalBank n r a q k w ell sign saved output count
    (unitEmbedding (.inr (.inr ()))) = _
  rw [finalBank, bank_at]
  rfl

theorem address_run (n r a q k w ell : Nat)
    (saved output count : List Bool) :
    ∃ t ≤ SourceClauseRowUnitAddress.cost n r a q k w ell,
      ((advance addressProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel
                  MatrixAddressMachine.Label.outer))))),
          (((((false, ((), none)), false), false),
            (((), none), ((), none))),
            (false, (SourceLabelAddressMachine.counter.initial, none))),
          initial n r a q k w ell saved output count⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            SourceClauseRowUnitAddress.Label SourceClauseRowUnitAddress.Control) =
        ⟨none,
          (((((false, ((), none)), false), false),
            (((), none), ((), none))),
            (false, (SourceLabelAddressMachine.counter.initial, none))),
          addressDone n r a q k w ell saved output count⟩ := by
  obtain ⟨t, ht, hr⟩ := SourceClauseRowUnitAddress.run n r a q k w ell
  let c : TM2.Cfg (fun _ : SourceClauseRowUnitAddress.Stack => Bool)
      SourceClauseRowUnitAddress.Label SourceClauseRowUnitAddress.Control :=
    ⟨some (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              MatrixAddressMachine.Label.outer))))),
      (((((false, ((), none)), false), false),
        (((), none), ((), none))),
        (false, (SourceLabelAddressMachine.counter.initial, none))),
      SourceClauseRowUnitAddress.initial n r a q k w ell⟩
  have he := BitMachineStackRun.run addressEmbedding
    (initial n r a q k w ell saved output count)
    SourceClauseRowUnitAddress.program c t
  have hstart : bank addressEmbedding
      (initial n r a q k w ell saved output count) c.stk =
      initial n r a q k w ell saved output count := by
    apply bank_eq_self
    intro i
    rfl
  have hend : bank addressEmbedding
      (initial n r a q k w ell saved output count)
      (SourceClauseRowUnitAddress.addressed n r a q k w ell) =
      addressDone n r a q k w ell saved output count := by
    funext i
    cases i with
    | inl j => exact bank_at addressEmbedding _ _ j
    | inr j =>
        rw [bank_outside]
        · rfl
        · rintro ⟨u, hu⟩
          cases hu
  rw [show ((advance SourceClauseRowUnitAddress.program)^[t]) c = _ from
    by simpa only [c] using hr] at he
  simp only [stackCfg, hstart, hend] at he
  exact ⟨t, ht, by simpa only [addressProgram, c] using he⟩

theorem binary_source (n r a q k w ell : Nat)
    (saved output count : List Bool) :
    addressDone n r a q k w ell saved output count binarySource =
      (p n r a q k w ell).bits := by
  exact SourceClauseRowUnitAddress.binary_result n r a q k w ell

theorem binary_temp (n r a q k w ell : Nat)
    (saved output count : List Bool) :
    addressDone n r a q k w ell saved output count binaryTemp = [] := by
  change SourceClauseRowUnitAddress.addressed n r a q k w ell
    (SourceClauseRowUnitAddress.labelEmbedding (.inl 3)) = []
  rw [SourceClauseRowUnitAddress.addressed, bank_at]
  rfl

theorem copy_run (n r a q k w ell : Nat)
    (saved output count : List Bool) :
    ((advance copyProgram)^[2 * (p n r a q k w ell).bits.length + 3])
      (⟨some .scan, ((), none), addressDone n r a q k w ell
        saved output count⟩ :
        TM2.Cfg (fun _ : Stack => Bool) CopyLabel (Unit × Option Bool)) =
      ⟨none, ((), none), copied n r a q k w ell saved output count⟩ := by
  let bits := (p n r a q k w ell).bits
  have hr := BitMachineBroadcast.broadcast_run copyProgram
    binarySource binaryTemp (by decide) [unitTarget] (by simp)
    (by simp [binarySource, unitTarget])
    (by simp [binaryTemp, unitTarget])
    .scan .restore .finish rfl rfl () none bits
    (addressDone n r a q k w ell saved output count)
    (binary_source ..) (binary_temp ..)
  rw [show 2 * (p n r a q k w ell).bits.length + 3 =
      2 * bits.length + 2 + 1 by rfl,
    Function.iterate_succ_apply']
  change advance copyProgram
    (BitMachineBroadcast.run copyProgram (2 * bits.length + 2)
      (⟨some .scan, ((), none), addressDone n r a q k w ell
        saved output count⟩ :
        TM2.Cfg (fun _ : Stack => Bool) CopyLabel (Unit × Option Bool))) = _
  rw [hr]
  simp [advance, TM2.step, copyProgram, copied, bits]

theorem unit_ready (n r a q k w ell : Nat)
    (saved output count : List Bool) :
    (fun i => copied n r a q k w ell saved output count (unitEmbedding i)) =
      SourceClauseUnitMachine.initial (p n r a q k w ell).bits
        saved output count := by
  funext i
  cases i with
  | inl j =>
      fin_cases j <;>
        simp [copied, BitMachineBroadcast.copied, binarySource,
          binaryTemp, unitTarget, unitEmbedding, addressDone,
          SourceClauseUnitMachine.initial,
          SourceClauseUnitMachine.source]
  | inr j =>
      simp [copied, BitMachineBroadcast.copied, binarySource,
        binaryTemp, unitTarget, unitEmbedding, addressDone,
        SourceClauseUnitMachine.initial,
        SourceClauseUnitMachine.source]

theorem unit_run (n r a q k w ell : Nat) (sign : Bool)
    (saved output count : List Bool) :
    ∃ t ≤ 5 * (p n r a q k w ell).bits.length + 13,
      ((advance (unitProgram sign))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          SourceClauseUnitMachine.CopyLabel.scan),
          (((), none), (none, ())),
          copied n r a q k w ell saved output count⟩ :
          TM2.Cfg (fun _ : Stack => Bool) UnitLabel UnitControl) =
        ⟨none, (((), none), (none, ())),
          finalBank n r a q k w ell sign saved output count⟩ := by
  let value := p n r a q k w ell
  obtain ⟨t, ht, hr⟩ := SourceClauseUnitMachine.unit_run value sign
    saved output count
  let localCfg : TM2.Cfg (fun _ : SourceClauseUnitMachine.Stack => Bool)
      UnitLabel UnitControl :=
    ⟨some (BitMachineRawSequence.leftLabel
      SourceClauseUnitMachine.CopyLabel.scan),
      (((), none), (none, ())),
      SourceClauseUnitMachine.initial value.bits saved output count⟩
  have he := BitMachineStackRun.run unitEmbedding
    (copied n r a q k w ell saved output count)
    (SourceClauseUnitMachine.program sign) localCfg t
  have hstart : bank unitEmbedding
      (copied n r a q k w ell saved output count) localCfg.stk =
      copied n r a q k w ell saved output count := by
    apply bank_eq_self
    intro i
    exact congrFun (unit_ready n r a q k w ell saved output count) i |>.symm
  rw [show ((advance (SourceClauseUnitMachine.program sign))^[t]) localCfg =
      ⟨none, (((), none), (none, ())),
        SourceClauseUnitMachine.finished
          (SourceClauseUnitMachine.unitClause value sign)
          saved output count⟩ from by
            simpa only [localCfg] using hr] at he
  simp only [stackCfg, hstart] at he
  exact ⟨t, by simpa only [value] using ht,
    by simpa only [unitProgram, finalBank, value, localCfg] using he⟩

theorem run (n r a q k w ell : Nat) (sign : Bool)
    (saved output count : List Bool) :
    ∃ t ≤ cost n r a q k w ell,
      ((advance (program sign))^[t])
        (⟨some startLabel, startControl,
          initial n r a q k w ell saved output count⟩ :
          TM2.Cfg (fun _ : Stack => Bool) Label Control) =
        ⟨none, startControl,
          finalBank n r a q k w ell sign saved output count⟩ := by
  obtain ⟨ta, hta, hra⟩ := address_run n r a q k w ell
    saved output count
  obtain ⟨tc, htc, hrc⟩ := BitMachineRawSequence.runs
    addressProgram copyProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              MatrixAddressMachine.Label.outer)))) :
        SourceClauseRowUnitAddress.Label)
    CopyLabel.scan
    (((((false, ((), none)), false), false),
      (((), none), ((), none))),
      (false, (SourceLabelAddressMachine.counter.initial, none)))
    (((((false, ((), none)), false), false),
      (((), none), ((), none))),
      (false, (SourceLabelAddressMachine.counter.initial, none)))
    (((), none) : Unit × Option Bool) ((), none)
    (initial n r a q k w ell saved output count)
    (addressDone n r a q k w ell saved output count)
    (copied n r a q k w ell saved output count)
    ta (2 * (p n r a q k w ell).bits.length + 3)
    hra (copy_run n r a q k w ell saved output count)
  obtain ⟨tu, htu, hru⟩ := unit_run n r a q k w ell sign
    saved output count
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    preProgram (unitProgram sign)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                MatrixAddressMachine.Label.outer))))) : PreLabel)
    (BitMachineRawSequence.leftLabel
      SourceClauseUnitMachine.CopyLabel.scan : UnitLabel)
    ((((((false, ((), none)), false), false),
      (((), none), ((), none))),
      (false, (SourceLabelAddressMachine.counter.initial, none))),
      ((), none))
    ((((((false, ((), none)), false), false),
      (((), none), ((), none))),
      (false, (SourceLabelAddressMachine.counter.initial, none))),
      ((), none))
    ((((), none), (none, ())) : UnitControl)
    (((), none), (none, ()))
    (initial n r a q k w ell saved output count)
    (copied n r a q k w ell saved output count)
    (finalBank n r a q k w ell sign saved output count)
    tc tu (by simpa only [preProgram] using hrc)
    (by simpa only [unitProgram] using hru)
  refine ⟨t, ?_, ?_⟩
  · dsimp [cost] at *
    omega
  · simpa only [program, startLabel, startControl, preControl,
      addressControl] using hr

end EthInapproximability.CurrentPaper.SourceClauseRowUnitMachine
