import EthInapproximability.CurrentPaper.SourceClausePrefixUnitRun
import EthInapproximability.CurrentPaper.SourceGenericUnitAddress

/-! The existing prefix-unit controller, run on its generic-alphabet
address banks. No instruction depends on the dynamic `n` or `ordinal`. -/

namespace EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.UnitRun

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceBooleanPrefix
open scoped Classical

abbrev Stack := PrefixUnitRun.Stack

noncomputable def initial (n a ordinal w ell : Nat)
    (saved output count : List Bool) : Stack → List Bool :=
  Sum.elim (SourceGenericUnitAddress.initial n a ordinal w ell)
    (SourceClauseUnitMachine.initial [] saved output count)

noncomputable def addressed (n a ordinal w ell : Nat)
    (saved output count : List Bool) : Stack → List Bool :=
  Sum.elim (SourceGenericUnitAddress.finalBank n a ordinal w ell)
    (SourceClauseUnitMachine.initial [] saved output count)

noncomputable def copied (n a ordinal w ell : Nat)
    (saved output count : List Bool) : Stack → List Bool :=
  BitMachineBroadcast.copied PrefixUnitRun.source PrefixUnitRun.temp
    PrefixUnitRun.targets (ordinal*w+(n*a+ell)).bits
    (addressed n a ordinal w ell saved output count)

noncomputable def finished (n a ordinal w ell : Nat) (sign : Bool)
    (saved output count : List Bool) : Stack → List Bool :=
  bank PrefixUnitRun.unitEmbedding
    (copied n a ordinal w ell saved output count)
    (SourceClauseUnitMachine.finished
      (SourceClauseUnitMachine.unitClause (ordinal*w+(n*a+ell)) sign)
      saved output count)

noncomputable def program (sign : Bool) := PrefixUnitRun.program sign
noncomputable def startControl := PrefixUnitRun.startControl

theorem address_initial (n a ordinal w ell : Nat)
    (saved output count : List Bool) :
    bank PrefixUnitRun.addressEmbedding
      (initial n a ordinal w ell saved output count)
      (SourceGenericUnitAddress.initial n a ordinal w ell) =
      initial n a ordinal w ell saved output count := by
  apply bank_eq_self
  intro k
  rfl

theorem address_final (n a ordinal w ell : Nat)
    (saved output count : List Bool) :
    bank PrefixUnitRun.addressEmbedding
      (initial n a ordinal w ell saved output count)
      (SourceGenericUnitAddress.finalBank n a ordinal w ell) =
      addressed n a ordinal w ell saved output count := by
  funext k
  cases k with
  | inl x => exact bank_at PrefixUnitRun.addressEmbedding _ _ x
  | inr x =>
      rw [bank_outside]
      · rfl
      · intro ⟨y,h⟩; cases h

theorem address_run (n a ordinal w ell : Nat)
    (saved output count : List Bool) :
    ∃ T ≤ SourceGenericUnitAddress.cost n a ordinal w ell,
      ((advance PrefixUnitRun.addressProgram)^[T])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)),
          ((false,((),none)),
            (false,(SourceLabelAddressMachine.counter.initial,none))),
          initial n a ordinal w ell saved output count⟩) =
        ⟨none,((false,((),none)),
          (false,(SourceLabelAddressMachine.counter.initial,none))),
          addressed n a ordinal w ell saved output count⟩ := by
  obtain ⟨T,hT,hr⟩ := SourceGenericUnitAddress.run n a ordinal w ell
  have hlift := BitMachineStackRun.run PrefixUnitRun.addressEmbedding
    (initial n a ordinal w ell saved output count)
    SourceGenericUnitAddress.program
    (⟨some (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)),
      ((false,((),none)),
        (false,(SourceLabelAddressMachine.counter.initial,none))),
      SourceGenericUnitAddress.initial n a ordinal w ell⟩) T
  rw [hr] at hlift
  simp only [stackCfg,address_initial,address_final] at hlift
  exact ⟨T,hT,by simpa only [PrefixUnitRun.addressProgram,
    SourceGenericUnitAddress.program] using hlift⟩

theorem addressed_source (n a ordinal w ell : Nat)
    (saved output count : List Bool) :
    addressed n a ordinal w ell saved output count PrefixUnitRun.source =
      (ordinal*w+(n*a+ell)).bits := by
  exact SourceGenericUnitAddress.final_binary n a ordinal w ell

theorem addressed_temp (n a ordinal w ell : Nat)
    (saved output count : List Bool) :
    addressed n a ordinal w ell saved output count PrefixUnitRun.temp =
      [] := by
  change SourceGenericUnitAddress.finalBank n a ordinal w ell
    SourceClauseGateSlotAddress.temp = []
  rw [SourceGenericUnitAddress.finalBank,bank_outside]
  · simp [SourceGenericUnitAddress.transferred,
      SourceClauseGateSlotAddress.transferred,
      BitMachineBroadcast.copied,SourceClauseGateSlotAddress.temp,
      SourceClauseGateSlotAddress.offsetSource]
  · intro ⟨x,h⟩; cases h

theorem copy_run (n a ordinal w ell : Nat)
    (saved output count : List Bool) :
    let p := ordinal*w+(n*a+ell)
    ((advance PrefixUnitRun.copyProgram)^[2*p.bits.length+3])
      (⟨some PrefixUnitRun.CopyLabel.scan,((),none),
        addressed n a ordinal w ell saved output count⟩) =
      ⟨none,((),none),copied n a ordinal w ell saved output count⟩ := by
  dsimp only
  let p := ordinal*w+(n*a+ell)
  have h := BitMachineBroadcast.broadcast_run PrefixUnitRun.copyProgram
    PrefixUnitRun.source PrefixUnitRun.temp
    (by simp [PrefixUnitRun.source,PrefixUnitRun.temp,
      PrefixUnitAddress.binarySource,
      SourceClauseGateSlotAddress.temp,
      SourceClauseGateSlotAddress.gateEmbedding])
    PrefixUnitRun.targets (by simp [PrefixUnitRun.targets])
    (by simp [PrefixUnitRun.source,PrefixUnitRun.targets,
      PrefixUnitRun.target])
    (by simp [PrefixUnitRun.temp,PrefixUnitRun.targets,
      PrefixUnitRun.target])
    .scan .restore .finish rfl rfl () none p.bits
    (addressed n a ordinal w ell saved output count)
    (addressed_source n a ordinal w ell saved output count)
    (addressed_temp n a ordinal w ell saved output count)
  rw [show 2*p.bits.length+3 = (2*p.bits.length+2)+1 by omega,
    Function.iterate_succ_apply']
  change advance PrefixUnitRun.copyProgram
    (BitMachineBroadcast.run PrefixUnitRun.copyProgram
      (2*p.bits.length+2)
      (⟨some .scan,((),none),
        addressed n a ordinal w ell saved output count⟩)) = _
  rw [h]
  simp [advance,TM2.step,PrefixUnitRun.copyProgram,copied,p]

theorem unit_ready (n a ordinal w ell : Nat)
    (saved output count : List Bool) :
    let p := ordinal*w+(n*a+ell)
    bank PrefixUnitRun.unitEmbedding
      (copied n a ordinal w ell saved output count)
      (SourceClauseUnitMachine.initial p.bits saved output count) =
      copied n a ordinal w ell saved output count := by
  dsimp only
  apply bank_eq_self
  intro k
  cases k with
  | inl x =>
      fin_cases x <;>
        simp [copied,BitMachineBroadcast.copied,
          PrefixUnitRun.unitEmbedding,SourceClauseUnitMachine.source,
          PrefixUnitRun.source,PrefixUnitRun.temp,PrefixUnitRun.targets,
          PrefixUnitRun.target,addressed,SourceClauseUnitMachine.initial]
  | inr x =>
      simp [copied,BitMachineBroadcast.copied,
        PrefixUnitRun.unitEmbedding,SourceClauseUnitMachine.source,
        PrefixUnitRun.source,PrefixUnitRun.temp,PrefixUnitRun.targets,
        PrefixUnitRun.target,addressed,SourceClauseUnitMachine.initial]

theorem unit_run (n a ordinal w ell : Nat) (sign : Bool)
    (saved output count : List Bool) :
    let p := ordinal*w+(n*a+ell)
    ∃ T ≤ 5*p.bits.length+13,
      ((advance (PrefixUnitRun.unitProgram sign))^[T])
        (⟨some (BitMachineRawSequence.leftLabel
          SourceClauseUnitMachine.CopyLabel.scan),
          (((),none),(none,())),
          copied n a ordinal w ell saved output count⟩) =
        ⟨none,(((),none),(none,())),
          finished n a ordinal w ell sign saved output count⟩ := by
  dsimp only
  let p := ordinal*w+(n*a+ell)
  obtain ⟨T,hT,hr⟩ := SourceClauseUnitMachine.unit_run p sign
    saved output count
  have hlift := BitMachineStackRun.run PrefixUnitRun.unitEmbedding
    (copied n a ordinal w ell saved output count)
    (SourceClauseUnitMachine.program sign)
    (⟨some (BitMachineRawSequence.leftLabel
      SourceClauseUnitMachine.CopyLabel.scan),
      (((),none),(none,())),
      SourceClauseUnitMachine.initial p.bits saved output count⟩) T
  rw [hr] at hlift
  simp only [stackCfg] at hlift
  rw [unit_ready] at hlift
  exact ⟨T,hT,by simpa only [PrefixUnitRun.unitProgram,finished]
    using hlift⟩

noncomputable def cost (n a ordinal w ell : Nat) : Nat :=
  let p := ordinal*w+(n*a+ell)
  SourceGenericUnitAddress.cost n a ordinal w ell +
    (2*p.bits.length+3)+1+(5*p.bits.length+13)+1

theorem run (n a ordinal w ell : Nat) (sign : Bool)
    (saved output count : List Bool) :
    ∃ T ≤ cost n a ordinal w ell,
      ((advance (program sign))^[T])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                MatrixAddressMachine.Label.outer)))),
          startControl,
          initial n a ordinal w ell saved output count⟩) =
        ⟨none,startControl,
          finished n a ordinal w ell sign saved output count⟩ := by
  let p := ordinal*w+(n*a+ell)
  obtain ⟨ta,hta,ha⟩ := address_run n a ordinal w ell
    saved output count
  have hc := copy_run n a ordinal w ell saved output count
  obtain ⟨tab,htab,hab⟩ := BitMachineRawSequence.runs
    PrefixUnitRun.addressProgram PrefixUnitRun.copyProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer))
    PrefixUnitRun.CopyLabel.scan
    ((false,((),none)),
      (false,(SourceLabelAddressMachine.counter.initial,none)))
    ((false,((),none)),
      (false,(SourceLabelAddressMachine.counter.initial,none)))
    ((),none) ((),none)
    (initial n a ordinal w ell saved output count)
    (addressed n a ordinal w ell saved output count)
    (copied n a ordinal w ell saved output count)
    ta (2*p.bits.length+3) ha hc
  obtain ⟨tu,htu,hu⟩ := unit_run n a ordinal w ell sign
    saved output count
  obtain ⟨T,hT,hr⟩ := BitMachineRawSequence.runs
    (BitMachineRawSequence.program PrefixUnitRun.addressProgram
      PrefixUnitRun.copyProgram PrefixUnitRun.CopyLabel.scan
      ((false,((),none)),
        (false,(SourceLabelAddressMachine.counter.initial,none)))
      ((),none))
    (PrefixUnitRun.unitProgram sign)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)))
    (BitMachineRawSequence.leftLabel SourceClauseUnitMachine.CopyLabel.scan)
    (((false,((),none)),
        (false,(SourceLabelAddressMachine.counter.initial,none))),
      ((),none))
    (((false,((),none)),
        (false,(SourceLabelAddressMachine.counter.initial,none))),
      ((),none))
    (((),none),(none,())) (((),none),(none,()))
    (initial n a ordinal w ell saved output count)
    (copied n a ordinal w ell saved output count)
    (finished n a ordinal w ell sign saved output count)
    tab tu hab hu
  exact ⟨T,by dsimp [cost,p] at *; omega,
    by simpa only [program,startControl,PrefixUnitRun.program,
      PrefixUnitRun.startControl] using hr⟩

theorem final_saved (n a ordinal w ell : Nat) (sign : Bool)
    (saved output count : List Bool) :
    finished n a ordinal w ell sign saved output count
      PrefixUnitRun.savedKey =
      (EncodedCNF.encodeClause (SourceClauseUnitMachine.unitClause
        (ordinal*w+(n*a+ell)) sign)).reverse ++ saved := by
  rw [finished,show PrefixUnitRun.savedKey =
    PrefixUnitRun.unitEmbedding (.inr (.inl 3)) by rfl,bank_at]
  rfl

theorem final_count (n a ordinal w ell : Nat) (sign : Bool)
    (saved output count : List Bool) :
    finished n a ordinal w ell sign saved output count
      PrefixUnitRun.countKey = true :: count := by
  rw [finished,show PrefixUnitRun.countKey =
    PrefixUnitRun.unitEmbedding (.inr (.inr ())) by rfl,bank_at]
  rfl

theorem final_output (n a ordinal w ell : Nat) (sign : Bool)
    (saved output count : List Bool) :
    finished n a ordinal w ell sign saved output count
      PrefixUnitRun.outputKey = output := by
  rw [finished,show PrefixUnitRun.outputKey =
    PrefixUnitRun.unitEmbedding (.inr (.inl 4)) by rfl,bank_at]
  rfl

#print axioms address_run
#print axioms run

end EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.UnitRun
