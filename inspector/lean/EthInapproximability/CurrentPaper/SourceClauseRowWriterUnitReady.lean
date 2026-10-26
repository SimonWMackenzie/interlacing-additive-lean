import EthInapproximability.CurrentPaper.SourceClauseRowWriterStageReady
import EthInapproximability.CurrentPaper.SourceClauseRowWriterInitial

/-! Full-bank handoff from the physical unary operand staging to the
existing unit-clause writer. The parsed row and shared reversed-clause
accumulator are retained; no prepared clause or query is supplied. -/

namespace EthInapproximability.CurrentPaper.SourceClauseRowWriterUnitReady

open Turing BitMachineEncoding BitMachineStackEmbedding
open scoped Classical

private theorem other_empty {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k w ell : ℕ) (saved output count : List Bool)
    (x : SourceClauseRowWriterCore.UnitBank q)
    (hcore : x ∉ Set.range SourceClauseRowWriterCore.unitCore)
    (hfixed : ∀ j : Fin 6,
      SourceClauseRowWriterOperands.unitConstants j ≠
        SourceClauseRowWriterOperands.unitCell x)
    (hvertex : SourceClauseRowWriterOperands.unitCell x ∉
      SourceClauseRowWriterOperands.unitVertexTargets)
    (hrow : SourceClauseRowWriterOperands.unitCell x ∉
      SourceClauseRowWriterOperands.unitRowTargets)
    (hinitial : SourceClauseRowUnitFrame.initial row n r a k w ell
      saved output count x = []) :
    SourceClauseRowWriterStage.unitFinal n r a k w ell
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterOperands.unitCell x) =
    SourceClauseRowUnitFrame.initial row n r a k w ell
      saved output count x := by
  rw [SourceClauseRowWriterStageReady.unit_final_other n r a k w ell
    (SourceClauseRowWriterBlank.bank row n r saved output count)
    (SourceClauseRowWriterOperands.unitCell x) hfixed hvertex hrow
    (by simp [SourceClauseRowWriterOperands.unitCell,
      SourceClauseRowWriterOperands.vertex])
    (by simp [SourceClauseRowWriterOperands.unitCell,
      SourceClauseRowWriterOperands.rowIndex])
    (by simp [SourceClauseRowWriterOperands.unitCell,
      SourceClauseRowWriterOperands.scratch])]
  exact (SourceClauseRowWriterBlank.unit_scratch_empty
    row n r saved output count x hcore).trans hinitial.symm

theorem unit_initial_bank {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k w ell : ℕ) (saved output count : List Bool)
    (x : SourceClauseRowWriterCore.UnitBank q) :
    SourceClauseRowWriterStage.unitFinal n r a k w ell
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterOperands.unitCell x) =
    SourceClauseRowUnitFrame.initial row n r a k w ell
      saved output count x := by
  cases x with
  | inl j =>
      simpa only [SourceClauseRowWriterCore.unitCore,
        SourceClauseRowWriterCore.unitCoreCell] using
        SourceClauseRowWriterInitial.unit_core_initial row n r a k w ell
          saved output count (.inl j)
  | inr j =>
      fin_cases j <;> first
        | exact SourceClauseRowWriterInitial.unit_core_initial
            row n r a k w ell saved output count (.inr 0)
        | exact SourceClauseRowWriterInitial.unit_core_initial
            row n r a k w ell saved output count (.inr 1)
        | exact SourceClauseRowWriterInitial.unit_core_initial
            row n r a k w ell saved output count (.inr 2)
        | simpa using SourceClauseRowWriterStageReady.unit_variable_inputs
            row n r a k w ell saved output count 0
        | simpa using SourceClauseRowWriterStageReady.unit_variable_inputs
            row n r a k w ell saved output count 1
        | simpa using SourceClauseRowWriterStageReady.unit_variable_inputs
            row n r a k w ell saved output count 2
        | simpa using SourceClauseRowWriterStageReady.unit_fixed_inputs
            row n r a k w ell saved output count 0
        | simpa using SourceClauseRowWriterStageReady.unit_fixed_inputs
            row n r a k w ell saved output count 1
        | simpa using SourceClauseRowWriterStageReady.unit_fixed_inputs
            row n r a k w ell saved output count 2
        | simpa using SourceClauseRowWriterStageReady.unit_fixed_inputs
            row n r a k w ell saved output count 3
        | simpa using SourceClauseRowWriterStageReady.unit_fixed_inputs
            row n r a k w ell saved output count 4
        | simpa using SourceClauseRowWriterStageReady.unit_fixed_inputs
            row n r a k w ell saved output count 5
        | (apply other_empty row n r a k w ell saved output count
           · rintro ⟨c, hc⟩
             cases c with
             | inl y => cases hc
             | inr i => fin_cases i <;> cases hc
           · intro i hi
             rw [SourceClauseRowWriterStageReady.unit_constant_cell] at hi
             have hh := SourceClauseRowWriterCore.unitEmbedding.injective
               (Sum.inl.inj hi)
             fin_cases i <;> cases hh
           · simp [SourceClauseRowWriterStageReady.unit_vertex_targets,
               SourceClauseRowWriterStageReady.unitVariableLocal,
               SourceClauseRowWriterOperands.unitCell,
               SourceClauseRowWriterOperands.unitAddress,
               SourceClauseRowUnitMachine.addressEmbedding,
               SourceClauseRowUnitAddress.slotEmbedding,
               SourceClauseRowUnitAddress.offsetEmbedding]
           · simp [SourceClauseRowWriterStageReady.unit_row_targets,
               SourceClauseRowWriterStageReady.unitVariableLocal,
               SourceClauseRowWriterOperands.unitCell,
               SourceClauseRowWriterOperands.unitAddress,
               SourceClauseRowUnitMachine.addressEmbedding,
               SourceClauseRowUnitAddress.slotEmbedding,
               SourceClauseRowUnitAddress.offsetEmbedding]
           · rfl)

noncomputable def unitSlots (q : ℕ) : SourceClauseRowWriterCore.UnitBank q ↪
    SourceClauseRowWriterOperands.Stack q where
  toFun := SourceClauseRowWriterOperands.unitCell
  inj' := by
    intro x y h
    exact SourceClauseRowWriterCore.unitEmbedding.injective (Sum.inl.inj h)

noncomputable def unitProgram (q : ℕ) (sign : Bool) :=
  fun l => stackStmt (unitSlots q) (SourceClauseRowUnitFrame.program q sign l)

noncomputable def unitFinalBank {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k w ell : ℕ) (sign : Bool)
    (saved output count : List Bool) :
    SourceClauseRowWriterOperands.Stack q → List Bool :=
  bank (unitSlots q)
    (SourceClauseRowWriterStage.unitFinal n r a k w ell
      (SourceClauseRowWriterBlank.bank row n r saved output count))
    (SourceClauseRowUnitFrame.finalBank row n r a k w ell sign
      saved output count)

private theorem stage_eq_unit_input {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k w ell : ℕ) (saved output count : List Bool) :
    bank (unitSlots q)
      (SourceClauseRowWriterStage.unitFinal n r a k w ell
        (SourceClauseRowWriterBlank.bank row n r saved output count))
      (SourceClauseRowUnitFrame.initial row n r a k w ell
        saved output count) =
      SourceClauseRowWriterStage.unitFinal n r a k w ell
        (SourceClauseRowWriterBlank.bank row n r saved output count) := by
  apply bank_eq_self
  intro x
  exact (unit_initial_bank row n r a k w ell saved output count x).symm

theorem unit_machine_run {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k w ell : ℕ) (sign : Bool)
    (saved output count : List Bool) :
    ∃ t ≤ SourceClauseRowUnitMachine.cost n r a q k w ell,
      ((advance (unitProgram q sign))^[t])
        (⟨some SourceClauseRowUnitMachine.startLabel,
          SourceClauseRowUnitMachine.startControl,
          SourceClauseRowWriterStage.unitFinal n r a k w ell
            (SourceClauseRowWriterBlank.bank row n r saved output count)⟩) =
        ⟨none, SourceClauseRowUnitMachine.startControl,
          unitFinalBank row n r a k w ell sign saved output count⟩ := by
  obtain ⟨t, ht, hr⟩ := SourceClauseRowUnitFrame.run
    row n r a k w ell sign saved output count
  have h := BitMachineStackRun.run (unitSlots q)
    (SourceClauseRowWriterStage.unitFinal n r a k w ell
      (SourceClauseRowWriterBlank.bank row n r saved output count))
    (SourceClauseRowUnitFrame.program q sign)
    (⟨some SourceClauseRowUnitMachine.startLabel,
      SourceClauseRowUnitMachine.startControl,
      SourceClauseRowUnitFrame.initial row n r a k w ell
        saved output count⟩) t
  rw [hr] at h
  refine ⟨t, ht, ?_⟩
  simpa only [unitProgram, unitFinalBank, stackCfg,
    stage_eq_unit_input] using h

def stageCost (q n r a k w ell : ℕ) : ℕ :=
  ((2 * n + 3) + (2 * r + 3) + 1) +
    (SourceClauseFixedBatch.costPrefix
      (SourceClauseRowWriterOperands.unitSizes a q k w ell) 6 + 1) + 1

def stageControl : SourceClauseRowWriterStage.FanoutControl × Unit :=
  ((((), none), ((), none)), ())

noncomputable def program {q : ℕ} (a k w ell : ℕ) (sign : Bool) :=
  BitMachineRawSequence.program
    (SourceClauseRowWriterStage.unitProgram a k w ell)
    (unitProgram q sign) SourceClauseRowUnitMachine.startLabel
    stageControl
    SourceClauseRowUnitMachine.startControl

theorem run {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k w ell : ℕ) (sign : Bool)
    (saved output count : List Bool) :
    ∃ t ≤ stageCost q n r a k w ell +
        SourceClauseRowUnitMachine.cost n r a q k w ell + 1,
      ((advance (program a k w ell sign))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              SourceClausePreservingBroadcast.Label.scan))),
          (stageControl, SourceClauseRowUnitMachine.startControl),
          SourceClauseRowWriterBlank.bank row n r saved output count⟩) =
        ⟨none,
          (stageControl, SourceClauseRowUnitMachine.startControl),
          unitFinalBank row n r a k w ell sign
            saved output count⟩ := by
  let S := SourceClauseRowWriterBlank.bank row n r saved output count
  let T := SourceClauseRowWriterStage.unitFinal n r a k w ell S
  let U := unitFinalBank row n r a k w ell sign saved output count
  obtain ⟨ts, hts, hs⟩ := SourceClauseRowWriterStage.unit_run
    n r a k w ell S
    (SourceClauseRowWriterBlank.vertex row n r saved output count)
    (SourceClauseRowWriterBlank.row_index row n r saved output count)
    (SourceClauseRowWriterBlank.scratch row n r saved output count)
  obtain ⟨tu, htu, hu⟩ := unit_machine_run
    row n r a k w ell sign saved output count
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (SourceClauseRowWriterStage.unitProgram a k w ell)
    (unitProgram q sign)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        SourceClausePreservingBroadcast.Label.scan))
    SourceClauseRowUnitMachine.startLabel
    stageControl stageControl
    SourceClauseRowUnitMachine.startControl
    SourceClauseRowUnitMachine.startControl
    S T U ts tu hs hu
  refine ⟨t, ?_, ?_⟩
  · dsimp only [stageCost] at ⊢
    omega
  · simpa only [program, S, T, U] using hr

theorem final_row {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k w ell : ℕ) (sign : Bool)
    (saved output count : List Bool)
    (x : SourceCSPRowQueryFrame.Stack q) :
    unitFinalBank row n r a k w ell sign saved output count
      (SourceClauseRowWriterOperands.unitCell (.inl x)) = row x := by
  rw [unitFinalBank, ← show unitSlots q (.inl x) =
      SourceClauseRowWriterOperands.unitCell (.inl x) from rfl,
    bank_at]
  exact SourceClauseRowUnitFrame.final_row
    row n r a k w ell sign saved output count x

theorem final_saved {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k w ell : ℕ) (sign : Bool)
    (saved output count : List Bool) :
    unitFinalBank row n r a k w ell sign saved output count
      (SourceClauseRowWriterOperands.unitCell
        (.inr SourceClauseRowUnitMachine.savedSlot)) =
      (EncodedCNF.encodeClause
        (SourceClauseUnitMachine.unitClause
          (SourceClauseRowUnitMachine.p n r a q k w ell) sign)).reverse ++
        saved := by
  rw [unitFinalBank, ← show unitSlots q
      (.inr SourceClauseRowUnitMachine.savedSlot) =
        SourceClauseRowWriterOperands.unitCell
          (.inr SourceClauseRowUnitMachine.savedSlot) from rfl,
    bank_at]
  exact SourceClauseRowUnitFrame.final_saved
    row n r a k w ell sign saved output count

theorem final_output {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k w ell : ℕ) (sign : Bool)
    (saved output count : List Bool) :
    unitFinalBank row n r a k w ell sign saved output count
      (SourceClauseRowWriterOperands.unitCell
        (.inr SourceClauseRowUnitMachine.outputSlot)) = output := by
  rw [unitFinalBank, ← show unitSlots q
      (.inr SourceClauseRowUnitMachine.outputSlot) =
        SourceClauseRowWriterOperands.unitCell
          (.inr SourceClauseRowUnitMachine.outputSlot) from rfl,
    bank_at]
  exact SourceClauseRowUnitFrame.final_output
    row n r a k w ell sign saved output count

theorem final_count {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k w ell : ℕ) (sign : Bool)
    (saved output count : List Bool) :
    unitFinalBank row n r a k w ell sign saved output count
      (SourceClauseRowWriterOperands.unitCell
        (.inr SourceClauseRowUnitMachine.countSlot)) = true :: count := by
  rw [unitFinalBank, ← show unitSlots q
      (.inr SourceClauseRowUnitMachine.countSlot) =
        SourceClauseRowWriterOperands.unitCell
          (.inr SourceClauseRowUnitMachine.countSlot) from rfl,
    bank_at]
  exact SourceClauseRowUnitFrame.final_count
    row n r a k w ell sign saved output count

private theorem stage_outer_fixed {q : ℕ}
    (n r a k w ell : ℕ)
    (S : SourceClauseRowWriterOperands.Stack q → List Bool)
    (i : Fin 3) :
    SourceClauseRowWriterStage.unitFinal n r a k w ell S (.inr i) =
      SourceClauseRowWriterFanout.afterRow
        SourceClauseRowWriterOperands.unitVertexTargets
        SourceClauseRowWriterOperands.unitRowTargets n r S (.inr i) := by
  rw [SourceClauseRowWriterStage.unitFinal,
    SourceClauseRowWriterOperands.unitFixedBank]
  apply SourceClauseFixedBatch.result_outside
  intro j
  fin_cases j <;> simp [SourceClauseRowWriterOperands.unitConstants,
    SourceClauseRowWriterOperands.unitCell]

theorem final_vertex {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k w ell : ℕ) (sign : Bool)
    (saved output count : List Bool) :
    unitFinalBank row n r a k w ell sign saved output count
      SourceClauseRowWriterOperands.vertex = List.replicate n true := by
  rw [unitFinalBank, bank_outside]
  · rw [SourceClauseRowWriterOperands.vertex, stage_outer_fixed,
      SourceClauseRowWriterFanout.afterRow]
    rw [SourceClausePreservingBroadcast.other_preserved]
    · exact SourceClausePreservingBroadcast.source_restored _ _ _
        (by simp [SourceClauseRowWriterOperands.vertex,
          SourceClauseRowWriterOperands.scratch]) _ _
    · simp [SourceClauseRowWriterOperands.rowIndex]
    · simp [SourceClauseRowWriterOperands.scratch]
    · exact (SourceClauseRowWriterFanout.unit_wellformed (q := q)).2.2.2.2.2.1
  · rintro ⟨x, hx⟩
    cases hx

theorem final_row_index {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k w ell : ℕ) (sign : Bool)
    (saved output count : List Bool) :
    unitFinalBank row n r a k w ell sign saved output count
      SourceClauseRowWriterOperands.rowIndex = List.replicate r true := by
  rw [unitFinalBank, bank_outside]
  · rw [SourceClauseRowWriterOperands.rowIndex, stage_outer_fixed,
      SourceClauseRowWriterFanout.afterRow]
    exact SourceClausePreservingBroadcast.source_restored _ _ _
      (by simp [SourceClauseRowWriterOperands.rowIndex,
        SourceClauseRowWriterOperands.scratch]) _ _
  · rintro ⟨x, hx⟩
    cases hx

theorem final_scratch {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k w ell : ℕ) (sign : Bool)
    (saved output count : List Bool) :
    unitFinalBank row n r a k w ell sign saved output count
      SourceClauseRowWriterOperands.scratch = [] := by
  rw [unitFinalBank, bank_outside]
  · rw [SourceClauseRowWriterOperands.scratch, stage_outer_fixed,
      SourceClauseRowWriterFanout.afterRow]
    exact SourceClausePreservingBroadcast.temp_empty _ _ _ _ _
  · rintro ⟨x, hx⟩
    cases hx

end EthInapproximability.CurrentPaper.SourceClauseRowWriterUnitReady
