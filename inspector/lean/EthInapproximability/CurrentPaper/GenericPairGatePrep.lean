import EthInapproximability.CurrentPaper.GenericPairGateBase

namespace EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.PairGatePrep

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceBooleanPrefix
open scoped Classical

abbrev Stack := PairUnitLift.Stack

noncomputable def prepared {n a : Nat} (v : Fin n) (bit : Fin a)
    (w ordinal : Nat) (saved output count : List Bool) :
    Stack → List Bool :=
  bank SourceBooleanPrefix.PairGateBase.coreEmbedding
    (SourceBooleanPrefix.PairGateBase.ordinalForeign ordinal)
    (GateReady.prepared v bit w saved output count)

noncomputable def cleared {n a : Nat} (v : Fin n) (bit : Fin a)
    (w ordinal : Nat) (saved output count : List Bool) :
    Stack → List Bool :=
  BitMachineClearBank.cleared PairGatePatch.target
    (prepared v bit w ordinal saved output count)

noncomputable def copied {n a : Nat} (v : Fin n) (bit : Fin a)
    (w ordinal : Nat) (saved output count : List Bool) :
    Stack → List Bool :=
  Function.update (cleared v bit w ordinal saved output count)
    PairGatePatch.gateIndex (List.replicate ordinal true)

noncomputable def ready {n a : Nat} (v : Fin n) (bit : Fin a)
    (w ordinal position : Nat) (saved output count : List Bool) :
    Stack → List Bool :=
  Function.update (copied v bit w ordinal saved output count)
    PairGatePatch.gateOffset (List.replicate position true)

theorem prepared_index {n a : Nat} (v : Fin n) (bit : Fin a)
    (w ordinal : Nat) (saved output count : List Bool) :
    prepared v bit w ordinal saved output count
      PairGatePatch.gateIndex = List.replicate v.val true := by
  rw [prepared,PairGatePatch.gateIndex]
  change bank SourceBooleanPrefix.PairGateBase.coreEmbedding
    (SourceBooleanPrefix.PairGateBase.ordinalForeign ordinal)
    (GateReady.prepared v bit w saved output count)
    (SourceBooleanPrefix.PairGateBase.coreEmbedding
      PrefixGateOperands.gateIndex) = _
  rw [bank_at]
  exact GateReady.prepared_target v bit w saved output count _
    (Or.inr rfl)

theorem prepared_offset {n a : Nat} (v : Fin n) (bit : Fin a)
    (w ordinal : Nat) (saved output count : List Bool) :
    prepared v bit w ordinal saved output count
      PairGatePatch.gateOffset = List.replicate bit.val true := by
  rw [prepared,PairGatePatch.gateOffset]
  change bank SourceBooleanPrefix.PairGateBase.coreEmbedding
    (SourceBooleanPrefix.PairGateBase.ordinalForeign ordinal)
    (GateReady.prepared v bit w saved output count)
    (SourceBooleanPrefix.PairGateBase.coreEmbedding
      PrefixGateOperands.gateOffset) = _
  rw [bank_at]
  simpa [PrefixGateOperands.gateOffset,
    PrefixGateOperands.constantTarget,GateOperands.constantSize] using
    GateReady.prepared_constant v bit w saved output count 3

theorem prepared_scratch {n a : Nat} (v : Fin n) (bit : Fin a)
    (w ordinal : Nat) (saved output count : List Bool) :
    prepared v bit w ordinal saved output count
      PairGatePatch.scratch = [] := by
  rw [prepared,PairGatePatch.scratch]
  change bank SourceBooleanPrefix.PairGateBase.coreEmbedding
    (SourceBooleanPrefix.PairGateBase.ordinalForeign ordinal)
    (GateReady.prepared v bit w saved output count)
    (SourceBooleanPrefix.PairGateBase.coreEmbedding
      PrefixGateOperands.temp) = _
  rw [bank_at]
  have h := GateReady.gate_ready v bit w saved output count
    PrefixGateOperands.tempLocal
  rw [GateReady.raw_initial_temp] at h
  exact h

theorem prepared_ordinal {n a : Nat} (v : Fin n) (bit : Fin a)
    (w ordinal : Nat) (saved output count : List Bool) :
    prepared v bit w ordinal saved output count
      PairGatePatch.ordinal = List.replicate ordinal true := by
  rw [prepared,PairGatePatch.ordinal,bank_outside]
  · rfl
  · rintro ⟨k,hk⟩; cases hk

theorem cleared_index {n a : Nat} (v : Fin n) (bit : Fin a)
    (w ordinal : Nat) (saved output count : List Bool) :
    cleared v bit w ordinal saved output count
      PairGatePatch.gateIndex = [] := by
  simpa only [cleared,PairGatePatch.target] using
    BitMachineClearBank.cleared_bank PairGatePatch.target
      (prepared v bit w ordinal saved output count) 0

theorem cleared_offset {n a : Nat} (v : Fin n) (bit : Fin a)
    (w ordinal : Nat) (saved output count : List Bool) :
    cleared v bit w ordinal saved output count
      PairGatePatch.gateOffset = [] := by
  simpa only [cleared,PairGatePatch.target] using
    BitMachineClearBank.cleared_bank PairGatePatch.target
      (prepared v bit w ordinal saved output count) 1

theorem cleared_ordinal {n a : Nat} (v : Fin n) (bit : Fin a)
    (w ordinal : Nat) (saved output count : List Bool) :
    cleared v bit w ordinal saved output count
      PairGatePatch.ordinal = List.replicate ordinal true := by
  have hf : ∀ i : Fin 2,
      PairGatePatch.target i ≠ PairGatePatch.ordinal := by
    intro i
    fin_cases i
    · exact PairGatePatch.ordinal_ne_index.symm
    · exact PairGatePatch.ordinal_ne_offset.symm
  rw [cleared,BitMachineClearBank.cleared_foreign
    PairGatePatch.target _ PairGatePatch.ordinal hf]
  exact prepared_ordinal v bit w ordinal saved output count

theorem cleared_scratch {n a : Nat} (v : Fin n) (bit : Fin a)
    (w ordinal : Nat) (saved output count : List Bool) :
    cleared v bit w ordinal saved output count
      PairGatePatch.scratch = [] := by
  have hf : ∀ i : Fin 2,
      PairGatePatch.target i ≠ PairGatePatch.scratch := by
    intro i
    fin_cases i
    · exact PairGatePatch.scratch_ne_index.symm
    · exact PairGatePatch.scratch_ne_offset.symm
  rw [cleared,BitMachineClearBank.cleared_foreign
    PairGatePatch.target _ PairGatePatch.scratch hf]
  exact prepared_scratch v bit w ordinal saved output count

theorem copied_offset {n a : Nat} (v : Fin n) (bit : Fin a)
    (w ordinal : Nat) (saved output count : List Bool) :
    copied v bit w ordinal saved output count
      PairGatePatch.gateOffset = [] := by
  rw [copied,Function.update_of_ne PairGatePatch.index_ne_offset.symm]
  exact cleared_offset v bit w ordinal saved output count

noncomputable def phase1 (a : Nat) (bit : Fin a) (w : Nat) :=
  BitMachineRawSequence.program (PairGateBase.preparationProgram a bit w)
    PairGatePatch.clearProgram 0 ((),((),none)) ((),none)

noncomputable def phase2 (a : Nat) (bit : Fin a) (w : Nat) :=
  BitMachineRawSequence.program (phase1 a bit w)
    PairGatePatch.copyProgram .scan
    (((),((),none)),((),none)) none

noncomputable def program (a : Nat) (bit : Fin a) (ell : Fin 2)
    (w : Nat) :=
  BitMachineRawSequence.program (phase2 a bit w)
    (PairGatePatch.offsetProgram ell)
    (SourceClauseFixedBatch.labelAt (PairGatePatch.offsetSize ell) 0)
    ((((),((),none)),((),none)),none) ()

theorem run {n a : Nat} (v : Fin n) (bit : Fin a) (ell : Fin 2)
    (w ordinal : Nat) (saved output count : List Bool) :
    ∃ t ≤ GateOperands.cost a bit.val w (List.replicate v.val true) +
      (v.val + bit.val + 4) + (2*ordinal+2) +
      (PairGatePatch.offsetSize ell 0 + 2) + 3,
      ((advance (program a bit ell w))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (SourceClauseFixedBatch.labelAt
                  (GateOperands.constantSize a bit.val w) 0))))),
          (((((),((),none)),((),none)),none),()),
          PairUnitLift.pairBank n v.val ordinal saved output count⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,(((((),((),none)),((),none)),none),()),
          ready v bit w ordinal ell.val saved output count⟩ := by
  obtain ⟨p,hp,hprep⟩ := PairGateBase.preparation_run v bit ordinal w
    saved output count
  let B0 := prepared v bit w ordinal saved output count
  let B1 := cleared v bit w ordinal saved output count
  let B2 := copied v bit w ordinal saved output count
  let B3 := ready v bit w ordinal ell.val saved output count
  have hclear := PairGatePatch.clear_run B0
  have hcopy := PairGatePatch.copy_run B1
    (cleared_index v bit w ordinal saved output count)
    (cleared_scratch v bit w ordinal saved output count)
  have hcopy' : ((advance PairGatePatch.copyProgram)^[2*ordinal+2])
      (⟨some .scan,none,B1⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none,none,B2⟩ := by
    have hor : B1 PairGatePatch.ordinal =
        List.replicate ordinal true :=
      cleared_ordinal v bit w ordinal saved output count
    rw [hor] at hcopy
    simpa only [List.length_replicate,B2,copied] using hcopy
  have hoffset := PairGatePatch.offset_run ell B2
    (copied_offset v bit w ordinal saved output count)
  have hclear' : ((advance PairGatePatch.clearProgram)^[
      PairGatePatch.clearTime B0])
      (⟨some 0,((),none),B0⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none,((),none),B1⟩ := by simpa [B1,cleared] using hclear
  have hoffset' : ((advance (PairGatePatch.offsetProgram ell))^[
      SourceClauseFixedBatch.costPrefix (PairGatePatch.offsetSize ell) 1 + 1])
      (⟨some (SourceClauseFixedBatch.labelAt
        (PairGatePatch.offsetSize ell) 0),(),B2⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none,(),B3⟩ := by simpa [B3,ready] using hoffset
  obtain ⟨t1,ht1,h1⟩ := BitMachineRawSequence.runs
    (PairGateBase.preparationProgram a bit w)
    PairGatePatch.clearProgram
    (BitMachineRawSequence.leftLabel
      (SourceClauseFixedBatch.labelAt
        (GateOperands.constantSize a bit.val w) 0))
    0 ((),((),none)) ((),((),none)) ((),none) ((),none)
    (PairUnitLift.pairBank n v.val ordinal saved output count)
    B0 B1 p (PairGatePatch.clearTime B0) hprep hclear'
  obtain ⟨t2,ht2,h2⟩ := BitMachineRawSequence.runs
    (phase1 a bit w) PairGatePatch.copyProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (SourceClauseFixedBatch.labelAt
          (GateOperands.constantSize a bit.val w) 0)))
    .scan (((),((),none)),((),none))
    (((),((),none)),((),none)) none none
    (PairUnitLift.pairBank n v.val ordinal saved output count)
    B1 B2 t1 (2*ordinal+2) h1 hcopy'
  obtain ⟨t3,ht3,h3⟩ := BitMachineRawSequence.runs
    (phase2 a bit w) (PairGatePatch.offsetProgram ell)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (SourceClauseFixedBatch.labelAt
            (GateOperands.constantSize a bit.val w) 0))))
    (SourceClauseFixedBatch.labelAt (PairGatePatch.offsetSize ell) 0)
    ((((),((),none)),((),none)),none)
    ((((),((),none)),((),none)),none) () ()
    (PairUnitLift.pairBank n v.val ordinal saved output count)
    B2 B3 t2
    (SourceClauseFixedBatch.costPrefix (PairGatePatch.offsetSize ell) 1+1)
    h2 hoffset'
  refine ⟨t3,?_,?_⟩
  · have htime : PairGatePatch.clearTime B0 =
        v.val + bit.val + 4 := by
      change (B0 PairGatePatch.gateIndex).length +
        (B0 PairGatePatch.gateOffset).length + 4 = _
      have hi : B0 PairGatePatch.gateIndex =
          List.replicate v.val true :=
        prepared_index v bit w ordinal saved output count
      have ho : B0 PairGatePatch.gateOffset =
          List.replicate bit.val true :=
        prepared_offset v bit w ordinal saved output count
      rw [hi,ho]
      simp
    have hc : SourceClauseFixedBatch.costPrefix
        (PairGatePatch.offsetSize ell) 1 =
        PairGatePatch.offsetSize ell 0 + 1 := by
      simp [SourceClauseFixedBatch.costPrefix]
    rw [hc] at ht3
    omega
  · simpa only [program,B3] using h3

#print axioms prepared_index
#print axioms run

end EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.PairGatePrep
