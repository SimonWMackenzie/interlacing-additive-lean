import EthInapproximability.CurrentPaper.SourceClausePairGatePatch

namespace EthInapproximability.CurrentPaper.SourceBooleanPrefix.PairGatePrep

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceBooleanEncoding
open scoped Classical

abbrev Stack := PairGateBase.Stack

noncomputable def prepared {n q : Nat} (v : Fin n) (bit : Fin 2)
    (ordinal : Nat) (saved output count : List Bool) :
    Stack → List Bool :=
  bank PairGateBase.coreEmbedding (PairGateBase.ordinalForeign ordinal)
    (PrefixGateReady.prepared (q := q) v bit saved output count)

noncomputable def cleared {n q : Nat} (v : Fin n) (bit : Fin 2)
    (ordinal : Nat) (saved output count : List Bool) :
    Stack → List Bool :=
  BitMachineClearBank.cleared PairGatePatch.target
    (prepared (q := q) v bit ordinal saved output count)

noncomputable def copied {n q : Nat} (v : Fin n) (bit : Fin 2)
    (ordinal : Nat) (saved output count : List Bool) :
    Stack → List Bool :=
  Function.update (cleared (q := q) v bit ordinal saved output count)
    PairGatePatch.gateIndex (List.replicate ordinal true)

noncomputable def ready {n q : Nat} (v : Fin n) (bit ell : Fin 2)
    (ordinal : Nat) (saved output count : List Bool) :
    Stack → List Bool :=
  Function.update (copied (q := q) v bit ordinal saved output count)
    PairGatePatch.gateOffset (List.replicate ell.val true)

theorem prepared_index {n q : Nat} (v : Fin n) (bit : Fin 2)
    (ordinal : Nat) (saved output count : List Bool) :
    prepared (q := q) v bit ordinal saved output count
      PairGatePatch.gateIndex = List.replicate v.val true := by
  rw [prepared, PairGatePatch.gateIndex]
  change bank PairGateBase.coreEmbedding
    (PairGateBase.ordinalForeign ordinal)
    (PrefixGateReady.prepared v bit saved output count)
    (PairGateBase.coreEmbedding PrefixGateOperands.gateIndex) = _
  rw [bank_at]
  exact PrefixGateReady.prepared_gateIndex v bit saved output count

theorem prepared_offset {n q : Nat} (v : Fin n) (bit : Fin 2)
    (ordinal : Nat) (saved output count : List Bool) :
    prepared (q := q) v bit ordinal saved output count
      PairGatePatch.gateOffset = List.replicate bit.val true := by
  rw [prepared, PairGatePatch.gateOffset]
  change bank PairGateBase.coreEmbedding
    (PairGateBase.ordinalForeign ordinal)
    (PrefixGateReady.prepared v bit saved output count)
    (PairGateBase.coreEmbedding PrefixGateOperands.gateOffset) = _
  rw [bank_at]
  simpa [PrefixGateOperands.gateOffset,
    PrefixGateOperands.constantTarget] using
    PrefixGateReady.prepared_constant v bit saved output count 3

theorem prepared_scratch {n q : Nat} (v : Fin n) (bit : Fin 2)
    (ordinal : Nat) (saved output count : List Bool) :
    prepared (q := q) v bit ordinal saved output count
      PairGatePatch.scratch = [] := by
  rw [prepared, PairGatePatch.scratch]
  change bank PairGateBase.coreEmbedding
    (PairGateBase.ordinalForeign ordinal)
    (PrefixGateReady.prepared v bit saved output count)
    (PairGateBase.coreEmbedding PrefixGateOperands.temp) = _
  rw [bank_at]
  have h := PrefixGateReady.gate_ready (q := q) v bit saved output count
    PrefixGateOperands.tempLocal
  rw [PrefixGateReady.raw_initial_temp (q := q)] at h
  exact h

theorem prepared_ordinal {n q : Nat} (v : Fin n) (bit : Fin 2)
    (ordinal : Nat) (saved output count : List Bool) :
    prepared (q := q) v bit ordinal saved output count
      PairGatePatch.ordinal = List.replicate ordinal true := by
  rw [prepared, PairGatePatch.ordinal, bank_outside]
  · rfl
  · rintro ⟨k, hk⟩
    cases hk

theorem cleared_index {n q : Nat} (v : Fin n) (bit : Fin 2)
    (ordinal : Nat) (saved output count : List Bool) :
    cleared (q := q) v bit ordinal saved output count
      PairGatePatch.gateIndex = [] := by
  simpa only [cleared, PairGatePatch.target] using
    BitMachineClearBank.cleared_bank PairGatePatch.target
      (prepared (q := q) v bit ordinal saved output count) 0

theorem cleared_offset {n q : Nat} (v : Fin n) (bit : Fin 2)
    (ordinal : Nat) (saved output count : List Bool) :
    cleared (q := q) v bit ordinal saved output count
      PairGatePatch.gateOffset = [] := by
  simpa only [cleared, PairGatePatch.target] using
    BitMachineClearBank.cleared_bank PairGatePatch.target
      (prepared (q := q) v bit ordinal saved output count) 1

theorem cleared_ordinal {n q : Nat} (v : Fin n) (bit : Fin 2)
    (ordinal : Nat) (saved output count : List Bool) :
    cleared (q := q) v bit ordinal saved output count
      PairGatePatch.ordinal = List.replicate ordinal true := by
  have hf : ∀ i : Fin 2,
      PairGatePatch.target i ≠ PairGatePatch.ordinal := by
    intro i
    fin_cases i
    · exact PairGatePatch.ordinal_ne_index.symm
    · exact PairGatePatch.ordinal_ne_offset.symm
  rw [cleared, BitMachineClearBank.cleared_foreign
    PairGatePatch.target _ PairGatePatch.ordinal hf]
  exact prepared_ordinal v bit ordinal saved output count

theorem cleared_scratch {n q : Nat} (v : Fin n) (bit : Fin 2)
    (ordinal : Nat) (saved output count : List Bool) :
    cleared (q := q) v bit ordinal saved output count
      PairGatePatch.scratch = [] := by
  have hf : ∀ i : Fin 2,
      PairGatePatch.target i ≠ PairGatePatch.scratch := by
    intro i
    fin_cases i
    · exact PairGatePatch.scratch_ne_index.symm
    · exact PairGatePatch.scratch_ne_offset.symm
  rw [cleared, BitMachineClearBank.cleared_foreign
    PairGatePatch.target _ PairGatePatch.scratch hf]
  exact prepared_scratch v bit ordinal saved output count

theorem copied_offset {n q : Nat} (v : Fin n) (bit : Fin 2)
    (ordinal : Nat) (saved output count : List Bool) :
    copied (q := q) v bit ordinal saved output count
      PairGatePatch.gateOffset = [] := by
  rw [copied, Function.update_of_ne PairGatePatch.index_ne_offset.symm]
  exact cleared_offset v bit ordinal saved output count

noncomputable def phase1 (bit : Fin 2) (w : Nat) :=
  BitMachineRawSequence.program (PairGateBase.preparationProgram bit w)
    PairGatePatch.clearProgram 0 ((), ((), none)) ((), none)

noncomputable def phase2 (bit : Fin 2) (w : Nat) :=
  BitMachineRawSequence.program (phase1 bit w)
    PairGatePatch.copyProgram .scan
    (((), ((), none)), ((), none)) none

noncomputable def program (bit ell : Fin 2) (w : Nat) :=
  BitMachineRawSequence.program (phase2 bit w)
    (PairGatePatch.offsetProgram ell)
    (SourceClauseFixedBatch.labelAt (PairGatePatch.offsetSize ell) 0)
    ((((), ((), none)), ((), none)), none) ()

theorem run {n q : Nat} (v : Fin n) (bit ell : Fin 2)
    (ordinal : Nat) (saved output count : List Bool) :
    ∃ t ≤ PrefixGateOperands.preparationCost bit.val (width 2 q + 1)
        (List.replicate v.val true) +
      (v.val + bit.val + 4) + (2 * ordinal + 2) +
      (PairGatePatch.offsetSize ell 0 + 2) + 3,
      ((advance (program bit ell (width 2 q + 1)))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (SourceClauseFixedBatch.labelAt
                  (PrefixGateOperands.constantSize bit.val
                    (width 2 q + 1)) 0))))),
          (((((), ((), none)), ((), none)), none), ()),
          PairUnitLift.pairBank n v.val ordinal saved output count⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, (((((), ((), none)), ((), none)), none), ()),
          ready (q := q) v bit ell ordinal saved output count⟩ := by
  obtain ⟨a, ha, hprep⟩ := PairGateBase.preparation_run (q := q)
    v bit ordinal saved output count
  let B0 := prepared (q := q) v bit ordinal saved output count
  let B1 := cleared (q := q) v bit ordinal saved output count
  let B2 := copied (q := q) v bit ordinal saved output count
  let B3 := ready (q := q) v bit ell ordinal saved output count
  have hclear := PairGatePatch.clear_run B0
  have hcopy := PairGatePatch.copy_run B1
    (cleared_index v bit ordinal saved output count)
    (cleared_scratch v bit ordinal saved output count)
  have hcopy' : ((advance PairGatePatch.copyProgram)^[
      2 * ordinal + 2])
      (⟨some .scan, none, B1⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, none, B2⟩ := by
    have hor : B1 PairGatePatch.ordinal =
        List.replicate ordinal true :=
      cleared_ordinal v bit ordinal saved output count
    rw [hor] at hcopy
    simpa only [List.length_replicate, B2, copied] using hcopy
  have hoffset := PairGatePatch.offset_run ell B2
    (copied_offset v bit ordinal saved output count)
  have hclear' : ((advance PairGatePatch.clearProgram)^[
      PairGatePatch.clearTime B0])
      (⟨some 0, ((), none), B0⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, ((), none), B1⟩ := by simpa [B1, cleared] using hclear
  have hoffset' : ((advance (PairGatePatch.offsetProgram ell))^[
      SourceClauseFixedBatch.costPrefix (PairGatePatch.offsetSize ell) 1 + 1])
      (⟨some (SourceClauseFixedBatch.labelAt
        (PairGatePatch.offsetSize ell) 0), (), B2⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, (), B3⟩ := by
    simpa [B3, ready] using hoffset
  obtain ⟨t1, ht1, h1⟩ := BitMachineRawSequence.runs
    (PairGateBase.preparationProgram bit (width 2 q + 1))
    PairGatePatch.clearProgram
    (BitMachineRawSequence.leftLabel
      (SourceClauseFixedBatch.labelAt
        (PrefixGateOperands.constantSize bit.val (width 2 q + 1)) 0))
    0 ((), ((), none)) ((), ((), none)) ((), none) ((), none)
    (PairUnitLift.pairBank n v.val ordinal saved output count)
    B0 B1 a (PairGatePatch.clearTime B0) hprep hclear'
  obtain ⟨t2, ht2, h2⟩ := BitMachineRawSequence.runs
    (phase1 bit (width 2 q + 1)) PairGatePatch.copyProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (SourceClauseFixedBatch.labelAt
          (PrefixGateOperands.constantSize bit.val (width 2 q + 1)) 0)))
    .scan (((), ((), none)), ((), none))
    (((), ((), none)), ((), none)) none none
    (PairUnitLift.pairBank n v.val ordinal saved output count)
    B1 B2 t1 (2 * ordinal + 2) h1 hcopy'
  obtain ⟨t3, ht3, h3⟩ := BitMachineRawSequence.runs
    (phase2 bit (width 2 q + 1)) (PairGatePatch.offsetProgram ell)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (SourceClauseFixedBatch.labelAt
            (PrefixGateOperands.constantSize bit.val (width 2 q + 1)) 0))))
    (SourceClauseFixedBatch.labelAt (PairGatePatch.offsetSize ell) 0)
    ((((), ((), none)), ((), none)), none)
    ((((), ((), none)), ((), none)), none) () ()
    (PairUnitLift.pairBank n v.val ordinal saved output count)
    B2 B3 t2
    (SourceClauseFixedBatch.costPrefix (PairGatePatch.offsetSize ell) 1 + 1)
    h2 hoffset'
  refine ⟨t3, ?_, ?_⟩
  · have htime : PairGatePatch.clearTime B0 = v.val + bit.val + 4 := by
      change (B0 PairGatePatch.gateIndex).length +
        (B0 PairGatePatch.gateOffset).length + 4 = _
      have hi : B0 PairGatePatch.gateIndex =
          List.replicate v.val true :=
        prepared_index v bit ordinal saved output count
      have ho : B0 PairGatePatch.gateOffset =
          List.replicate bit.val true :=
        prepared_offset v bit ordinal saved output count
      rw [hi, ho]
      simp
    have hc : SourceClauseFixedBatch.costPrefix
        (PairGatePatch.offsetSize ell) 1 =
        PairGatePatch.offsetSize ell 0 + 1 := by
      simp [SourceClauseFixedBatch.costPrefix]
    rw [hc] at ht3
    omega
  · simpa only [program, B3] using h3

end EthInapproximability.CurrentPaper.SourceBooleanPrefix.PairGatePrep
