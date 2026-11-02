import EthInapproximability.CurrentPaper.SourceClausePrefixGateOperands

/-!
Exact full-bank readiness of the prefix OR gate after charged operand
preparation. The bank starts with only the five shared core cells nonempty.
-/

namespace EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixGateReady

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceBooleanEncoding
open scoped Classical
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

abbrev Stack := PrefixSharedCore.Stack
noncomputable instance : Fintype (SourceClauseRowGate.Stack 1) :=
  Fintype.ofFinite _

def coreWords (n v : ℕ) (saved output count : List Bool) :
    PrefixSharedCore.Core → List Bool :=
  ![List.replicate n true, List.replicate v true,
    saved, output, count]

noncomputable def blank (n v : ℕ) (saved output count : List Bool) :
    Stack → List Bool :=
  Sum.elim (coreWords n v saved output count) (fun _ => [])

theorem blank_vertex (n v : ℕ) (saved output count : List Bool) :
    blank n v saved output count PrefixGateOperands.vertex =
      List.replicate v true := by rfl

theorem blank_temp (n v : ℕ) (saved output count : List Bool) :
    blank n v saved output count PrefixGateOperands.temp = [] := by
  change blank n v saved output count
    (PrefixSharedCore.gateEmbedding PrefixGateOperands.tempLocal) = []
  rw [PrefixSharedCore.gateEmbedding,
    SourceClauseSharedCore.left_outside PrefixSharedCore.gateCore
      PrefixSharedCore.unitCore _ PrefixGateOperands.temp_not_core]
  rfl

noncomputable def prepared {n q : ℕ} (v : Fin n) (s : Fin 2)
    (saved output count : List Bool) : Stack → List Bool :=
  PrefixGateOperands.copied (List.replicate v.val true)
    (PrefixGateOperands.fixed s.val (width 2 q + 1)
      (blank n v.val saved output count))

theorem prepared_run {n q : ℕ} (v : Fin n) (s : Fin 2)
    (saved output count : List Bool) :
    ∃ T ≤ PrefixGateOperands.preparationCost s.val (width 2 q + 1)
        (List.replicate v.val true),
      ((advance (PrefixGateOperands.preparationProgram s.val
        (width 2 q + 1)))^[T])
        (⟨some (BitMachineRawSequence.leftLabel
          (SourceClauseFixedBatch.labelAt
            (PrefixGateOperands.constantSize s.val (width 2 q + 1)) 0)),
          ((), ((), none)), blank n v.val saved output count⟩) =
        ⟨none, ((), ((), none)), prepared (q := q) v s saved output count⟩ := by
  exact PrefixGateOperands.preparation_run s.val (width 2 q + 1)
    (List.replicate v.val true) (blank n v.val saved output count)
    (blank_vertex n v.val saved output count)
    (blank_temp n v.val saved output count)

theorem blank_gate_core (n v : ℕ) (saved output count : List Bool)
    (i : PrefixSharedCore.Core) :
    blank n v saved output count
      (PrefixSharedCore.gateEmbedding (PrefixSharedCore.gateCore i)) =
      coreWords n v saved output count i := by
  rw [PrefixSharedCore.gateEmbedding,
    SourceClauseSharedCore.left_core PrefixSharedCore.gateCore
      PrefixSharedCore.unitCore i]
  rfl

theorem blank_gate_scratch (n v : ℕ) (saved output count : List Bool)
    (x : PrefixSharedCore.Gate)
    (hx : x ∉ Set.range PrefixSharedCore.gateCore) :
    blank n v saved output count (PrefixSharedCore.gateEmbedding x) = [] := by
  rw [PrefixSharedCore.gateEmbedding,
    SourceClauseSharedCore.left_outside PrefixSharedCore.gateCore
      PrefixSharedCore.unitCore x hx]
  rfl

theorem fixed_constant {n : ℕ} (v : Fin n) (s : Fin 2)
    (w : ℕ) (saved output count : List Bool) (i : Fin 5) :
    PrefixGateOperands.fixed s.val w
      (blank n v.val saved output count)
      (PrefixGateOperands.constantTarget i) =
      List.replicate (PrefixGateOperands.constantSize s.val w i) true := by
  rw [PrefixGateOperands.fixed, SourceClauseFixedBatch.result_target
    PrefixGateOperands.constantTarget
    (PrefixGateOperands.constantSize s.val w)
    (blank n v.val saved output count)
    PrefixGateOperands.constantTarget_injective i]
  rw [PrefixGateOperands.constantTarget_eq]
  change List.replicate (PrefixGateOperands.constantSize s.val w i) true ++
    blank n v.val saved output count
      (PrefixSharedCore.gateEmbedding (PrefixGateOperands.constantLocal i)) = _
  rw [blank_gate_scratch n v.val saved output count _
    (PrefixGateOperands.constant_not_core i)]
  simp

theorem fixed_other {n : ℕ} (v : Fin n) (s : Fin 2)
    (w : ℕ) (saved output count : List Bool)
    (x : PrefixSharedCore.Gate)
    (hconst : ∀ i : Fin 5,
      x ≠ PrefixGateOperands.constantLocal i) :
    PrefixGateOperands.fixed s.val w
      (blank n v.val saved output count)
      (PrefixSharedCore.gateEmbedding x) =
      blank n v.val saved output count
        (PrefixSharedCore.gateEmbedding x) := by
  apply SourceClauseFixedBatch.result_outside
  intro i
  rw [PrefixGateOperands.constantTarget_eq]
  exact fun h => hconst i (PrefixSharedCore.gateEmbedding.injective h.symm)

theorem literal_not_constant (i : Fin 5) :
    PrefixGateOperands.literalLocal ≠ PrefixGateOperands.constantLocal i := by
  fin_cases i <;>
    simp [PrefixGateOperands.literalLocal,
      PrefixGateOperands.constantLocal,
      SourceClauseRowGate.addressEmbedding,
      SourceClauseRowGate.gateEmbedding]

theorem gateIndex_not_constant (i : Fin 5) :
    PrefixGateOperands.gateIndexLocal ≠
      PrefixGateOperands.constantLocal i := by
  fin_cases i <;>
    simp [PrefixGateOperands.gateIndexLocal,
      PrefixGateOperands.constantLocal,
      SourceClauseRowGate.addressEmbedding,
      SourceClauseRowGate.gateEmbedding,
      SourceClauseGateSlotAddress.gateEmbedding,
      SourceClauseGateAffineAddress.addressEmbedding]

theorem prepared_literal {n q : ℕ} (v : Fin n) (s : Fin 2)
    (saved output count : List Bool) :
    prepared (q := q) v s saved output count
      PrefixGateOperands.literalIndex = List.replicate v.val true := by
  rw [prepared, PrefixGateOperands.copied,
    SourceClausePreservingBroadcast.target_written]
  · change List.replicate v.val true ++
      PrefixGateOperands.fixed s.val (width 2 q + 1)
        (blank n v.val saved output count)
        (PrefixSharedCore.gateEmbedding PrefixGateOperands.literalLocal) = _
    rw [fixed_other v s (width 2 q + 1) saved output count
      PrefixGateOperands.literalLocal literal_not_constant]
    rw [blank_gate_scratch n v.val saved output count _
      PrefixGateOperands.literalIndex_not_core]
    simp
  · simpa [PrefixGateOperands.vertexTargets] using
      (show PrefixGateOperands.temp ≠ PrefixGateOperands.literalIndex ∧
          PrefixGateOperands.temp ≠ PrefixGateOperands.gateIndex from
        ⟨PrefixGateOperands.temp_ne_literal,
          PrefixGateOperands.temp_ne_gate⟩)
  · simpa [PrefixGateOperands.vertexTargets] using
      (show PrefixGateOperands.vertex ≠ PrefixGateOperands.literalIndex ∧
          PrefixGateOperands.vertex ≠ PrefixGateOperands.gateIndex from
        ⟨PrefixGateOperands.source_ne _
            PrefixGateOperands.literalIndex_not_core,
          PrefixGateOperands.source_ne _
            PrefixGateOperands.gateIndex_not_core⟩)
  · exact PrefixGateOperands.source_ne _
      PrefixGateOperands.temp_not_core
  · simp [PrefixGateOperands.vertexTargets]

theorem prepared_gateIndex {n q : ℕ} (v : Fin n) (s : Fin 2)
    (saved output count : List Bool) :
    prepared (q := q) v s saved output count
      PrefixGateOperands.gateIndex = List.replicate v.val true := by
  rw [prepared, PrefixGateOperands.copied,
    SourceClausePreservingBroadcast.target_written]
  · change List.replicate v.val true ++
      PrefixGateOperands.fixed s.val (width 2 q + 1)
        (blank n v.val saved output count)
        (PrefixSharedCore.gateEmbedding PrefixGateOperands.gateIndexLocal) = _
    rw [fixed_other v s (width 2 q + 1) saved output count
      PrefixGateOperands.gateIndexLocal gateIndex_not_constant]
    rw [blank_gate_scratch n v.val saved output count _
      PrefixGateOperands.gateIndex_not_core]
    simp
  · simpa [PrefixGateOperands.vertexTargets] using
      (show PrefixGateOperands.temp ≠ PrefixGateOperands.literalIndex ∧
          PrefixGateOperands.temp ≠ PrefixGateOperands.gateIndex from
        ⟨PrefixGateOperands.temp_ne_literal,
          PrefixGateOperands.temp_ne_gate⟩)
  · simpa [PrefixGateOperands.vertexTargets] using
      (show PrefixGateOperands.vertex ≠ PrefixGateOperands.literalIndex ∧
          PrefixGateOperands.vertex ≠ PrefixGateOperands.gateIndex from
        ⟨PrefixGateOperands.source_ne _
            PrefixGateOperands.literalIndex_not_core,
          PrefixGateOperands.source_ne _
            PrefixGateOperands.gateIndex_not_core⟩)
  · exact PrefixGateOperands.source_ne _
      PrefixGateOperands.temp_not_core
  · simp [PrefixGateOperands.vertexTargets]

theorem prepared_constant {n q : ℕ} (v : Fin n) (s : Fin 2)
    (saved output count : List Bool) (i : Fin 5) :
    prepared (q := q) v s saved output count
      (PrefixGateOperands.constantTarget i) =
      List.replicate
        (PrefixGateOperands.constantSize s.val (width 2 q + 1) i) true := by
  rw [prepared, PrefixGateOperands.copied,
    SourceClausePreservingBroadcast.other_preserved]
  · exact fixed_constant v s (width 2 q + 1) saved output count i
  · rw [PrefixGateOperands.constantTarget_eq]
    exact Ne.symm (PrefixGateOperands.source_ne _
      (PrefixGateOperands.constant_not_core i))
  · intro h
    rw [PrefixGateOperands.constantTarget_eq] at h
    have hh := PrefixSharedCore.gateEmbedding.injective h
    fin_cases i <;>
      simp [PrefixGateOperands.constantLocal,
        PrefixGateOperands.temp, PrefixGateOperands.gateCell,
        SourceClauseRowGate.temp,
        SourceClauseRowGate.addressEmbedding,
        SourceClauseRowGate.gateEmbedding] at hh
  · simpa [PrefixGateOperands.vertexTargets,
      PrefixGateOperands.constantTarget_eq] using
      (show PrefixGateOperands.constantTarget i ≠
            PrefixGateOperands.literalIndex ∧
          PrefixGateOperands.constantTarget i ≠
            PrefixGateOperands.gateIndex from
        ⟨by
          intro h
          rw [PrefixGateOperands.constantTarget_eq] at h
          change PrefixSharedCore.gateEmbedding
            (PrefixGateOperands.constantLocal i) =
            PrefixSharedCore.gateEmbedding
              PrefixGateOperands.literalLocal at h
          exact literal_not_constant i
            (PrefixSharedCore.gateEmbedding.injective h).symm,
         by
          intro h
          rw [PrefixGateOperands.constantTarget_eq] at h
          change PrefixSharedCore.gateEmbedding
            (PrefixGateOperands.constantLocal i) =
            PrefixSharedCore.gateEmbedding
              PrefixGateOperands.gateIndexLocal at h
          exact gateIndex_not_constant i
            (PrefixSharedCore.gateEmbedding.injective h).symm⟩)

theorem prepared_core {n q : ℕ} (v : Fin n) (s : Fin 2)
    (saved output count : List Bool)
    (i : PrefixSharedCore.Core) :
    prepared (q := q) v s saved output count
      (PrefixSharedCore.gateEmbedding (PrefixSharedCore.gateCore i)) =
      coreWords n v.val saved output count i := by
  by_cases hi : i = 1
  · subst i
    rw [PrefixSharedCore.gateEmbedding,
      SourceClauseSharedCore.left_core]
    change prepared (q := q) v s saved output count
      PrefixGateOperands.vertex = _
    rw [prepared, PrefixGateOperands.copied,
      SourceClausePreservingBroadcast.source_restored]
    · rfl
    · exact PrefixGateOperands.source_ne _
        PrefixGateOperands.temp_not_core
  · rw [prepared, PrefixGateOperands.copied,
      SourceClausePreservingBroadcast.other_preserved]
    · rw [fixed_other v s (width 2 q + 1) saved output count]
      · exact blank_gate_core n v.val saved output count i
      · intro j h
        exact PrefixGateOperands.constant_not_core j ⟨i, h⟩
    · rw [PrefixSharedCore.gateEmbedding,
        SourceClauseSharedCore.left_core]
      simpa [PrefixGateOperands.vertex] using hi
    · intro h
      have hh := PrefixSharedCore.gateEmbedding.injective h
      exact PrefixGateOperands.temp_not_core ⟨i, hh⟩
    · simp only [PrefixGateOperands.vertexTargets, List.mem_cons,
        List.mem_singleton, not_or]
      constructor
      · intro h
        have hh := PrefixSharedCore.gateEmbedding.injective h
        exact PrefixGateOperands.literalIndex_not_core ⟨i, hh⟩
      · refine ⟨?_, by simp⟩
        intro h
        have hh := PrefixSharedCore.gateEmbedding.injective h
        exact PrefixGateOperands.gateIndex_not_core ⟨i, hh⟩

theorem prepared_other_empty {n q : ℕ} (v : Fin n) (s : Fin 2)
    (saved output count : List Bool)
    (x : PrefixSharedCore.Gate)
    (hcore : x ∉ Set.range PrefixSharedCore.gateCore)
    (hconst : ∀ i : Fin 5,
      x ≠ PrefixGateOperands.constantLocal i)
    (hliteral : x ≠ PrefixGateOperands.literalLocal)
    (hindex : x ≠ PrefixGateOperands.gateIndexLocal)
    (htemp : x ≠ PrefixGateOperands.tempLocal) :
    prepared (q := q) v s saved output count
      (PrefixSharedCore.gateEmbedding x) = [] := by
  rw [prepared, PrefixGateOperands.copied,
    SourceClausePreservingBroadcast.other_preserved]
  · rw [fixed_other v s (width 2 q + 1) saved output count x hconst]
    exact blank_gate_scratch n v.val saved output count x hcore
  · intro h
    rw [PrefixGateOperands.vertex] at h
    have hh := PrefixSharedCore.gateEmbedding.injective
      (show PrefixSharedCore.gateEmbedding x =
        PrefixSharedCore.gateEmbedding (PrefixSharedCore.gateCore 1) from
        by simpa [PrefixSharedCore.gateEmbedding,
          SourceClauseSharedCore.left_core PrefixSharedCore.gateCore
            PrefixSharedCore.unitCore (1 : PrefixSharedCore.Core)] using h)
    exact hcore ⟨1, hh.symm⟩
  · intro h
    exact htemp (PrefixSharedCore.gateEmbedding.injective
      (by simpa [PrefixGateOperands.temp,
        PrefixGateOperands.gateCell,
        PrefixGateOperands.tempLocal] using h))
  · simpa [PrefixGateOperands.vertexTargets] using
      (show PrefixSharedCore.gateEmbedding x ≠
            PrefixGateOperands.literalIndex ∧
          PrefixSharedCore.gateEmbedding x ≠
            PrefixGateOperands.gateIndex from
        ⟨fun h => hliteral (PrefixSharedCore.gateEmbedding.injective
            (by simpa [PrefixGateOperands.literalIndex,
              PrefixGateOperands.gateCell,
              PrefixGateOperands.literalLocal] using h)),
         fun h => hindex (PrefixSharedCore.gateEmbedding.injective
            (by simpa [PrefixGateOperands.gateIndex,
              PrefixGateOperands.gateCell,
              PrefixGateOperands.gateIndexLocal] using h))⟩)

theorem raw_initial_core {n q : ℕ} (v : Fin n) (s : Fin 2)
    (saved output count : List Bool)
    (i : PrefixSharedCore.Core) :
    SourceClauseRowGate.initial (vertexFrame v)
      v.val 2 s.val n s.val v.val (width 2 q + 1)
      saved output count (PrefixSharedCore.gateCore i) =
    coreWords n v.val saved output count i := by
  fin_cases i <;>
    simp [PrefixSharedCore.gateCore, PrefixSharedCore.gateCoreCell,
      PrefixSharedCore.gateN, PrefixSharedCore.gateVertex,
      PrefixGateClean.savedCell, PrefixGateClean.outputCell,
      PrefixGateClean.countCell, gateSavedKey, gateCountKey,
      SourceClauseRowGate.initial, SourceClauseRowGate.gateEmbedding,
      SourceClauseGateSlotAddress.gateEmbedding,
      SourceClauseGateAffineAddress.gateEmbedding,
      SourceClauseGateTwoAddress.embedding,
      SourceClauseGateMachine.embedding,
      SourceClauseGateSlotAddress.initial,
      SourceClauseGateAffineAddress.initial,
      SourceClauseGateSuccessor.initial,
      SourceClauseGateBroadcast.initial,
      SourceClauseGateSchedule.contents,
      SourceLiteralWriter.contents,
      SourceClauseRowLiteralAddress.initial,
      SourceLabelAddressMachine.inputs,
      SourceClauseGateSlotAddress.offsetInput,
      MatrixAddressMachine.cfg,
      vertexFrame, coreWords]

theorem raw_initial_constant {n q : ℕ} (v : Fin n) (s : Fin 2)
    (saved output count : List Bool) (i : Fin 5) :
    SourceClauseRowGate.initial (vertexFrame v)
      v.val 2 s.val n s.val v.val (width 2 q + 1)
      saved output count (PrefixGateOperands.constantLocal i) =
    List.replicate
      (PrefixGateOperands.constantSize s.val (width 2 q + 1) i) true := by
  fin_cases i <;>
    simp [PrefixGateOperands.constantLocal,
      PrefixGateOperands.constantSize,
      SourceClauseRowGate.initial,
      SourceClauseRowGate.addressEmbedding,
      SourceClauseRowGate.gateEmbedding,
      SourceClauseGateSlotAddress.gateEmbedding,
      SourceClauseGateAffineAddress.addressEmbedding,
      SourceClauseRowLiteralAddress.initial,
      SourceClauseGateSlotAddress.initial,
      SourceClauseGateAffineAddress.initial,
      SourceLabelAddressMachine.inputs,
      SourceLabelAddressMachine.ambient,
      SourceClauseGateSlotAddress.offsetInput,
      MatrixAddressMachine.cfg]

theorem raw_initial_literal {n q : ℕ} (v : Fin n) (s : Fin 2)
    (saved output count : List Bool) :
    SourceClauseRowGate.initial (vertexFrame v)
      v.val 2 s.val n s.val v.val (width 2 q + 1)
      saved output count PrefixGateOperands.literalLocal =
    List.replicate v.val true := by
  rfl

theorem raw_initial_gateIndex {n q : ℕ} (v : Fin n) (s : Fin 2)
    (saved output count : List Bool) :
    SourceClauseRowGate.initial (vertexFrame v)
      v.val 2 s.val n s.val v.val (width 2 q + 1)
      saved output count PrefixGateOperands.gateIndexLocal =
    List.replicate v.val true := by
  rfl

theorem raw_initial_temp {n q : ℕ} (v : Fin n) (s : Fin 2)
    (saved output count : List Bool) :
    SourceClauseRowGate.initial (vertexFrame v)
      v.val 2 s.val n s.val v.val (width 2 q + 1)
      saved output count PrefixGateOperands.tempLocal = [] := by
  rfl

theorem raw_initial_other_empty {n q : ℕ} (v : Fin n) (s : Fin 2)
    (saved output count : List Bool)
    (x : PrefixSharedCore.Gate)
    (hcore : x ∉ Set.range PrefixSharedCore.gateCore)
    (hconst : ∀ i : Fin 5,
      x ≠ PrefixGateOperands.constantLocal i)
    (hliteral : x ≠ PrefixGateOperands.literalLocal)
    (hindex : x ≠ PrefixGateOperands.gateIndexLocal) :
    SourceClauseRowGate.initial (vertexFrame v)
      v.val 2 s.val n s.val v.val (width 2 q + 1)
      saved output count x = [] := by
  have hc0 : x ≠ PrefixSharedCore.gateCore 0 :=
    fun h => hcore ⟨0, h.symm⟩
  have hc1 : x ≠ PrefixSharedCore.gateCore 1 :=
    fun h => hcore ⟨1, h.symm⟩
  have hc2 : x ≠ PrefixSharedCore.gateCore 2 :=
    fun h => hcore ⟨2, h.symm⟩
  have hc3 : x ≠ PrefixSharedCore.gateCore 3 :=
    fun h => hcore ⟨3, h.symm⟩
  have hc4 : x ≠ PrefixSharedCore.gateCore 4 :=
    fun h => hcore ⟨4, h.symm⟩
  have hf0 := hconst 0
  have hf1 := hconst 1
  have hf2 := hconst 2
  have hf3 := hconst 3
  have hf4 := hconst 4
  rcases x with x | x
  · rcases x with x | x
    · rcases x with x | x
      · fin_cases x <;> simp_all [SourceClauseRowGate.initial,
          SourceClauseRowLiteralAddress.initial,
          SourceLabelAddressMachine.inputs,
          SourceLabelAddressMachine.ambient,
          vertexFrame, PrefixSharedCore.gateCore,
          PrefixSharedCore.gateCoreCell,
          PrefixSharedCore.gateVertex]
      · fin_cases x <;> simp_all [SourceClauseRowGate.initial,
          SourceClauseRowLiteralAddress.initial,
          SourceLabelAddressMachine.inputs,
          SourceLabelAddressMachine.ambient,
          PrefixGateOperands.constantLocal,
          PrefixGateOperands.literalLocal,
          SourceClauseRowGate.addressEmbedding,
          vertexFrame]
    · fin_cases x <;> simp_all [SourceClauseRowGate.initial,
        SourceClauseRowLiteralAddress.initial,
        SourceLabelAddressMachine.inputs,
        SourceLabelAddressMachine.ambient,
        PrefixGateOperands.constantLocal,
        PrefixGateOperands.literalLocal,
        SourceClauseRowGate.addressEmbedding]
  · rcases x with x | x
    · rcases x with x | x
      · fin_cases x <;> simp_all [SourceClauseRowGate.initial,
          SourceClauseGateSlotAddress.initial,
          SourceClauseGateSlotAddress.offsetInput,
          MatrixAddressMachine.cfg,
          PrefixSharedCore.gateCore,
          PrefixSharedCore.gateCoreCell,
          PrefixSharedCore.gateN,
          PrefixGateOperands.constantLocal,
          SourceClauseRowGate.gateEmbedding]
      · fin_cases x <;> simp_all [SourceClauseRowGate.initial,
          SourceClauseGateSlotAddress.initial,
          SourceClauseGateAffineAddress.initial,
          SourceLabelAddressMachine.inputs,
          SourceLabelAddressMachine.ambient,
          PrefixGateOperands.constantLocal,
          PrefixGateOperands.gateIndexLocal,
          SourceClauseRowGate.gateEmbedding,
          SourceClauseGateSlotAddress.gateEmbedding,
          SourceClauseGateAffineAddress.addressEmbedding,
          SourceClauseGateSuccessor.initial,
           SourceClauseGateBroadcast.initial,
           SourceClauseGateSchedule.contents,
           SourceClauseCountedStream.contents,
           SourceLiteralWriter.contents, PrefixSharedCore.gateCore,
           PrefixSharedCore.gateCoreCell]
        all_goals first
          | exact False.elim (hc2 rfl)
          | exact False.elim (hc3 rfl)
          | exact False.elim (hc4 rfl)
    · fin_cases x <;> simp_all [SourceClauseRowGate.initial]

theorem gate_ready {n q : ℕ} (v : Fin n) (s : Fin 2)
    (saved output count : List Bool) :
    ∀ x : SourceClauseRowGate.Stack 1,
      prepared (q := q) v s saved output count
        (PrefixSharedCore.gateEmbedding x) =
      SourceClauseRowGate.initial (vertexFrame v)
        v.val 2 s.val n s.val v.val (width 2 q + 1)
        saved output count x := by
  intro x
  by_cases hcore : x ∈ Set.range PrefixSharedCore.gateCore
  · obtain ⟨i, rfl⟩ := hcore
    rw [prepared_core, raw_initial_core]
  by_cases hc : ∃ i : Fin 5, x = PrefixGateOperands.constantLocal i
  · obtain ⟨i, rfl⟩ := hc
    rw [raw_initial_constant]
    simpa only [PrefixGateOperands.constantTarget_eq,
      PrefixGateOperands.gateCell] using
      (prepared_constant v s saved output count i)
  have hconst : ∀ i : Fin 5, x ≠ PrefixGateOperands.constantLocal i :=
    fun i h => hc ⟨i, h⟩
  by_cases hliteral : x = PrefixGateOperands.literalLocal
  · subst x
    rw [raw_initial_literal]
    exact prepared_literal v s saved output count
  by_cases hindex : x = PrefixGateOperands.gateIndexLocal
  · subst x
    rw [raw_initial_gateIndex]
    exact prepared_gateIndex v s saved output count
  by_cases htemp : x = PrefixGateOperands.tempLocal
  · subst x
    rw [raw_initial_temp]
    exact SourceClausePreservingBroadcast.temp_empty
      PrefixGateOperands.vertex PrefixGateOperands.temp
      PrefixGateOperands.vertexTargets (List.replicate v.val true)
      (PrefixGateOperands.fixed s.val (width 2 q + 1)
        (blank n v.val saved output count))
  rw [prepared_other_empty v s saved output count x
      hcore hconst hliteral hindex htemp,
    raw_initial_other_empty v s saved output count x
      hcore hconst hliteral hindex]


end EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixGateReady
