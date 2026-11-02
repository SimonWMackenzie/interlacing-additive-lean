import EthInapproximability.CurrentPaper.GenericPrefixGateOperands
import EthInapproximability.CurrentPaper.SourceGenericPrefix

namespace EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.GateReady

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceBooleanEncoding
open scoped Classical
noncomputable section

open SourceBooleanPrefix

def prepared {n a : Nat} (v : Fin n) (s : Fin a)
    (w : Nat) (saved output count : List Bool) :=
  GateOperands.prepared a s.val w (List.replicate v.val true)
    (PrefixGateReady.blank n v.val saved output count)

theorem prepared_run {n a : Nat} (v : Fin n) (s : Fin a)
    (w : Nat) (saved output count : List Bool) :
    ∃ T ≤ GateOperands.cost a s.val w (List.replicate v.val true),
      ((advance (GateOperands.program a s.val w))^[T])
        (⟨some (BitMachineRawSequence.leftLabel
          (SourceClauseFixedBatch.labelAt
            (GateOperands.constantSize a s.val w) 0)),
          ((),((),none)),PrefixGateReady.blank n v.val
            saved output count⟩) =
        ⟨none,((),((),none)),prepared v s w saved output count⟩ := by
  exact GateOperands.run a s.val w (List.replicate v.val true)
    (PrefixGateReady.blank n v.val saved output count)
    (PrefixGateReady.blank_vertex n v.val saved output count)
    (PrefixGateReady.blank_temp n v.val saved output count)

theorem fixed_constant {n a : Nat} (v : Fin n) (s : Fin a)
    (w : Nat) (saved output count : List Bool) (i : Fin 5) :
    GateOperands.fixed a s.val w
      (PrefixGateReady.blank n v.val saved output count)
      (PrefixGateOperands.constantTarget i) =
        List.replicate (GateOperands.constantSize a s.val w i) true := by
  rw [GateOperands.fixed,SourceClauseFixedBatch.result_target
    PrefixGateOperands.constantTarget (GateOperands.constantSize a s.val w)
    (PrefixGateReady.blank n v.val saved output count)
    PrefixGateOperands.constantTarget_injective i]
  rw [PrefixGateOperands.constantTarget_eq]
  change List.replicate (GateOperands.constantSize a s.val w i) true ++
    PrefixGateReady.blank n v.val saved output count
      (PrefixSharedCore.gateEmbedding
        (PrefixGateOperands.constantLocal i)) = _
  rw [PrefixGateReady.blank_gate_scratch n v.val saved output count _
    (PrefixGateOperands.constant_not_core i)]
  simp

theorem fixed_other {n a : Nat} (v : Fin n) (s : Fin a)
    (w : Nat) (saved output count : List Bool)
    (x : PrefixSharedCore.Gate)
    (hconst : ∀ i : Fin 5, x ≠ PrefixGateOperands.constantLocal i) :
    GateOperands.fixed a s.val w
      (PrefixGateReady.blank n v.val saved output count)
      (PrefixSharedCore.gateEmbedding x) =
    PrefixGateReady.blank n v.val saved output count
      (PrefixSharedCore.gateEmbedding x) := by
  apply SourceClauseFixedBatch.result_outside
  intro i
  rw [PrefixGateOperands.constantTarget_eq]
  exact fun h => hconst i (PrefixSharedCore.gateEmbedding.injective h.symm)

theorem prepared_constant {n a : Nat} (v : Fin n) (s : Fin a)
    (w : Nat) (saved output count : List Bool) (i : Fin 5) :
    prepared v s w saved output count
      (PrefixGateOperands.constantTarget i) =
        List.replicate (GateOperands.constantSize a s.val w i) true := by
  rw [prepared,GateOperands.prepared,PrefixGateOperands.copied,
    SourceClausePreservingBroadcast.other_preserved]
  · exact fixed_constant v s w saved output count i
  · rw [PrefixGateOperands.constantTarget_eq]
    exact Ne.symm (PrefixGateOperands.source_ne _
      (PrefixGateOperands.constant_not_core i))
  · intro h
    rw [PrefixGateOperands.constantTarget_eq] at h
    have hh := PrefixSharedCore.gateEmbedding.injective h
    fin_cases i <;>
      simp [PrefixGateOperands.constantLocal,PrefixGateOperands.temp,
        PrefixGateOperands.gateCell,SourceClauseRowGate.temp,
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
          exact PrefixGateReady.literal_not_constant i
            (PrefixSharedCore.gateEmbedding.injective h).symm,
         by
          intro h
          rw [PrefixGateOperands.constantTarget_eq] at h
          change PrefixSharedCore.gateEmbedding
            (PrefixGateOperands.constantLocal i) =
            PrefixSharedCore.gateEmbedding
              PrefixGateOperands.gateIndexLocal at h
          exact PrefixGateReady.gateIndex_not_constant i
            (PrefixSharedCore.gateEmbedding.injective h).symm⟩)

theorem prepared_core {n a : Nat} (v : Fin n) (s : Fin a)
    (w : Nat) (saved output count : List Bool)
    (i : PrefixSharedCore.Core) :
    prepared v s w saved output count
      (PrefixSharedCore.gateEmbedding (PrefixSharedCore.gateCore i)) =
      PrefixGateReady.coreWords n v.val saved output count i := by
  by_cases hi : i = 1
  · subst i
    rw [PrefixSharedCore.gateEmbedding,
      SourceClauseSharedCore.left_core]
    change prepared v s w saved output count PrefixGateOperands.vertex = _
    rw [prepared,GateOperands.prepared,PrefixGateOperands.copied,
      SourceClausePreservingBroadcast.source_restored]
    · rfl
    · exact PrefixGateOperands.source_ne _
        PrefixGateOperands.temp_not_core
  · rw [prepared,GateOperands.prepared,PrefixGateOperands.copied,
      SourceClausePreservingBroadcast.other_preserved]
    · rw [fixed_other v s w saved output count]
      · exact PrefixGateReady.blank_gate_core n v.val saved output count i
      · intro j h
        exact PrefixGateOperands.constant_not_core j ⟨i,h⟩
    · rw [PrefixSharedCore.gateEmbedding,
        SourceClauseSharedCore.left_core]
      simpa [PrefixGateOperands.vertex] using hi
    · intro h
      have hh := PrefixSharedCore.gateEmbedding.injective h
      exact PrefixGateOperands.temp_not_core ⟨i,hh⟩
    · simp only [PrefixGateOperands.vertexTargets,List.mem_cons,
        List.mem_singleton,not_or]
      constructor
      · intro h
        have hh := PrefixSharedCore.gateEmbedding.injective h
        exact PrefixGateOperands.literalIndex_not_core ⟨i,hh⟩
      · refine ⟨?_,by simp⟩
        intro h
        have hh := PrefixSharedCore.gateEmbedding.injective h
        exact PrefixGateOperands.gateIndex_not_core ⟨i,hh⟩

theorem prepared_target {n a : Nat} (v : Fin n) (s : Fin a)
    (w : Nat) (saved output count : List Bool)
    (x : PrefixSharedCore.Gate)
    (hx : x = PrefixGateOperands.literalLocal ∨
      x = PrefixGateOperands.gateIndexLocal) :
    prepared v s w saved output count
      (PrefixSharedCore.gateEmbedding x) =
      List.replicate v.val true := by
  rcases hx with rfl | rfl
  · rw [prepared,GateOperands.prepared,PrefixGateOperands.copied,
      SourceClausePreservingBroadcast.target_written]
    · change List.replicate v.val true ++
        GateOperands.fixed a s.val w
          (PrefixGateReady.blank n v.val saved output count)
          (PrefixSharedCore.gateEmbedding PrefixGateOperands.literalLocal) = _
      rw [fixed_other v s w saved output count _
        PrefixGateReady.literal_not_constant]
      rw [PrefixGateReady.blank_gate_scratch n v.val saved output count _
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
    · simp [PrefixGateOperands.vertexTargets,
        PrefixGateOperands.literalIndex,PrefixGateOperands.literalLocal,
        PrefixGateOperands.gateCell]
  · rw [prepared,GateOperands.prepared,PrefixGateOperands.copied,
      SourceClausePreservingBroadcast.target_written]
    · change List.replicate v.val true ++
        GateOperands.fixed a s.val w
          (PrefixGateReady.blank n v.val saved output count)
          (PrefixSharedCore.gateEmbedding PrefixGateOperands.gateIndexLocal) = _
      rw [fixed_other v s w saved output count _
        PrefixGateReady.gateIndex_not_constant]
      rw [PrefixGateReady.blank_gate_scratch n v.val saved output count _
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
    · simp [PrefixGateOperands.vertexTargets,
        PrefixGateOperands.gateIndex,PrefixGateOperands.gateIndexLocal,
        PrefixGateOperands.gateCell]

theorem prepared_other_empty {n a : Nat} (v : Fin n) (s : Fin a)
    (w : Nat) (saved output count : List Bool)
    (x : PrefixSharedCore.Gate)
    (hcore : x ∉ Set.range PrefixSharedCore.gateCore)
    (hconst : ∀ i : Fin 5,
      x ≠ PrefixGateOperands.constantLocal i)
    (hliteral : x ≠ PrefixGateOperands.literalLocal)
    (hindex : x ≠ PrefixGateOperands.gateIndexLocal)
    (htemp : x ≠ PrefixGateOperands.tempLocal) :
    prepared v s w saved output count
      (PrefixSharedCore.gateEmbedding x) = [] := by
  rw [prepared,GateOperands.prepared,PrefixGateOperands.copied,
    SourceClausePreservingBroadcast.other_preserved]
  · rw [fixed_other v s w saved output count x hconst]
    exact PrefixGateReady.blank_gate_scratch n v.val saved output count x hcore
  · intro h
    rw [PrefixGateOperands.vertex] at h
    have hh := PrefixSharedCore.gateEmbedding.injective
      (show PrefixSharedCore.gateEmbedding x =
        PrefixSharedCore.gateEmbedding (PrefixSharedCore.gateCore 1) from
        by simpa [PrefixSharedCore.gateEmbedding,
          SourceClauseSharedCore.left_core PrefixSharedCore.gateCore
            PrefixSharedCore.unitCore (1 : PrefixSharedCore.Core)] using h)
    exact hcore ⟨1,hh.symm⟩
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

theorem raw_initial_core {n a : Nat} (v : Fin n) (s : Fin a)
    (w : Nat) (saved output count : List Bool)
    (i : PrefixSharedCore.Core) :
    SourceClauseRowGate.initial (vertexFrame v)
      v.val a s.val n s.val v.val w saved output count
      (PrefixSharedCore.gateCore i) =
    PrefixGateReady.coreWords n v.val saved output count i := by
  fin_cases i <;>
    simp [PrefixSharedCore.gateCore,PrefixSharedCore.gateCoreCell,
      PrefixSharedCore.gateN,PrefixSharedCore.gateVertex,
      PrefixGateClean.savedCell,PrefixGateClean.outputCell,
      PrefixGateClean.countCell,gateSavedKey,gateCountKey,
      SourceClauseRowGate.initial,SourceClauseRowGate.gateEmbedding,
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
      MatrixAddressMachine.cfg,vertexFrame,
      PrefixGateReady.coreWords]

theorem raw_initial_constant {n a : Nat} (v : Fin n) (s : Fin a)
    (w : Nat) (saved output count : List Bool) (i : Fin 5) :
    SourceClauseRowGate.initial (vertexFrame v)
      v.val a s.val n s.val v.val w saved output count
      (PrefixGateOperands.constantLocal i) =
    List.replicate (GateOperands.constantSize a s.val w i) true := by
  fin_cases i <;>
    simp [PrefixGateOperands.constantLocal,GateOperands.constantSize,
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

theorem raw_initial_target {n a : Nat} (v : Fin n) (s : Fin a)
    (w : Nat) (saved output count : List Bool)
    (x : PrefixSharedCore.Gate)
    (hx : x = PrefixGateOperands.literalLocal ∨
      x = PrefixGateOperands.gateIndexLocal) :
    SourceClauseRowGate.initial (vertexFrame v)
      v.val a s.val n s.val v.val w saved output count x =
      List.replicate v.val true := by
  rcases hx with rfl | rfl <;> rfl

theorem raw_initial_temp {n a : Nat} (v : Fin n) (s : Fin a)
    (w : Nat) (saved output count : List Bool) :
    SourceClauseRowGate.initial (vertexFrame v)
      v.val a s.val n s.val v.val w saved output count
      PrefixGateOperands.tempLocal = [] := by rfl

theorem raw_initial_other_empty {n a : Nat} (v : Fin n) (s : Fin a)
    (w : Nat) (saved output count : List Bool)
    (x : PrefixSharedCore.Gate)
    (hcore : x ∉ Set.range PrefixSharedCore.gateCore)
    (hconst : ∀ i : Fin 5, x ≠ PrefixGateOperands.constantLocal i)
    (hliteral : x ≠ PrefixGateOperands.literalLocal)
    (hindex : x ≠ PrefixGateOperands.gateIndexLocal) :
    SourceClauseRowGate.initial (vertexFrame v)
      v.val a s.val n s.val v.val w saved output count x = [] := by
  have hc0 : x ≠ PrefixSharedCore.gateCore 0 :=
    fun h => hcore ⟨0,h.symm⟩
  have hc1 : x ≠ PrefixSharedCore.gateCore 1 :=
    fun h => hcore ⟨1,h.symm⟩
  have hc2 : x ≠ PrefixSharedCore.gateCore 2 :=
    fun h => hcore ⟨2,h.symm⟩
  have hc3 : x ≠ PrefixSharedCore.gateCore 3 :=
    fun h => hcore ⟨3,h.symm⟩
  have hc4 : x ≠ PrefixSharedCore.gateCore 4 :=
    fun h => hcore ⟨4,h.symm⟩
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
          vertexFrame,PrefixSharedCore.gateCore,
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
          SourceLiteralWriter.contents,
          PrefixSharedCore.gateCore,
          PrefixSharedCore.gateCoreCell]
        all_goals first
          | exact False.elim (hc2 rfl)
          | exact False.elim (hc3 rfl)
          | exact False.elim (hc4 rfl)
    · fin_cases x <;> simp_all [SourceClauseRowGate.initial]

theorem gate_ready {n a : Nat} (v : Fin n) (s : Fin a)
    (w : Nat) (saved output count : List Bool) :
    ∀ x : SourceClauseRowGate.Stack 1,
      prepared v s w saved output count
        (PrefixSharedCore.gateEmbedding x) =
      SourceClauseRowGate.initial (vertexFrame v)
        v.val a s.val n s.val v.val w saved output count x := by
  intro x
  by_cases hcore : x ∈ Set.range PrefixSharedCore.gateCore
  · obtain ⟨i,rfl⟩ := hcore
    rw [prepared_core,raw_initial_core]
  by_cases hc : ∃ i : Fin 5, x = PrefixGateOperands.constantLocal i
  · obtain ⟨i,rfl⟩ := hc
    rw [raw_initial_constant]
    simpa only [PrefixGateOperands.constantTarget_eq,
      PrefixGateOperands.gateCell] using
      (prepared_constant v s w saved output count i)
  have hconst : ∀ i : Fin 5,
      x ≠ PrefixGateOperands.constantLocal i :=
    fun i h => hc ⟨i,h⟩
  by_cases hliteral : x = PrefixGateOperands.literalLocal
  · subst x
    rw [raw_initial_target]
    · exact prepared_target v s w saved output count _ (Or.inl rfl)
    · exact Or.inl rfl
  by_cases hindex : x = PrefixGateOperands.gateIndexLocal
  · subst x
    rw [raw_initial_target]
    · exact prepared_target v s w saved output count _ (Or.inr rfl)
    · exact Or.inr rfl
  by_cases htemp : x = PrefixGateOperands.tempLocal
  · subst x
    rw [raw_initial_temp]
    exact SourceClausePreservingBroadcast.temp_empty
      PrefixGateOperands.vertex PrefixGateOperands.temp
      PrefixGateOperands.vertexTargets (List.replicate v.val true)
      (GateOperands.fixed a s.val w
        (PrefixGateReady.blank n v.val saved output count))
  rw [prepared_other_empty v s w saved output count x
      hcore hconst hliteral hindex htemp,
    raw_initial_other_empty v s w saved output count x
      hcore hconst hliteral hindex]

#print axioms prepared_run
#print axioms prepared_constant
#print axioms gate_ready

end
end EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.GateReady
