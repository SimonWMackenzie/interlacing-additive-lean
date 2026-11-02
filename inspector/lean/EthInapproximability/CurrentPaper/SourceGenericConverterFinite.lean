import EthInapproximability.CurrentPaper.SourceGenericConverterTotal

/-!
# Finite names for the fixed generic converter (unit 1, cited composition)

Paper B, locked v8 Section 6 (`thm:paper-sparse-gap-source`) and Appendix B;
CP-SOURCE-EFFECTIVE, arbitrary fixed alphabet `a`.

The frozen predecessor program `SourceGenericComposite.Converter.converter a q hq`
is a raw `TM2` program over explicit finite label, control and stack types.
This module proves those types finite (no assumption: each constituent is
certified, including the list-recursive ordered-pair routine over all `a*a`
symbol pairs), so the program can be renamed to a `BitMachine.Machine` by the
existing `BitMachineEncoding.ofFinite`. Finite relabelling is a change of
finite names, not a unit-cost instruction.
-/

namespace EthInapproximability.CurrentPaper.SourceGenericComposite.ConverterFinite

open Turing BitMachineEncoding
open SourceBooleanPrefix SourceBooleanPrefix.PairMachineComposition
open SourceGenericPrefixMachine
open scoped Classical

abbrev LabOf {K L V : Type} [DecidableEq K]
    (_P : L → TM2.Stmt (fun _ : K => Bool) L V) : Type := L

/-! ## The global validator control -/

def globalControlCode {a q : Nat} : SourceCSPGlobalDecisionProgram.Control a q →
    SourceCSPGuardOutputCombined.Control ⊕
      ((Unit × SourceCSPPositiveCapEntry.CapControl) ⊕
        (Option Bool ⊕ (SourceCSPHeaderRowBridge.Control5 ⊕
          (SourceCSPRowLoopController.Control ⊕
            (Option Bool ⊕ (Option Bool ⊕ Unit))))))
  | .prefix v => .inl v
  | .cap v => .inr (.inl v)
  | .capStatus v => .inr (.inr (.inl v))
  | .prepare v => .inr (.inr (.inr (.inl v)))
  | .row v => .inr (.inr (.inr (.inr (.inl v))))
  | .rowCopy v => .inr (.inr (.inr (.inr (.inr (.inl v)))))
  | .writer v => .inr (.inr (.inr (.inr (.inr (.inr (.inl v))))))
  | .done => .inr (.inr (.inr (.inr (.inr (.inr (.inr ()))))))

theorem globalControlCode_injective (a q : Nat) :
    Function.Injective (globalControlCode (a := a) (q := q)) := by
  intro x y h
  cases x <;> cases y <;> simp_all [globalControlCode]

instance globalControlFinite (a q : Nat) :
    Finite (SourceCSPGlobalDecisionProgram.Control a q) := by
  haveI h1 : Finite (Option Bool ⊕ (Option Bool ⊕ Unit)) := inferInstance
  haveI h2 : Finite (SourceCSPRowLoopController.Control ⊕
      (Option Bool ⊕ (Option Bool ⊕ Unit))) := inferInstance
  haveI h3 : Finite (SourceCSPHeaderRowBridge.Control5 ⊕
      (SourceCSPRowLoopController.Control ⊕ (Option Bool ⊕ (Option Bool ⊕ Unit)))) :=
    inferInstance
  haveI h4 : Finite (Option Bool ⊕ (SourceCSPHeaderRowBridge.Control5 ⊕
      (SourceCSPRowLoopController.Control ⊕ (Option Bool ⊕ (Option Bool ⊕ Unit))))) :=
    inferInstance
  haveI h5 : Finite ((Unit × SourceCSPPositiveCapEntry.CapControl) ⊕
      (Option Bool ⊕ (SourceCSPHeaderRowBridge.Control5 ⊕
        (SourceCSPRowLoopController.Control ⊕ (Option Bool ⊕ (Option Bool ⊕ Unit)))))) :=
    inferInstance
  exact Finite.of_injective _ (globalControlCode_injective a q)

/-! ## Routine certificates (ordered-pair callback over all `a*a` pairs) -/

structure RoutineFinite (R : Routine) : Prop where
  labels : Finite R.Label
  controls : Finite R.Control

theorem sequence_finite {A B : Routine} (hA : RoutineFinite A) (hB : RoutineFinite B) :
    RoutineFinite (sequence A B) := by
  have hAL := hA.labels
  have hAC := hA.controls
  have hBL := hB.labels
  have hBC := hB.controls
  refine ⟨?_, ?_⟩
  · change Finite (BitMachineRawSequence.Label A.Label B.Label)
    infer_instance
  · change Finite (BitMachineRawSequence.Control A.Control B.Control)
    infer_instance

theorem idle_finite : RoutineFinite SourceGenericPairEnumeration.idle := by
  refine ⟨?_, ?_⟩
  · change Finite Unit; infer_instance
  · change Finite Unit; infer_instance

theorem listRoutine_finite {α : Type} (C : α → Routine) (hC : ∀ x, RoutineFinite (C x)) :
    ∀ xs : List α, RoutineFinite (SourceGenericPairEnumeration.listRoutine C xs)
  | [] => idle_finite
  | x :: xs => sequence_finite (hC x) (listRoutine_finite C hC xs)

theorem loader_finite (a : Nat) (s t : Fin a) :
    RoutineFinite (PairOneMachine.loader a s t) := by
  refine ⟨?_, ?_⟩
  · dsimp [PairOneMachine.loader, fromProgram]; infer_instance
  · dsimp [PairOneMachine.loader, fromProgram]; infer_instance

theorem unit_finite (a w ell : Nat) (sign : Bool) :
    RoutineFinite (PairOneMachine.unit a w ell sign) := by
  refine ⟨?_, ?_⟩
  · dsimp [PairOneMachine.unit, fromProgram]; infer_instance
  · dsimp [PairOneMachine.unit, fromProgram]; infer_instance

theorem gate_finite {a : Nat} (bit : Fin a) (ell : Fin 2) (sign : Bool) (w : Nat) :
    RoutineFinite (PairOneMachine.gate bit ell sign w) := by
  refine ⟨?_, ?_⟩
  · dsimp [PairOneMachine.gate, fromProgram]; infer_instance
  · dsimp [PairOneMachine.gate, fromProgram]; infer_instance

theorem reset_finite : RoutineFinite PairOneMachine.reset := by
  refine ⟨?_, ?_⟩
  · dsimp [PairOneMachine.reset, fromProgram]; infer_instance
  · dsimp [PairOneMachine.reset, fromProgram]; infer_instance

theorem one_finite (a q : Nat) (s t : Fin a) :
    RoutineFinite (PairOneMachine.routine a q s t) := by
  unfold PairOneMachine.routine
  exact sequence_finite (sequence_finite (sequence_finite (sequence_finite
    (sequence_finite (loader_finite a s t) (unit_finite _ _ _ _))
    (gate_finite _ _ _ _)) (gate_finite _ _ _ _)) (unit_finite _ _ _ _)) reset_finite

theorem vertex_finite (a q : Nat) :
    RoutineFinite (PairVertexLoopCallback.routine a q) := by
  change RoutineFinite (SourceGenericPairEnumeration.vertexRoutine a q)
  unfold SourceGenericPairEnumeration.vertexRoutine
  exact listRoutine_finite (fun st : Fin a × Fin a => PairOneMachine.routine a q st.1 st.2)
    (fun st => one_finite a q st.1 st.2) (SourceGenericPairEnumeration.pairs a)

instance vertexLabelFinite (a q : Nat) :
    Finite (PairVertexLoopCallback.routine a q).Label := (vertex_finite a q).labels

instance vertexControlFinite (a q : Nat) :
    Finite (PairVertexLoopCallback.routine a q).Control := (vertex_finite a q).controls

instance atLeastLabelFinite (a q : Nat) :
    Finite (AtLeastLoopCallback.callback a q).Label :=
  (AtLeastLoopCallback.callback a q).labelsFinite

instance atLeastControlFinite (a q : Nat) :
    Finite (AtLeastLoopCallback.callback a q).Control :=
  (AtLeastLoopCallback.callback a q).controlFinite

instance allCircuitLabelFinite {a q : Nat} (hq : 0 < q) :
    Finite (SourceClauseGenericAllSlots.allCircuit (a := a) hq).Label :=
  (SourceClauseGenericAllSlots.allCircuit (a := a) hq).labelsFinite

instance allCircuitControlFinite {a q : Nat} (hq : 0 < q) :
    Finite (SourceClauseGenericAllSlots.allCircuit (a := a) hq).Control :=
  (SourceClauseGenericAllSlots.allCircuit (a := a) hq).controlFinite

/-! ## The converter's label and control types -/

set_option synthInstance.maxSize 2048 in
theorem labelFinite (a q : Nat) (hq : 0 < q) :
    Finite (Converter.TopLabel a q (Converter.LabOf (Converter.body (a := a) hq))) := by
  infer_instance

set_option synthInstance.maxSize 2048 in
theorem controlFinite (a q : Nat) (hq : 0 < q) :
    Finite (Converter.TopControl a q (FirstRow.CtlOf (Converter.body (a := a) hq))) := by
  infer_instance

#print axioms globalControlFinite
#print axioms vertex_finite
#print axioms labelFinite
#print axioms controlFinite

end EthInapproximability.CurrentPaper.SourceGenericComposite.ConverterFinite
