import CurrentAdditive.GaussAnyWidthFirstFree
import CurrentAdditive.CodeDIndependenceGuardRun

/-!
Source: v39, appendices/support.tex, paragraph beginning `Discard zero weights`.
This is the actual fixed post-Gauss selector, matrix projection, and preserving
independence branch.  The complete Code D machine must still produce the
Gauss state and connect its dependent branch to relation/update/compaction.
This module makes no claim that its post-Gauss input was physically produced.
-/

namespace CurrentAdditive.CodeDPostGaussStopping

open Turing Turing.TM2 EthInapproximability.CurrentPaper BitMachineEncoding
open GaussAnyWidthFirstFree GaussFirstFreeArithmetic
open GaussPivotPrefixPhysical SequentialTotality
open CurrentAdditive.MinimumRatioContext

noncomputable abbrev Bank := GaussStateMatrixContext.Bank

private theorem mod_bank (j : Nat) (hj : j < 32) :
    j % (32 + (GaussStateMatrixContext.Sel.stackCount +
      GaussStateMatrixContext.Proj.stackCount)) = j :=
  Nat.mod_eq_of_lt (by omega)

noncomputable def program := BitMachineRawSequence.program
  GaussStateMatrixContext.program CodeDIndependenceGuard.program
  (.rowCopy .scan)
  (MachineInvokeFull.control GaussStateMatrixContext.selectorSlots,
    MachineInvokeFull.control GaussStateMatrixContext.matrixSlots)
  (.copy ((), none))

abbrev Label := BitMachineRawSequence.Label
  (BitMachineRawSequence.Label
    (MachineInvokeFull.LabelFull GaussStateMatrixContext.Sel)
    (MachineInvokeFull.LabelFull GaussStateMatrixContext.Proj))
  CodeDIndependenceGuard.Label

noncomputable def start : Label := BitMachineRawSequence.leftLabel
  (BitMachineRawSequence.leftLabel
    (MachineInvokeFull.start GaussStateMatrixContext.selectorSlots))

noncomputable def initialControl :=
  ((MachineInvokeFull.control GaussStateMatrixContext.selectorSlots,
    MachineInvokeFull.control GaussStateMatrixContext.matrixSlots),
    CodeDIndependenceGuard.Control.copy ((), none))

noncomputable def selectorClock (state : List Bool) (m k : Nat) : Nat :=
  MachineInvokeFull.uniformBound GaussStateMatrixContext.Sel state
      (GaussPivotPrefixClock.prefixClock m k) +
    MachineInvokeFull.uniformBound GaussStateMatrixContext.Proj state
      (12 * (state.length + 1)) + 1

theorem typedFree_none_iff {m k : Nat} (A : Fin m → Fin k → ℚ) :
    let s := GaussControlTrace.after A k
    let f := prefixCount (GaussPivotPacketBridge.natPivots s.pivots)
    typedFree s.pivots = none ↔ ¬ f < k := by
  dsimp only
  have h := after_typedFree_eq_prefix_or_none A
  dsimp only at h
  change (typedFree (GaussControlTrace.after A k).pivots).map Fin.val =
    (if _h : prefixCount (GaussPivotPacketBridge.natPivots
      (GaussControlTrace.after A k).pivots) < k then
      some (prefixCount (GaussPivotPacketBridge.natPivots
        (GaussControlTrace.after A k).pivots)) else none) at h
  cases hf : typedFree (GaussControlTrace.after A k).pivots <;>
    by_cases hlt : prefixCount (GaussPivotPacketBridge.natPivots
      (GaussControlTrace.after A k).pivots) < k <;>
    simp_all

/-- One fixed finite stack program obtains the actual first-free prefix and
matrix, then halts with a finite-control bit saying whether elimination is
needed.  Its exact output bank retains the state, width, prefix, and matrix;
all guard scratch is cleared again. -/
theorem outputs {m k : Nat} (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1) :
    let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
    let s := GaussControlTrace.after Aq k
    let f := prefixCount (GaussPivotPacketBridge.natPivots s.pivots)
    let S := GaussStateMatrixContext.inputBank (GaussControlTrace.statePacket s) k
    let T := Function.update
      (Function.update S GaussStateMatrixContext.selectorSlots.target
        (List.replicate f true))
      GaussStateMatrixContext.matrixSlots.target
      (GaussPhysical.encodeTypedMatrix s.B)
    ∃ t, t ≤ selectorClock (GaussControlTrace.statePacket s) m k +
        CodeDIndependenceGuardRun.clock f k + 2 ∧
      ((advance program)^[t])
        (⟨some start, initialControl, S⟩ : TM2.Cfg (fun _ : Bank => Bool) _ _) =
        ⟨none,
          ((MachineInvokeFull.control GaussStateMatrixContext.selectorSlots,
            MachineInvokeFull.control GaussStateMatrixContext.matrixSlots),
            CodeDIndependenceGuard.Control.choose (some (decide (f < k)))), T⟩ ∧
      (typedFree s.pivots = none ↔ ¬ f < k) := by
  dsimp only
  let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
  let s := GaussControlTrace.after Aq k
  let f := prefixCount (GaussPivotPacketBridge.natPivots s.pivots)
  let S := GaussStateMatrixContext.inputBank (GaussControlTrace.statePacket s) k
  let T := Function.update
    (Function.update S GaussStateMatrixContext.selectorSlots.target
      (List.replicate f true)) GaussStateMatrixContext.matrixSlots.target
    (GaussPhysical.encodeTypedMatrix s.B)
  obtain ⟨u, hu, hr, _⟩ := physical_selector_and_matrix_any_width A h01
  have h1 : T 1 = List.replicate f true := by
    simp [T, Function.update_apply, Fin.ext_iff, GaussStateMatrixContext.matrixSlots,
      GaussStateMatrixContext.selectorSlots, mod_bank 1 (by omega), mod_bank 3 (by omega), mod_bank 20 (by omega), mod_bank 21 (by omega), mod_bank 22 (by omega), mod_bank 29 (by omega)]
  have h3 : T 3 = List.replicate k true := by
    simp [T, S, Function.update_apply, Fin.ext_iff, GaussStateMatrixContext.inputBank,
      GaussStateMatrixContext.matrixSlots, GaussStateMatrixContext.selectorSlots, mod_bank 1 (by omega), mod_bank 3 (by omega), mod_bank 20 (by omega), mod_bank 21 (by omega), mod_bank 22 (by omega), mod_bank 29 (by omega)]
  have h20 : T 20 = [] := by
    simp [T, S, Function.update_apply, Fin.ext_iff, GaussStateMatrixContext.inputBank,
      GaussStateMatrixContext.matrixSlots, GaussStateMatrixContext.selectorSlots, mod_bank 1 (by omega), mod_bank 3 (by omega), mod_bank 20 (by omega), mod_bank 21 (by omega), mod_bank 22 (by omega), mod_bank 29 (by omega)]
  have h21 : T 21 = [] := by
    simp [T, S, Function.update_apply, Fin.ext_iff, GaussStateMatrixContext.inputBank,
      GaussStateMatrixContext.matrixSlots, GaussStateMatrixContext.selectorSlots, mod_bank 1 (by omega), mod_bank 3 (by omega), mod_bank 20 (by omega), mod_bank 21 (by omega), mod_bank 22 (by omega), mod_bank 29 (by omega)]
  have h22 : T 22 = [] := by
    simp [T, S, Function.update_apply, Fin.ext_iff, GaussStateMatrixContext.inputBank,
      GaussStateMatrixContext.matrixSlots, GaussStateMatrixContext.selectorSlots, mod_bank 1 (by omega), mod_bank 3 (by omega), mod_bank 20 (by omega), mod_bank 21 (by omega), mod_bank 22 (by omega), mod_bank 29 (by omega)]
  have h29 : T 29 = [] := by
    simp [T, S, Function.update_apply, Fin.ext_iff, GaussStateMatrixContext.inputBank,
      GaussStateMatrixContext.matrixSlots, GaussStateMatrixContext.selectorSlots, mod_bank 1 (by omega), mod_bank 3 (by omega), mod_bank 20 (by omega), mod_bank 21 (by omega), mod_bank 22 (by omega), mod_bank 29 (by omega)]
  obtain ⟨v, hv, hg⟩ :=
    CodeDIndependenceGuardRun.outputs T f k h1 h3 h20 h21 h22 h29
  have haltStep : CodeDIndependenceGuard.run 1
      ⟨some (if f < k then .active else .terminal),
        .choose (some (decide (f < k))), T⟩ =
      ⟨none, .choose (some (decide (f < k))), T⟩ := by
    by_cases hlt : f < k <;>
      simp [CodeDIndependenceGuard.run, CodeDIndependenceGuard.program,
        hlt, advance, TM2.step, TM2.stepAux]
  have hg' := (CodeDIndependenceGuard.run_add hg 1).trans haltStep
  obtain ⟨t, ht, htRun⟩ := BitMachineRawSequence.runs
    GaussStateMatrixContext.program CodeDIndependenceGuard.program
    (BitMachineRawSequence.leftLabel
      (MachineInvokeFull.start GaussStateMatrixContext.selectorSlots))
    (.rowCopy .scan)
    (MachineInvokeFull.control GaussStateMatrixContext.selectorSlots,
      MachineInvokeFull.control GaussStateMatrixContext.matrixSlots)
    (MachineInvokeFull.control GaussStateMatrixContext.selectorSlots,
      MachineInvokeFull.control GaussStateMatrixContext.matrixSlots)
    (.copy ((), none)) (.choose (some (decide (f < k))))
    S T T u (v + 1) hr hg'
  refine ⟨t, ?_, ?_, ?_⟩
  · change u ≤ selectorClock (GaussControlTrace.statePacket s) m k at hu
    change t ≤ selectorClock (GaussControlTrace.statePacket s) m k +
      CodeDIndependenceGuardRun.clock f k + 2
    omega
  · simpa only [program, start, initialControl] using htRun
  · exact typedFree_none_iff Aq

#print axioms typedFree_none_iff
#print axioms outputs

end CurrentAdditive.CodeDPostGaussStopping
