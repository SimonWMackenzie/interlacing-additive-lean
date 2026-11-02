import Paper2.CodeSampleInterpreterResult
import Paper2.CodeTableFallback
import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps

/-! Source-preserving physical copies of raw mX/mY to the fallback writer. -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

namespace Paper2.CodeFallbackDimensionLoader

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSerialization

abbrev SourceStack := CodeSampleInterpreterJoin.Stack
abbrev WriterStack := CodeTableFallback.WriterStack
abbrev Stack := SourceStack ⊕ WriterStack

def sourceX : Stack := .inl (CodeSampleInterpreterLoader.sampleSlots
  CodeGeneratorSampleTransfer.countX)
def sourceY : Stack := .inl (CodeSampleInterpreterLoader.sampleSlots
  CodeGeneratorSampleTransfer.countY)
def rows : Stack := .inr (.inr .rows)
def cols : Stack := .inr (.inr .cols)
def scratch : Stack := .inl CodeSampleInterpreterLoader.scratch

def xSlot : Fin 3 → Stack
  | 0 => sourceX
  | 1 => rows
  | _ => scratch
def ySlot : Fin 3 → Stack
  | 0 => sourceY
  | 1 => cols
  | _ => scratch

theorem xSlot_injective : Function.Injective xSlot := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [xSlot, sourceX, rows, scratch,
      CodeSampleInterpreterLoader.sampleSlots,
      CodeSampleInterpreterLoader.scratch]
theorem ySlot_injective : Function.Injective ySlot := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [ySlot, sourceY, cols, scratch,
      CodeSampleInterpreterLoader.sampleSlots,
      CodeSampleInterpreterLoader.scratch]

def xSlots : Fin 3 ↪ Stack := ⟨xSlot, xSlot_injective⟩
def ySlots : Fin 3 ↪ Stack := ⟨ySlot, ySlot_injective⟩
noncomputable def xProgram := MatrixStage4ScalarPreparationOps.copyProgram xSlots
noncomputable def yProgram := MatrixStage4ScalarPreparationOps.copyProgram ySlots

def initialBank (S : SourceStack → List Bool) : Stack → List Bool :=
  Sum.elim S (fun _ => [])
noncomputable def afterX (S : SourceStack → List Bool) (mX : Nat) :
    Stack → List Bool := Function.update (initialBank S) rows
      (List.replicate mX true)
noncomputable def afterY (S : SourceStack → List Bool) (mX mY : Nat) :
    Stack → List Bool := Function.update (afterX S mX) cols
      (List.replicate mY true)

theorem x_run (S : SourceStack → List Bool) (mX : Nat)
    (hX : S (CodeSampleInterpreterLoader.sampleSlots
      CodeGeneratorSampleTransfer.countX) = List.replicate mX true)
    (hScratch : S CodeSampleInterpreterLoader.scratch = []) :
    ((advance xProgram)^[2*mX+2])
      (⟨some .scan,none,initialBank S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none,none,afterX S mX⟩ := by
  have h := MatrixStage4ScalarPreparationOps.copy_run xSlots
    (initialBank S) (by simpa [initialBank, xSlots, xSlot,
      scratch] using hScratch)
  rw [show initialBank S (xSlots 0) = List.replicate mX true from hX,
    show initialBank S (xSlots 1) = [] from rfl,
    List.append_nil, List.length_replicate] at h
  simpa only [xProgram, xSlots, xSlot, afterX] using h

theorem y_run (S : SourceStack → List Bool) (mX mY : Nat)
    (hY : S (CodeSampleInterpreterLoader.sampleSlots
      CodeGeneratorSampleTransfer.countY) = List.replicate mY true)
    (hScratch : S CodeSampleInterpreterLoader.scratch = []) :
    ((advance yProgram)^[2*mY+2])
      (⟨some .scan,none,afterX S mX⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none,none,afterY S mX mY⟩ := by
  have h := MatrixStage4ScalarPreparationOps.copy_run ySlots
    (afterX S mX) (by simpa [afterX, initialBank, ySlots, ySlot,
      scratch, rows] using hScratch)
  rw [show afterX S mX (ySlots 0) = List.replicate mY true from by
      simpa [afterX, initialBank, ySlots, ySlot, cols, sourceY] using hY,
    show afterX S mX (ySlots 1) = [] from by
      simp [afterX, initialBank, ySlots, ySlot, cols, rows],
    List.append_nil, List.length_replicate] at h
  simpa only [yProgram, ySlots, ySlot, afterY] using h

#print axioms x_run
#print axioms y_run

end Paper2.CodeFallbackDimensionLoader
