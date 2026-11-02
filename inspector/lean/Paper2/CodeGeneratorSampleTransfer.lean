import Paper2.CodeGeneratorComplete
import Paper2.CodeSampleAssembly
import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps

/-! Four charged source-preserving copies from the completed Fin65 compiler
and public sample counts into the reviewed Fin12 sample-code assembler. -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

namespace Paper2.CodeGeneratorSampleTransfer

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2.GeneratorCode Paper2.GeneratorSerialization

abbrev CompilerStack := Paper2.CodeRecursiveLoop.Stack
abbrev SampleStack := Paper2.CodeSampleAssembly.Stack
abbrev Stack := CompilerStack ⊕ (SampleStack ⊕ Fin 3)

def compilerSlots : CompilerStack ↪ Stack :=
  ⟨Sum.inl, by intro a b h; exact Sum.inl_injective h⟩
def sampleSlots : SampleStack ↪ Stack :=
  ⟨fun k => .inr (.inl k), by intro a b h; cases h; rfl⟩

def countX : Stack := .inr (.inr 0)
def countY : Stack := .inr (.inr 1)
def scratch : Stack := .inr (.inr 2)
def sample (k : SampleStack) : Stack := sampleSlots k

def foreign (mX mY : Nat) : Stack → List Bool
  | .inr (.inr 0) => List.replicate mX true
  | .inr (.inr 1) => List.replicate mY true
  | _ => []

noncomputable def initialBank (F : CompilerStack → List Bool)
    (mX mY : Nat) : Stack → List Bool :=
  bank compilerSlots (foreign mX mY) F

def rowSlots : Fin 3 ↪ Stack :=
  ⟨![.inl 2, sample 1, scratch], by decide⟩
def colSlots : Fin 3 ↪ Stack :=
  ⟨![.inl 33, sample 6, scratch], by decide⟩
def xSlots : Fin 3 ↪ Stack :=
  ⟨![countX, sample 0, scratch], by decide⟩
def ySlots : Fin 3 ↪ Stack :=
  ⟨![countY, sample 5, scratch], by decide⟩

def rowProgram := MatrixStage4ScalarPreparationOps.copyProgram rowSlots
def colProgram := MatrixStage4ScalarPreparationOps.copyProgram colSlots
def xProgram := MatrixStage4ScalarPreparationOps.copyProgram xSlots
def yProgram := MatrixStage4ScalarPreparationOps.copyProgram ySlots

def afterRow (S : Stack → List Bool) (row : Code) :=
  Function.update S (sample 1) (encodeCode row)
def afterCol (S : Stack → List Bool) (row col : Code) :=
  Function.update (afterRow S row) (sample 6) (encodeCode col)
def seedBank (S : Stack → List Bool) (row col : Code) :=
  Function.update (Function.update (afterCol S row col)
    (sample 0) [false]) (sample 5) [false]
def afterX (S : Stack → List Bool) (row col : Code) (mX : Nat) :=
  Function.update (seedBank S row col) (sample 0) (unary mX)
def afterY (S : Stack → List Bool) (row col : Code) (mX mY : Nat) :=
  Function.update (afterX S row col mX) (sample 5) (unary mY)
noncomputable def readyBank (F : CompilerStack → List Bool) (mX mY : Nat)
    (row col : Code) := afterY (initialBank F mX mY) row col mX mY

private theorem source_at (F : CompilerStack → List Bool)
    (mX mY : Nat) (k : CompilerStack) :
    initialBank F mX mY (.inl k) = F k := by
  exact bank_at compilerSlots (foreign mX mY) F k

private theorem sample_empty (F : CompilerStack → List Bool)
    (mX mY : Nat) (k : SampleStack) :
    initialBank F mX mY (sample k) = [] := by
  rw [initialBank, bank_outside]
  · rfl
  · rintro ⟨j,h⟩; cases h

private theorem scratch_empty (F : CompilerStack → List Bool)
    (mX mY : Nat) : initialBank F mX mY scratch = [] := by
  rw [initialBank, bank_outside]
  · rfl
  · rintro ⟨j,h⟩; cases h

theorem countX_at (F : CompilerStack → List Bool)
    (mX mY : Nat) : initialBank F mX mY countX = List.replicate mX true := by
  rw [initialBank, bank_outside]
  · rfl
  · rintro ⟨j,h⟩; cases h

theorem countY_at (F : CompilerStack → List Bool)
    (mX mY : Nat) : initialBank F mX mY countY = List.replicate mY true := by
  rw [initialBank, bank_outside]
  · rfl
  · rintro ⟨j,h⟩; cases h

theorem row_run (F : CompilerStack → List Bool) (mX mY : Nat)
    (row : Code) (hr : F 2 = encodeCode row) :
    ((advance rowProgram)^[2*(encodeCode row).length+2])
      (⟨some .scan,none,initialBank F mX mY⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none,none,afterRow (initialBank F mX mY) row⟩ := by
  have h := MatrixStage4ScalarPreparationOps.copy_run rowSlots
    (initialBank F mX mY) (scratch_empty F mX mY)
  rw [show initialBank F mX mY (rowSlots 0) = encodeCode row
      from (source_at F mX mY 2).trans hr,
    show initialBank F mX mY (rowSlots 1) = []
      from sample_empty F mX mY 1, List.append_nil] at h
  simpa only [rowProgram, rowSlots, afterRow] using h

theorem col_run (F : CompilerStack → List Bool) (mX mY : Nat)
    (row col : Code) (hc : F 33 = encodeCode col) :
    ((advance colProgram)^[2*(encodeCode col).length+2])
      (⟨some .scan,none,afterRow (initialBank F mX mY) row⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none,none,afterCol (initialBank F mX mY) row col⟩ := by
  let S := afterRow (initialBank F mX mY) row
  have hscr : S (colSlots 2) = [] := by
    simpa [S, afterRow, colSlots, sample, sampleSlots, scratch] using
      scratch_empty F mX mY
  have h := MatrixStage4ScalarPreparationOps.copy_run colSlots S hscr
  have hsrc : S (colSlots 0) = encodeCode col := by
    have h := (source_at F mX mY 33).trans hc
    simpa [S, afterRow, colSlots, sample, sampleSlots] using h
  have hdst : S (colSlots 1) = [] := by
    have h := sample_empty F mX mY 6
    simpa [S, afterRow, colSlots, sample, sampleSlots] using h
  rw [hsrc, hdst, List.append_nil] at h
  simpa only [colProgram, colSlots, afterCol, S] using h

theorem x_run (F : CompilerStack → List Bool) (mX mY : Nat)
    (row col : Code) :
    ((advance xProgram)^[2*mX+2])
      (⟨some .scan,none,seedBank (initialBank F mX mY) row col⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none,none,afterX (initialBank F mX mY) row col mX⟩ := by
  let S := seedBank (initialBank F mX mY) row col
  have hscr : S (xSlots 2) = [] := by
    simpa [S, seedBank, afterCol, afterRow, xSlots, sample, sampleSlots, scratch]
      using scratch_empty F mX mY
  have h := MatrixStage4ScalarPreparationOps.copy_run xSlots S hscr
  have hsrc : S (xSlots 0) = List.replicate mX true := by
    simpa [S, seedBank, afterCol, afterRow, xSlots, sample, sampleSlots, countX]
      using countX_at F mX mY
  have hdst : S (xSlots 1) = [false] := by
    simp [S, seedBank, xSlots, sample, sampleSlots]
  rw [hsrc, hdst] at h
  simp only [List.length_replicate] at h
  simpa only [xProgram, show xSlots 1 = sample 0 from rfl,
    afterX, S, GeneratorSerialization.unary] using h

theorem y_run (F : CompilerStack → List Bool) (mX mY : Nat)
    (row col : Code) :
    ((advance yProgram)^[2*mY+2])
      (⟨some .scan,none,afterX (initialBank F mX mY) row col mX⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none,none,afterY (initialBank F mX mY) row col mX mY⟩ := by
  let S := afterX (initialBank F mX mY) row col mX
  have hscr : S (ySlots 2) = [] := by
    simpa [S, afterX, seedBank, afterCol, afterRow, ySlots, sample, sampleSlots,
      scratch] using scratch_empty F mX mY
  have h := MatrixStage4ScalarPreparationOps.copy_run ySlots S hscr
  have hsrc : S (ySlots 0) = List.replicate mY true := by
    simpa [S, afterX, seedBank, afterCol, afterRow, ySlots, sample, sampleSlots,
      countY] using countY_at F mX mY
  have hdst : S (ySlots 1) = [false] := by
    simp [S, afterX, seedBank, ySlots, sample, sampleSlots]
  rw [hsrc, hdst] at h
  simp only [List.length_replicate] at h
  simpa only [yProgram, show ySlots 1 = sample 5 from rfl,
    afterY, S, GeneratorSerialization.unary] using h

inductive TermLabel where | terminate
  deriving DecidableEq, Fintype

def termProgram : TermLabel → TM2.Stmt (fun _ : Stack => Bool)
    TermLabel Unit
  | .terminate => .push (sample 0) (fun _ => false)
      (.push (sample 5) (fun _ => false) .halt)

theorem term_run (F : CompilerStack → List Bool) (mX mY : Nat)
    (row col : Code) :
    advance termProgram
      (⟨some .terminate,(),afterCol (initialBank F mX mY) row col⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none,(),seedBank (initialBank F mX mY) row col⟩ := by
  have h0 : initialBank F mX mY (.inr (.inl (0 : SampleStack))) = [] :=
    sample_empty F mX mY 0
  have h5 : initialBank F mX mY (.inr (.inl (5 : SampleStack))) = [] :=
    sample_empty F mX mY 5
  simp [termProgram, EthInapproximability.CurrentPaper.BitMachineEncoding.advance, TM2.step, TM2.stepAux,
    seedBank, afterCol, afterRow, sample, sampleSlots, h0, h5]

def prog01 := BitMachineRawSequence.program rowProgram colProgram
  BitMachineCopy.Label.scan none none
def prog012 := BitMachineRawSequence.program prog01 termProgram
  TermLabel.terminate (none,none) ()
def prog0123 := BitMachineRawSequence.program prog012 xProgram
  BitMachineCopy.Label.scan ((none,none),()) none
def transferProgram := BitMachineRawSequence.program prog0123 yProgram
  BitMachineCopy.Label.scan (((none,none),()),none) none

def start01 : BitMachineRawSequence.Label BitMachineCopy.Label
    BitMachineCopy.Label := .inl .scan
def start012 : BitMachineRawSequence.Label
    (BitMachineRawSequence.Label BitMachineCopy.Label BitMachineCopy.Label)
    TermLabel := .inl start01
def start0123 : BitMachineRawSequence.Label
    (BitMachineRawSequence.Label
      (BitMachineRawSequence.Label BitMachineCopy.Label BitMachineCopy.Label)
      TermLabel) BitMachineCopy.Label := .inl start012
def transferStart : BitMachineRawSequence.Label
    (BitMachineRawSequence.Label
      (BitMachineRawSequence.Label
        (BitMachineRawSequence.Label BitMachineCopy.Label
          BitMachineCopy.Label) TermLabel) BitMachineCopy.Label)
    BitMachineCopy.Label := .inl start0123

def transferClock (mX mY : Nat) (row col : Code) : Nat :=
  (2*(encodeCode row).length+2) + (2*(encodeCode col).length+2) +
    (2*mX+2) + (2*mY+2) + 1 + 4

theorem transfer_run (F : CompilerStack → List Bool) (mX mY : Nat)
    (row col : Code)
    (hr : F 2 = encodeCode row) (hc : F 33 = encodeCode col) :
    ∃ t ≤ transferClock mX mY row col,
      ((advance transferProgram)^[t])
        (⟨some transferStart,((((none,none),()),none),none),
          initialBank F mX mY⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,((((none,none),()),none),none),
          readyBank F mX mY row col⟩ := by
  obtain ⟨t01,ht01,h01⟩ := BitMachineRawSequence.runs
    rowProgram colProgram .scan .scan none none none none
    (initialBank F mX mY) (afterRow (initialBank F mX mY) row)
    (afterCol (initialBank F mX mY) row col)
    (2*(encodeCode row).length+2) (2*(encodeCode col).length+2)
    (row_run F mX mY row hr) (col_run F mX mY row col hc)
  obtain ⟨t012,ht012,h012⟩ := BitMachineRawSequence.runs
    prog01 termProgram start01 .terminate (none,none) (none,none) () ()
    (initialBank F mX mY) (afterCol (initialBank F mX mY) row col)
    (seedBank (initialBank F mX mY) row col)
    t01 1 (by simpa only [prog01, start01] using h01)
    (by simpa only [Function.iterate_one] using term_run F mX mY row col)
  obtain ⟨t0123,ht0123,h0123⟩ := BitMachineRawSequence.runs
    prog012 xProgram start012 .scan ((none,none),())
    ((none,none),()) none none
    (initialBank F mX mY) (seedBank (initialBank F mX mY) row col)
    (afterX (initialBank F mX mY) row col mX)
    t012 (2*mX+2) (by simpa only [prog012, start012] using h012)
    (x_run F mX mY row col)
  obtain ⟨t,ht,h⟩ := BitMachineRawSequence.runs
    prog0123 yProgram start0123 .scan
    (((none,none),()),none) (((none,none),()),none) none none
    (initialBank F mX mY)
    (afterX (initialBank F mX mY) row col mX)
    (afterY (initialBank F mX mY) row col mX mY)
    t0123 (2*mY+2) (by simpa only [prog0123, start0123] using h0123)
    (y_run F mX mY row col)
  exact ⟨t, by dsimp [transferClock]; omega,
    by simpa only [transferProgram, transferStart, readyBank] using h⟩

theorem ready_sample (F : CompilerStack → List Bool) (mX mY : Nat)
    (row col : Code) :
    (fun k : SampleStack => readyBank F mX mY row col (sample k)) =
      CodeSampleAssembly.initial mX mY row col := by
  have hempty (k : SampleStack) :
      initialBank F mX mY (.inr (.inl k)) = [] :=
    sample_empty F mX mY k
  funext k
  fin_cases k <;>
    simp [readyBank, afterY, afterX, seedBank, afterCol, afterRow,
      CodeSampleAssembly.initial, sample, sampleSlots,
      hempty]

#print axioms row_run
#print axioms col_run
#print axioms x_run
#print axioms y_run
#print axioms transfer_run
#print axioms ready_sample

end Paper2.CodeGeneratorSampleTransfer
