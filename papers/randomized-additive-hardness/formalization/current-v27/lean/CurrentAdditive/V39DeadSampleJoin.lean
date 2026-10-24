import Paper2.CodeGeneratorSampleTransfer
import CurrentAdditive.V39DeadCodeComplete
import CurrentAdditive.V39DeadSampleAssembly

/-! Actual public-count code compilation followed by physical row-first
sample-code assembly. This builds syntax only, not a sampled table. -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

namespace CurrentAdditive.V39DeadSampleJoin

open Paper2

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.CodeGeneratorSampleTransfer

abbrev Stack := CodeGeneratorSampleTransfer.Stack

noncomputable def compilerProgram := fun l =>
  stackStmt compilerSlots (CurrentAdditive.V39DeadCodeComplete.program l)
noncomputable def assemblyProgram := fun l =>
  stackStmt sampleSlots (CurrentAdditive.V39DeadSampleAssembly.program l)

def compilerStart := BitMachineRawSequence.leftLabel
  (LB := CurrentAdditive.V39DeadCodeLoop.Label)
  CurrentAdditive.V39DeadCodeComplete.seedStart
def compilerControl :=
  (CurrentAdditive.V39DeadCodeComplete.seedControl,
    CurrentAdditive.V39DeadCodeComplete.loopControl)
def transferControl :
    ((((Option Bool × Option Bool) × Unit) × Option Bool) × Option Bool) :=
  ((((none,none),()),none),none)
def assemblyControl : ((Option Bool × Option Bool) × Option Bool) :=
  ((none,none),none)

noncomputable def initial (n p s q₁ q₂ w Q k mX mY : Nat) :
    Stack → List Bool :=
  initialBank
    (Paper2.CodeRecursiveSeedPrep.publicBase n s q₁ q₂ w Q p
      (List.replicate k true)) mX mY

private theorem finished_row (n s q₁ q₂ w Q : Nat) (row col : Code) :
    (CurrentAdditive.V39DeadCodeLoop.finished n s q₁ q₂ w Q row col).stk 2 =
      encodeCode row := by
  change bank CurrentAdditive.V39DeadCodeLoop.embedRound
    (CurrentAdditive.V39DeadCodeLoop.foreign [])
    (Paper2.CodeRecursiveColumn.initial n s q₁ q₂ w Q row col)
    (CurrentAdditive.V39DeadCodeLoop.embedRound 2) = _
  rw [bank_at]
  rw [CurrentAdditive.V39DeadCodeInitialLayout.initial_core_at
    n s q₁ q₂ w Q row col 2 (by decide)]
  exact Paper2.CodeRowsGraphCompiler.initial_child n s q₁ q₂ row

private theorem finished_col (n s q₁ q₂ w Q : Nat) (row col : Code) :
    (CurrentAdditive.V39DeadCodeLoop.finished n s q₁ q₂ w Q row col).stk 33 =
      encodeCode col := by
  change bank CurrentAdditive.V39DeadCodeLoop.embedRound
    (CurrentAdditive.V39DeadCodeLoop.foreign [])
    (Paper2.CodeRecursiveColumn.initial n s q₁ q₂ w Q row col)
    (CurrentAdditive.V39DeadCodeLoop.embedRound 33) = _
  rw [bank_at]
  rw [Paper2.CodeRecursiveColumn.initial,
    Paper2.CodeRecursiveColumn.foreign_at w Q col _ 33 (by decide)]
  simp [Paper2.CodeRecursiveColumn.foreignWords]

theorem compiler_run (n p s q₁ q₂ w Q k mX mY : Nat)
    (hs : 3 ≤ s) :
    ∃ t ≤ CurrentAdditive.V39DeadCodeComplete.clock n p s q₁ q₂ w Q k,
      ((advance compilerProgram)^[t])
        (⟨some compilerStart,compilerControl,
          initial n p s q₁ q₂ w Q k mX mY⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,compilerControl,
          initialBank
            (CurrentAdditive.V39DeadCodeLoop.finished n s q₁ q₂ w Q
              (CurrentAdditive.V39DeadCodeComplete.seedRecursiveCodes
                n p s q₁ q₂ w Q k).1
              (CurrentAdditive.V39DeadCodeComplete.seedRecursiveCodes
                n p s q₁ q₂ w Q k).2).stk mX mY⟩ := by
  obtain ⟨t,ht,hr⟩ :=
    CurrentAdditive.V39DeadCodeComplete.run_seedRecursiveCodes
      n p s q₁ q₂ w Q k hs
  have he := BitMachineStackRun.run compilerSlots (foreign mX mY)
    CurrentAdditive.V39DeadCodeComplete.program
    (⟨some compilerStart,compilerControl,
      Paper2.CodeRecursiveSeedPrep.publicBase n s q₁ q₂ w Q p
        (List.replicate k true)⟩ :
          TM2.Cfg (fun _ : CompilerStack => Bool) _ _) t
  change ((advance CurrentAdditive.V39DeadCodeComplete.program)^[t])
    (⟨some compilerStart,compilerControl,
      Paper2.CodeRecursiveSeedPrep.publicBase n s q₁ q₂ w Q p
        (List.replicate k true)⟩ :
        TM2.Cfg (fun _ : CompilerStack => Bool) _ _) =
    ⟨none,compilerControl,
      (CurrentAdditive.V39DeadCodeLoop.finished n s q₁ q₂ w Q
        (CurrentAdditive.V39DeadCodeComplete.seedRecursiveCodes n p s q₁ q₂ w Q k).1
        (CurrentAdditive.V39DeadCodeComplete.seedRecursiveCodes n p s q₁ q₂ w Q k).2).stk⟩ at hr
  rw [hr] at he
  exact ⟨t,ht,by
    simpa only [compilerProgram, initial, initialBank, stackCfg] using he⟩

noncomputable def afterAssembly (F : CompilerStack → List Bool)
    (mX mY : Nat) (row col : Code) : Stack → List Bool :=
  bank sampleSlots (readyBank F mX mY row col)
    (V39DeadSampleAssembly.final mX mY row col)

theorem assembly_run (F : CompilerStack → List Bool) (mX mY : Nat)
    (row col : Code) :
    ∃ t ≤ V39DeadSampleAssembly.clock mX mY row col,
      ((advance assemblyProgram)^[t])
        (⟨some V39DeadSampleAssembly.startLabel,assemblyControl,
          readyBank F mX mY row col⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,assemblyControl,afterAssembly F mX mY row col⟩ := by
  obtain ⟨t,ht,hr⟩ := V39DeadSampleAssembly.run mX mY row col
  have hbase : bank sampleSlots (readyBank F mX mY row col)
      (V39DeadSampleAssembly.initial mX mY row col) =
      readyBank F mX mY row col :=
    bank_eq_self sampleSlots _ _
      (fun j => (congrFun (ready_sample F mX mY row col) j).symm)
  have he := BitMachineStackRun.run sampleSlots
    (readyBank F mX mY row col) V39DeadSampleAssembly.program
    (⟨some V39DeadSampleAssembly.startLabel,assemblyControl,
      V39DeadSampleAssembly.initial mX mY row col⟩ :
        TM2.Cfg (fun _ : SampleStack => Bool) _ _) t
  change ((advance V39DeadSampleAssembly.program)^[t])
    (⟨some V39DeadSampleAssembly.startLabel,assemblyControl,
      V39DeadSampleAssembly.initial mX mY row col⟩ :
        TM2.Cfg (fun _ : SampleStack => Bool) _ _) =
    ⟨none,assemblyControl,V39DeadSampleAssembly.final mX mY row col⟩ at hr
  rw [hr] at he
  exact ⟨t,ht,by
    simpa only [assemblyProgram, assemblyControl,
      hbase, afterAssembly, stackCfg] using he⟩

def transferStart := CodeGeneratorSampleTransfer.transferStart
noncomputable def compiledTransferProgram :=
  BitMachineRawSequence.program compilerProgram transferProgram
    transferStart compilerControl transferControl
noncomputable def program :=
  BitMachineRawSequence.program compiledTransferProgram assemblyProgram
    V39DeadSampleAssembly.startLabel (compilerControl,transferControl)
    assemblyControl

noncomputable def clock (n p s q₁ q₂ w Q k mX mY : Nat) : Nat :=
  let c := CurrentAdditive.V39DeadCodeComplete.seedRecursiveCodes n p s q₁ q₂ w Q k
  CurrentAdditive.V39DeadCodeComplete.clock n p s q₁ q₂ w Q k +
    CodeGeneratorSampleTransfer.transferClock mX mY c.1 c.2 +
    V39DeadSampleAssembly.clock mX mY c.1 c.2 + 2

/-- One fixed program from raw seven compiler counts, raw k fuel, and raw
sample counts to the complete row-first encoded sample syntax. -/
theorem run (n p s q₁ q₂ w Q k mX mY : Nat) (hs : 3 ≤ s) :
    ∃ t ≤ clock n p s q₁ q₂ w Q k mX mY,
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel compilerStart)),
          ((compilerControl,transferControl),assemblyControl),
          initial n p s q₁ q₂ w Q k mX mY⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,((compilerControl,transferControl),assemblyControl),
          afterAssembly
            (CurrentAdditive.V39DeadCodeLoop.finished n s q₁ q₂ w Q
              (CurrentAdditive.V39DeadCodeComplete.seedRecursiveCodes
                n p s q₁ q₂ w Q k).1
              (CurrentAdditive.V39DeadCodeComplete.seedRecursiveCodes
                n p s q₁ q₂ w Q k).2).stk mX mY
            (CurrentAdditive.V39DeadCodeComplete.seedRecursiveCodes
              n p s q₁ q₂ w Q k).1
            (CurrentAdditive.V39DeadCodeComplete.seedRecursiveCodes
              n p s q₁ q₂ w Q k).2⟩ := by
  let c := CurrentAdditive.V39DeadCodeComplete.seedRecursiveCodes n p s q₁ q₂ w Q k
  let F := (CurrentAdditive.V39DeadCodeLoop.finished n s q₁ q₂ w Q c.1 c.2).stk
  obtain ⟨tc,htc,hc⟩ := compiler_run n p s q₁ q₂ w Q k mX mY hs
  obtain ⟨tt,htt,ht⟩ := CodeGeneratorSampleTransfer.transfer_run
    F mX mY c.1 c.2
    (finished_row n s q₁ q₂ w Q c.1 c.2)
    (finished_col n s q₁ q₂ w Q c.1 c.2)
  obtain ⟨ta,hta,ha⟩ := assembly_run F mX mY c.1 c.2
  obtain ⟨tct,htct,hct⟩ := BitMachineRawSequence.runs
    compilerProgram transferProgram compilerStart transferStart
    compilerControl compilerControl transferControl transferControl
    (initial n p s q₁ q₂ w Q k mX mY) (initialBank F mX mY)
    (readyBank F mX mY c.1 c.2) tc tt
    (by simpa only [F, c] using hc)
    (by simpa only [F, c] using ht)
  obtain ⟨t,httot,h⟩ := BitMachineRawSequence.runs
    compiledTransferProgram assemblyProgram
    (BitMachineRawSequence.leftLabel compilerStart)
    V39DeadSampleAssembly.startLabel
    (compilerControl,transferControl) (compilerControl,transferControl)
    assemblyControl assemblyControl
    (initial n p s q₁ q₂ w Q k mX mY)
    (readyBank F mX mY c.1 c.2) (afterAssembly F mX mY c.1 c.2)
    tct ta (by simpa only [compiledTransferProgram] using hct) ha
  exact ⟨t, by
    change t ≤ CurrentAdditive.V39DeadCodeComplete.clock n p s q₁ q₂ w Q k +
      CodeGeneratorSampleTransfer.transferClock mX mY c.1 c.2 +
      V39DeadSampleAssembly.clock mX mY c.1 c.2 + 2
    omega,
    by simpa only [program, F, c] using h⟩

theorem output_exact (F : CompilerStack → List Bool) (mX mY : Nat)
    (row col : Code) :
    afterAssembly F mX mY row col (sample 10) =
      encodeCode (.append (copies mX row) (copies mY col)) := by
  exact (bank_at sampleSlots (readyBank F mX mY row col)
    (V39DeadSampleAssembly.final mX mY row col) 10).trans
    (V39DeadSampleAssembly.output_exact mX mY row col)

#print axioms run
#print axioms output_exact

end CurrentAdditive.V39DeadSampleJoin
