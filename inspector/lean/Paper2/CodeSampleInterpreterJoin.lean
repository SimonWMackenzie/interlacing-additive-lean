import Paper2.CodeSampleInterpreterLoader

/-! One fixed public-count compiler/sample-syntax table followed by a
physical code-input copy to the first-order interpreter bank. -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

namespace Paper2.CodeSampleInterpreterJoin

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.CodeSampleInterpreterLoader

abbrev Stack := CodeSampleInterpreterLoader.Stack

noncomputable def sampleProgram := fun l =>
  stackStmt sampleSlots (CodeGeneratorSampleJoin.program l)
def sampleControl :=
  ((CodeGeneratorSampleJoin.compilerControl,
      CodeGeneratorSampleJoin.transferControl),
    CodeGeneratorSampleJoin.assemblyControl)
def copyControl : Option Bool := none

noncomputable def program :=
  BitMachineRawSequence.program sampleProgram copyProgram
    (BitMachineCopy.Label.scan) sampleControl copyControl

noncomputable def initial (n p s q₁ q₂ w Q k mX mY : Nat)
    (tape : List Bool) (B R : Nat) : Stack → List Bool :=
  initialBank (CodeGeneratorSampleJoin.initial n p s q₁ q₂ w Q k mX mY)
    tape B R

noncomputable def finalBank (n s q₁ q₂ w Q k mX mY : Nat)
    (row col : Code) (tape : List Bool) (B R : Nat) : Stack → List Bool :=
  loadedBank
    (CodeGeneratorSampleJoin.afterAssembly
      (CodeRecursiveLoop.finished n s q₁ q₂ w Q row col).stk
      mX mY row col) tape B R
    (.append (copies mY col) (copies mX row))

noncomputable def clock (n p s q₁ q₂ w Q k mX mY : Nat) : Nat :=
  let c := GeneratorSource.seedRecursiveCodes n p s q₁ q₂ w Q k
  let root : Code := .append (copies mY c.2) (copies mX c.1)
  CodeGeneratorSampleJoin.clock n p s q₁ q₂ w Q k mX mY +
    2*(encodeCode root).length+2+1

theorem sample_run (n p s q₁ q₂ w Q k mX mY : Nat)
    (tape : List Bool) (B R : Nat) (hs : 3 ≤ s) :
    ∃ t ≤ CodeGeneratorSampleJoin.clock n p s q₁ q₂ w Q k mX mY,
      let c := GeneratorSource.seedRecursiveCodes n p s q₁ q₂ w Q k
      ((advance sampleProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel CodeGeneratorSampleJoin.compilerStart)),
          sampleControl,
          initial n p s q₁ q₂ w Q k mX mY tape B R⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,sampleControl,
          initialBank
            (CodeGeneratorSampleJoin.afterAssembly
              (CodeRecursiveLoop.finished n s q₁ q₂ w Q c.1 c.2).stk
              mX mY c.1 c.2) tape B R⟩ := by
  obtain ⟨t,ht,hr⟩ := CodeGeneratorSampleJoin.run
    n p s q₁ q₂ w Q k mX mY hs
  have h := BitMachineStackRun.run sampleSlots (foreign tape B R)
    CodeGeneratorSampleJoin.program
    (⟨some (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel CodeGeneratorSampleJoin.compilerStart)),
      sampleControl,
      CodeGeneratorSampleJoin.initial n p s q₁ q₂ w Q k mX mY⟩ :
        TM2.Cfg (fun _ : SampleStack => Bool) _ _) t
  change ((advance CodeGeneratorSampleJoin.program)^[t])
    (⟨some (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel CodeGeneratorSampleJoin.compilerStart)),
      sampleControl,
      CodeGeneratorSampleJoin.initial n p s q₁ q₂ w Q k mX mY⟩ :
      TM2.Cfg (fun _ : SampleStack => Bool) _ _) = _ at hr
  rw [hr] at h
  exact ⟨t,ht,by
    simpa only [sampleProgram, initial, initialBank, stackCfg]
      using h⟩

theorem run (n p s q₁ q₂ w Q k mX mY : Nat)
    (tape : List Bool) (B R : Nat) (hs : 3 ≤ s) :
    ∃ t ≤ clock n p s q₁ q₂ w Q k mX mY,
      let c := GeneratorSource.seedRecursiveCodes n p s q₁ q₂ w Q k
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel CodeGeneratorSampleJoin.compilerStart))),
          (sampleControl,copyControl),
          initial n p s q₁ q₂ w Q k mX mY tape B R⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,(sampleControl,copyControl),
          finalBank n s q₁ q₂ w Q k mX mY c.1 c.2 tape B R⟩ := by
  let c := GeneratorSource.seedRecursiveCodes n p s q₁ q₂ w Q k
  let root : Code := .append (copies mY c.2) (copies mX c.1)
  let S := CodeGeneratorSampleJoin.afterAssembly
    (CodeRecursiveLoop.finished n s q₁ q₂ w Q c.1 c.2).stk mX mY c.1 c.2
  obtain ⟨ts,hts,hsr⟩ := sample_run n p s q₁ q₂ w Q k mX mY
    tape B R hs
  have hout : S (CodeGeneratorSampleTransfer.sample 10) =
      encodeCode root := CodeGeneratorSampleJoin.output_exact _ mX mY c.1 c.2
  have hc := copy_run S tape B R root hout
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    sampleProgram copyProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel CodeGeneratorSampleJoin.compilerStart)) .scan
    sampleControl sampleControl copyControl copyControl
    (initial n p s q₁ q₂ w Q k mX mY tape B R)
    (initialBank S tape B R) (loadedBank S tape B R root)
    ts (2*(encodeCode root).length+2) hsr hc
  exact ⟨t,by
    change t ≤ CodeGeneratorSampleJoin.clock n p s q₁ q₂ w Q k mX mY +
      2*(encodeCode root).length+2+1
    omega,
    by simpa only [program, finalBank, S, root, c] using hr⟩

#print axioms sample_run
#print axioms run

end Paper2.CodeSampleInterpreterJoin
