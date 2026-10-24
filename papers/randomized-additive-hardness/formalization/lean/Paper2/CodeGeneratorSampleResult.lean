import Paper2.CodeGeneratorSampleJoin

/-! Exact encoded output and public-count retention for the single fixed
compiler-plus-assembler program. -/

set_option maxHeartbeats 1000000

namespace Paper2.CodeGeneratorSampleResult

open Turing
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.CodeGeneratorSampleJoin
open Paper2.CodeGeneratorSampleTransfer

private theorem countX_retained (F : CompilerStack → List Bool)
    (mX mY : Nat) (row col : Code) :
    afterAssembly F mX mY row col countX = List.replicate mX true := by
  have hout : ¬ ∃ j : SampleStack, sampleSlots j = countX := by
    rintro ⟨j,h⟩; cases h
  rw [afterAssembly,
    EthInapproximability.CurrentPaper.BitMachineStackEmbedding.bank_outside
      sampleSlots (readyBank F mX mY row col) _ countX hout]
  simpa [readyBank, afterY, afterX, seedBank, afterCol, afterRow,
    sample, sampleSlots, countX] using
    CodeGeneratorSampleTransfer.countX_at F mX mY

private theorem countY_retained (F : CompilerStack → List Bool)
    (mX mY : Nat) (row col : Code) :
    afterAssembly F mX mY row col countY = List.replicate mY true := by
  have hout : ¬ ∃ j : SampleStack, sampleSlots j = countY := by
    rintro ⟨j,h⟩; cases h
  rw [afterAssembly,
    EthInapproximability.CurrentPaper.BitMachineStackEmbedding.bank_outside
      sampleSlots (readyBank F mX mY row col) _ countY hout]
  simpa [readyBank, afterY, afterX, seedBank, afterCol, afterRow,
    sample, sampleSlots, countY] using
    CodeGeneratorSampleTransfer.countY_at F mX mY

theorem run_output (n p s q₁ q₂ w Q k mX mY : Nat)
    (hs : 3 ≤ s) :
    ∃ t ≤ CodeGeneratorSampleJoin.clock n p s q₁ q₂ w Q k mX mY,
      let c := Paper2.GeneratorSource.seedRecursiveCodes
        n p s q₁ q₂ w Q k
      let F := (Paper2.CodeRecursiveLoop.finished n s q₁ q₂ w Q
        c.1 c.2).stk
      ((advance CodeGeneratorSampleJoin.program)^[t])
        (⟨some (EthInapproximability.CurrentPaper.BitMachineRawSequence.leftLabel
            (EthInapproximability.CurrentPaper.BitMachineRawSequence.leftLabel
              CodeGeneratorSampleJoin.compilerStart)),
          ((CodeGeneratorSampleJoin.compilerControl,
            CodeGeneratorSampleJoin.transferControl),
            CodeGeneratorSampleJoin.assemblyControl),
          CodeGeneratorSampleJoin.initial n p s q₁ q₂ w Q k mX mY⟩ :
          Turing.TM2.Cfg (fun _ : CodeGeneratorSampleJoin.Stack => Bool) _ _) =
        ⟨none,((CodeGeneratorSampleJoin.compilerControl,
          CodeGeneratorSampleJoin.transferControl),
          CodeGeneratorSampleJoin.assemblyControl),
          CodeGeneratorSampleJoin.afterAssembly F mX mY c.1 c.2⟩ ∧
      CodeGeneratorSampleJoin.afterAssembly F mX mY c.1 c.2
        (CodeGeneratorSampleTransfer.sample 10) =
          encodeCode (.append (copies mY c.2) (copies mX c.1)) ∧
      CodeGeneratorSampleJoin.afterAssembly F mX mY c.1 c.2 countX =
        List.replicate mX true ∧
      CodeGeneratorSampleJoin.afterAssembly F mX mY c.1 c.2 countY =
        List.replicate mY true := by
  obtain ⟨t,ht,hr⟩ := CodeGeneratorSampleJoin.run
    n p s q₁ q₂ w Q k mX mY hs
  refine ⟨t,ht,?_,?_,?_,?_⟩
  · simpa only [] using hr
  · exact CodeGeneratorSampleJoin.output_exact _ mX mY _ _
  · exact countX_retained _ mX mY _ _
  · exact countY_retained _ mX mY _ _

theorem clock_output_sensitive (n p s q₁ q₂ w Q k mX mY : Nat) :
    let c := Paper2.GeneratorSource.seedRecursiveCodes n p s q₁ q₂ w Q k
    CodeGeneratorSampleJoin.clock n p s q₁ q₂ w Q k mX mY ≤
      Paper2.CodeGeneratorComplete.clock n p s q₁ q₂ w Q k +
        CodeGeneratorSampleTransfer.transferClock mX mY c.1 c.2 +
        64*(mX+mY+codeSize c.1+codeSize c.2+2)^2 + 2 := by
  let c := Paper2.GeneratorSource.seedRecursiveCodes n p s q₁ q₂ w Q k
  have h := Paper2.CodeSampleAssembly.clock_polynomial
    mX mY c.1 c.2
  change Paper2.CodeGeneratorComplete.clock n p s q₁ q₂ w Q k +
    CodeGeneratorSampleTransfer.transferClock mX mY c.1 c.2 +
    Paper2.CodeSampleAssembly.clock mX mY c.1 c.2 + 2 ≤
      Paper2.CodeGeneratorComplete.clock n p s q₁ q₂ w Q k +
        CodeGeneratorSampleTransfer.transferClock mX mY c.1 c.2 +
        64*(mX+mY+codeSize c.1+codeSize c.2+2)^2 + 2
  omega

#print axioms run_output
#print axioms clock_output_sensitive

end Paper2.CodeGeneratorSampleResult
