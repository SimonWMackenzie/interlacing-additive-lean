import CurrentAdditive.V39DeadSampleJoin

/-! Exact encoded output and public-count retention for the single fixed
compiler-plus-assembler program. -/

set_option maxHeartbeats 1000000

namespace CurrentAdditive.V39DeadSampleResult

open Paper2

open Turing
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open CurrentAdditive.V39DeadSampleJoin
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
    ∃ t ≤ V39DeadSampleJoin.clock n p s q₁ q₂ w Q k mX mY,
      let c := CurrentAdditive.V39DeadCodeComplete.seedRecursiveCodes
        n p s q₁ q₂ w Q k
      let F := (CurrentAdditive.V39DeadCodeLoop.finished n s q₁ q₂ w Q
        c.1 c.2).stk
      ((advance V39DeadSampleJoin.program)^[t])
        (⟨some (EthInapproximability.CurrentPaper.BitMachineRawSequence.leftLabel
            (EthInapproximability.CurrentPaper.BitMachineRawSequence.leftLabel
              V39DeadSampleJoin.compilerStart)),
          ((V39DeadSampleJoin.compilerControl,
            V39DeadSampleJoin.transferControl),
            V39DeadSampleJoin.assemblyControl),
          V39DeadSampleJoin.initial n p s q₁ q₂ w Q k mX mY⟩ :
          Turing.TM2.Cfg (fun _ : V39DeadSampleJoin.Stack => Bool) _ _) =
        ⟨none,((V39DeadSampleJoin.compilerControl,
          V39DeadSampleJoin.transferControl),
          V39DeadSampleJoin.assemblyControl),
          V39DeadSampleJoin.afterAssembly F mX mY c.1 c.2⟩ ∧
      V39DeadSampleJoin.afterAssembly F mX mY c.1 c.2
        (CodeGeneratorSampleTransfer.sample 10) =
          encodeCode (.append (copies mX c.1) (copies mY c.2)) ∧
      V39DeadSampleJoin.afterAssembly F mX mY c.1 c.2 countX =
        List.replicate mX true ∧
      V39DeadSampleJoin.afterAssembly F mX mY c.1 c.2 countY =
        List.replicate mY true := by
  obtain ⟨t,ht,hr⟩ := V39DeadSampleJoin.run
    n p s q₁ q₂ w Q k mX mY hs
  refine ⟨t,ht,?_,?_,?_,?_⟩
  · simpa only [] using hr
  · exact V39DeadSampleJoin.output_exact _ mX mY _ _
  · exact countX_retained _ mX mY _ _
  · exact countY_retained _ mX mY _ _

theorem clock_output_sensitive (n p s q₁ q₂ w Q k mX mY : Nat) :
    let c := CurrentAdditive.V39DeadCodeComplete.seedRecursiveCodes n p s q₁ q₂ w Q k
    V39DeadSampleJoin.clock n p s q₁ q₂ w Q k mX mY ≤
      CurrentAdditive.V39DeadCodeComplete.clock n p s q₁ q₂ w Q k +
        CodeGeneratorSampleTransfer.transferClock mX mY c.1 c.2 +
        64*(mX+mY+codeSize c.1+codeSize c.2+2)^2 + 2 := by
  let c := CurrentAdditive.V39DeadCodeComplete.seedRecursiveCodes n p s q₁ q₂ w Q k
  have h := CurrentAdditive.V39DeadSampleAssembly.clock_polynomial
    mX mY c.1 c.2
  change CurrentAdditive.V39DeadCodeComplete.clock n p s q₁ q₂ w Q k +
    CodeGeneratorSampleTransfer.transferClock mX mY c.1 c.2 +
    CurrentAdditive.V39DeadSampleAssembly.clock mX mY c.1 c.2 + 2 ≤
      CurrentAdditive.V39DeadCodeComplete.clock n p s q₁ q₂ w Q k +
        CodeGeneratorSampleTransfer.transferClock mX mY c.1 c.2 +
        64*(mX+mY+codeSize c.1+codeSize c.2+2)^2 + 2
  omega

#print axioms run_output
#print axioms clock_output_sensitive

end CurrentAdditive.V39DeadSampleResult
