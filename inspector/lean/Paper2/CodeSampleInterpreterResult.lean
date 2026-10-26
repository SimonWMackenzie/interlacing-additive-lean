import Paper2.CodeSampleInterpreterJoin
import Paper2.CodeGeneratorSampleResult

/-! Final exact-bank interface of the physical sample syntax loader. -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

namespace Paper2.CodeSampleInterpreterResult

open Turing
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSerialization

theorem run_ready (n p s q₁ q₂ w Q k mX mY : Nat)
    (tape : List Bool) (B R : Nat) (hs : 3 ≤ s) :
    ∃ t ≤ CodeSampleInterpreterJoin.clock n p s q₁ q₂ w Q k mX mY,
      let c := GeneratorSource.seedRecursiveCodes n p s q₁ q₂ w Q k
      let root : Code := .append (copies mY c.2) (copies mX c.1)
      let S := CodeSampleInterpreterJoin.finalBank n s q₁ q₂ w Q k mX mY
        c.1 c.2 tape B R
      ((advance CodeSampleInterpreterJoin.program)^[t])
        (⟨some (EthInapproximability.CurrentPaper.BitMachineRawSequence.leftLabel
            (EthInapproximability.CurrentPaper.BitMachineRawSequence.leftLabel
              (EthInapproximability.CurrentPaper.BitMachineRawSequence.leftLabel
                CodeGeneratorSampleJoin.compilerStart))),
          (CodeSampleInterpreterJoin.sampleControl,
            CodeSampleInterpreterJoin.copyControl),
          CodeSampleInterpreterJoin.initial n p s q₁ q₂ w Q k mX mY
            tape B R⟩ :
          Turing.TM2.Cfg (fun _ : CodeSampleInterpreterJoin.Stack => Bool) _ _) =
        ⟨none,(CodeSampleInterpreterJoin.sampleControl,
          CodeSampleInterpreterJoin.copyControl),S⟩ ∧
      (fun j => S (CodeSampleInterpreterLoader.consumerSlots j)) =
        (CodeFullPadding.start (GeneratorCode.initial root) tape B R).stk ∧
      S (CodeSampleInterpreterLoader.sampleSlots
        CodeGeneratorSampleTransfer.countX) = List.replicate mX true ∧
      S (CodeSampleInterpreterLoader.sampleSlots
        CodeGeneratorSampleTransfer.countY) = List.replicate mY true := by
  let c := GeneratorSource.seedRecursiveCodes n p s q₁ q₂ w Q k
  let root : Code := .append (copies mY c.2) (copies mX c.1)
  let F := (CodeRecursiveLoop.finished n s q₁ q₂ w Q c.1 c.2).stk
  let A := CodeGeneratorSampleJoin.afterAssembly F mX mY c.1 c.2
  obtain ⟨t,ht,hr⟩ := CodeSampleInterpreterJoin.run
    n p s q₁ q₂ w Q k mX mY tape B R hs
  obtain ⟨_,_,_,_,hx,hy⟩ := CodeGeneratorSampleResult.run_output
    n p s q₁ q₂ w Q k mX mY hs
  refine ⟨t,ht,?_,?_,?_,?_⟩
  · simpa only [c] using hr
  · exact CodeSampleInterpreterLoader.loaded_consumer_bank A tape B R root
  · exact (CodeSampleInterpreterLoader.sample_retained A tape B R root
      CodeGeneratorSampleTransfer.countX).trans hx
  · exact (CodeSampleInterpreterLoader.sample_retained A tape B R root
      CodeGeneratorSampleTransfer.countY).trans hy

#print axioms run_ready

end Paper2.CodeSampleInterpreterResult
