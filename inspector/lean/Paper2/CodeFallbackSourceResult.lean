import Paper2.CodeFallbackFullJoin

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

namespace Paper2.CodeFallbackSourceResult

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.GeneratorStateSize

def sampleRoot (n p s q₁ q₂ w Q k mX mY : Nat) : Code :=
  let c := GeneratorSource.seedRecursiveCodes n p s q₁ q₂ w Q k
  .append (copies mY c.2) (copies mX c.1)

abbrev Stack := CodeFallbackFullJoin.Stack

noncomputable def finalBank (n p s q₁ q₂ w Q k mX mY : Nat)
    (tape : List Bool) (B R : Nat) (d : CodeTableFallback.Config) :=
  let c := GeneratorSource.seedRecursiveCodes n p s q₁ q₂ w Q k
  bank CodeFallbackEntryBank.fallbackSlots
    (CodeFallbackEntryJoin.finalBank n s q₁ q₂ w Q k mX mY
      c.1 c.2 tape B R) d.stk

theorem source_success (n p s q₁ q₂ w Q k mX mY M B R N : Nat)
    (hs : 3 ≤ s)
    (hM : (meaning (sampleRoot n p s q₁ q₂ w Q k mX mY)).maxAlphabet ≤ M)
    (hMB : Nat.clog 2 M ≤ B) (hR : 0 < R)
    (hp : GeneratorPositive.Positive (sampleRoot n p s q₁ q₂ w Q k mX mY))
    (tape : CappedSampler.Adaptive.Tape B R N) (bytes : List Bool)
    (hr : GeneratorCode.run B R hMB N
      (initialBounded (sampleRoot n p s q₁ q₂ w Q k mX mY) hM)
      tape = some bytes) :
    ∃ (clock : Nat) (d : CodeFullPadding.Config),
      clock ≤ CodeFallbackEntryJoin.clock n p s q₁ q₂ w Q k mX mY +
        (codeSize (sampleRoot n p s q₁ q₂ w Q k mX mY)+1) *
          CodeFullRepeatPublic.repeatStepCap
            (sampleRoot n p s q₁ q₂ w Q k mX mY) B R + N*(R*B)+4 ∧
      CodeFullRun.observed d = some bytes ∧
      d.stk CodeFullPadding.tapeSlot = [] ∧
      ((advance CodeFallbackFullJoin.program)^[clock])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel
                  (BitMachineRawSequence.leftLabel
                    (BitMachineRawSequence.leftLabel
                      CodeGeneratorSampleJoin.compilerStart)))))),
          (CodeFallbackFullJoin.prepControl,CodeFallbackFullJoin.fallbackControl),
          CodeFallbackEntryJoin.initial n p s q₁ q₂ w Q k mX mY
            (RecursiveSamplingTape.writeTape B R N tape).val B R⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,
          (CodeFallbackFullJoin.prepControl,
            CodeTableFallback.embedInterpreter d.var),
          finalBank n p s q₁ q₂ w Q k mX mY
            (RecursiveSamplingTape.writeTape B R N tape).val B R
            ⟨none,CodeTableFallback.embedInterpreter d.var,
              Sum.elim d.stk
                (CodeTableFallback.writerData mX mY).contents⟩⟩ := by
  let root := sampleRoot n p s q₁ q₂ w Q k mX mY
  let word := (RecursiveSamplingTape.writeTape B R N tape).val
  obtain ⟨t,ht,hd,hobs,htape⟩ :=
    CodeFullRunConsumer.run_some_physical root M B R N hMB hR
      (initialBounded root hM)
      (GeneratorPositive.positive_initial root hp)
      GeneratorStateSize.Trace.initial tape bytes hr
  let d := CodeFullPadding.run t
    (CodeFullPadding.start (GeneratorCode.initial root) word B R)
  have hd' : d.l = none := by simpa [d,root,word] using hd
  have hobs' : CodeFullRun.observed d = some bytes := by
    simpa [d,root,word] using hobs
  have htape' : d.stk CodeFullPadding.tapeSlot = [] := by
    simpa [d,root,word] using htape
  have hs' := CodeTableFallback.observed_some_status d bytes hobs'
  obtain ⟨tf,htf,hf⟩ := CodeTableFallback.success_from_initial
    (GeneratorCode.initial root) word B R mX mY t d rfl hd' hs'
  let fd : CodeTableFallback.Config :=
    ⟨none,CodeTableFallback.embedInterpreter d.var,
      Sum.elim d.stk (CodeTableFallback.writerData mX mY).contents⟩
  have hf' : CodeTableFallback.run tf
      (CodeTableFallback.initial (GeneratorCode.initial root)
        word B R mX mY) = fd := by simpa only [fd] using hf
  obtain ⟨u,hu,hrun⟩ := CodeFallbackFullJoin.run_from_fallback
    n p s q₁ q₂ w Q k mX mY word B R hs tf fd
    (by simpa only [sampleRoot] using hf') rfl
  refine ⟨u,d,?_,hobs',htape',?_⟩
  · have ht' : t ≤ (codeSize (sampleRoot n p s q₁ q₂ w Q k mX mY)+1) *
        CodeFullRepeatPublic.repeatStepCap
          (sampleRoot n p s q₁ q₂ w Q k mX mY) B R + N*(R*B)+2 := by
      simpa only [root] using ht
    omega
  · simpa only [finalBank,fd] using hrun

theorem source_failure (n p s q₁ q₂ w Q k mX mY M B R N : Nat)
    (hs : 3 ≤ s)
    (hM : (meaning (sampleRoot n p s q₁ q₂ w Q k mX mY)).maxAlphabet ≤ M)
    (hMB : Nat.clog 2 M ≤ B) (hR : 0 < R)
    (hp : GeneratorPositive.Positive (sampleRoot n p s q₁ q₂ w Q k mX mY))
    (hN : (meaning (sampleRoot n p s q₁ q₂ w Q k mX mY)).maxDraws ≤ N)
    (tape : CappedSampler.Adaptive.Tape B R N)
    (hr : GeneratorCode.run B R hMB N
      (initialBounded (sampleRoot n p s q₁ q₂ w Q k mX mY) hM)
      tape = none) :
    ∃ (clock : Nat) (d : CodeFullPadding.Config)
      (wc : CodeTableFallback.WriterControl),
      clock ≤ CodeFallbackEntryJoin.clock n p s q₁ q₂ w Q k mX mY +
        CodeTableFallback.sourceFailureCap
          (sampleRoot n p s q₁ q₂ w Q k mX mY) B R mX mY + 1 ∧
      ((advance CodeFallbackFullJoin.program)^[clock])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel
                  (BitMachineRawSequence.leftLabel
                    (BitMachineRawSequence.leftLabel
                      CodeGeneratorSampleJoin.compilerStart)))))),
          (CodeFallbackFullJoin.prepControl,CodeFallbackFullJoin.fallbackControl),
          CodeFallbackEntryJoin.initial n p s q₁ q₂ w Q k mX mY
            (RecursiveSamplingTape.writeTape B R N tape).val B R⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,
          (CodeFallbackFullJoin.prepControl,CodeTableFallback.embedWriter wc),
          finalBank n p s q₁ q₂ w Q k mX mY
            (RecursiveSamplingTape.writeTape B R N tape).val B R
            ⟨none,CodeTableFallback.embedWriter wc,
              Sum.elim (Function.update d.stk CodeHeaderDraw.output [])
                (MatrixTableWriter.ready CodeTableFallback.emptyBank mX mY
                  0 0 0 0 []
                  (MatrixMaterialization.rowMajor
                    (fun (_ : Fin mX) (_ : Fin mY) => false))).contents⟩⟩ := by
  let root := sampleRoot n p s q₁ q₂ w Q k mX mY
  let word := (RecursiveSamplingTape.writeTape B R N tape).val
  have hN' : (GeneratorCode.semantic
      (initialBounded root hM)).val.maxDraws ≤ N := by
    rw [CodeFullRunConsumer.initial_semantic_draws]
    exact hN
  obtain ⟨tf,htf,d,wc,hf,_⟩ := CodeTableFallback.source_run_failure_public
    root M B R N mX mY hMB hR
    (initialBounded root hM)
    (GeneratorPositive.positive_initial root hp)
    GeneratorStateSize.Trace.initial hN' tape hr
  let fd : CodeTableFallback.Config :=
    ⟨none,CodeTableFallback.embedWriter wc,
      Sum.elim (Function.update d.stk CodeHeaderDraw.output [])
        (MatrixTableWriter.ready CodeTableFallback.emptyBank mX mY
          0 0 0 0 []
          (MatrixMaterialization.rowMajor
            (fun (_ : Fin mX) (_ : Fin mY) => false))).contents⟩
  have hf' : CodeTableFallback.run tf
      (CodeTableFallback.initial (GeneratorCode.initial root)
        word B R mX mY) = fd := by simpa only [fd,word,root] using hf
  obtain ⟨u,hu,hrun⟩ := CodeFallbackFullJoin.run_from_fallback
    n p s q₁ q₂ w Q k mX mY word B R hs tf fd
    (by simpa only [sampleRoot] using hf') rfl
  refine ⟨u,d,wc,?_,?_⟩
  · have htf' : tf ≤ CodeTableFallback.sourceFailureCap
        (sampleRoot n p s q₁ q₂ w Q k mX mY) B R mX mY := by
      simpa only [root] using htf
    omega
  · simpa only [finalBank,fd] using hrun

#print axioms source_success
#print axioms source_failure

end Paper2.CodeFallbackSourceResult
