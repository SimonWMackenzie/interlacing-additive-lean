import Paper2.CodeFallbackSourceResult

/-! The actual raw-count controller halts on every supplied capped random tape.
The result predicate keeps the exact success-word and physical failure-table
conclusions. No case choice or terminating-run premise is supplied. -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

namespace Paper2.CodeFallbackAllOutcomes

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.GeneratorStateSize Paper2.CodeFallbackSourceResult

private theorem failure_clock_le (clock prep failure success : Nat)
    (h : clock ≤ prep + failure + 1) :
    clock ≤ prep + max success (failure + 1) := by omega

private theorem success_clock_le (clock prep core tail failure : Nat)
    (h : clock ≤ prep + core + tail + 4) :
    clock ≤ prep + max (core + tail + 4) failure := by omega

def Outcome (mX mY : Nat) (result : Option (List Bool))
    (d : CodeTableFallback.Config) : Prop :=
  match result with
  | some bytes => ∃ a : CodeFullPadding.Config,
      d = ⟨none,CodeTableFallback.embedInterpreter a.var,
        Sum.elim a.stk (CodeTableFallback.writerData mX mY).contents⟩ ∧
      CodeFullRun.observed a = some bytes ∧
      a.stk CodeFullPadding.tapeSlot = []
  | none => ∃ (a : CodeFullPadding.Config) (wc : CodeTableFallback.WriterControl),
      d = ⟨none,CodeTableFallback.embedWriter wc,
        Sum.elim (Function.update a.stk CodeHeaderDraw.output [])
          (MatrixTableWriter.ready CodeTableFallback.emptyBank mX mY
            0 0 0 0 [] (MatrixMaterialization.rowMajor
              (fun (_ : Fin mX) (_ : Fin mY) => false))).contents⟩

def Runs (clock n p s q₁ q₂ w Q k mX mY : Nat)
    (tape : List Bool) (B R : Nat) (d : CodeTableFallback.Config) : Prop :=
  ((advance CodeFallbackFullJoin.program)^[clock])
    (⟨some (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel
                  CodeGeneratorSampleJoin.compilerStart)))))),
      (CodeFallbackFullJoin.prepControl,CodeFallbackFullJoin.fallbackControl),
      CodeFallbackEntryJoin.initial n p s q₁ q₂ w Q k mX mY tape B R⟩ :
      TM2.Cfg (fun _ : CodeFallbackFullJoin.Stack => Bool) _ _) =
    ⟨none,(CodeFallbackFullJoin.prepControl,d.var),
      CodeFallbackSourceResult.finalBank n p s q₁ q₂ w Q k mX mY tape B R d⟩

theorem every_tape_halts_with_source_outcome
    (n p s q₁ q₂ w Q k mX mY M B R N : Nat)
    (hs : 3 ≤ s)
    (hM : (meaning (sampleRoot n p s q₁ q₂ w Q k mX mY)).maxAlphabet ≤ M)
    (hMB : Nat.clog 2 M ≤ B) (hR : 0 < R)
    (hp : GeneratorPositive.Positive (sampleRoot n p s q₁ q₂ w Q k mX mY))
    (hN : (meaning (sampleRoot n p s q₁ q₂ w Q k mX mY)).maxDraws ≤ N)
    (tape : CappedSampler.Adaptive.Tape B R N) :
    ∃ clock ≤ CodeFallbackEntryJoin.clock n p s q₁ q₂ w Q k mX mY +
      max ((codeSize (sampleRoot n p s q₁ q₂ w Q k mX mY)+1) *
          CodeFullRepeatPublic.repeatStepCap
            (sampleRoot n p s q₁ q₂ w Q k mX mY) B R + N*(R*B)+4)
        (CodeTableFallback.sourceFailureCap
          (sampleRoot n p s q₁ q₂ w Q k mX mY) B R mX mY+1),
      ∃ d : CodeTableFallback.Config,
        d.l = none ∧
        Runs clock n p s q₁ q₂ w Q k mX mY
          (RecursiveSamplingTape.writeTape B R N tape).val B R d ∧
        Outcome mX mY (GeneratorCode.run B R hMB N
          (initialBounded (sampleRoot n p s q₁ q₂ w Q k mX mY) hM) tape) d := by
  cases he : GeneratorCode.run B R hMB N
      (initialBounded (sampleRoot n p s q₁ q₂ w Q k mX mY) hM) tape with
  | none =>
    obtain ⟨clock,a,wc,hclock,hrun⟩ := source_failure
      n p s q₁ q₂ w Q k mX mY M B R N hs hM hMB hR hp hN tape he
    let d : CodeTableFallback.Config :=
      ⟨none,CodeTableFallback.embedWriter wc,
        Sum.elim (Function.update a.stk CodeHeaderDraw.output [])
          (MatrixTableWriter.ready CodeTableFallback.emptyBank mX mY
            0 0 0 0 [] (MatrixMaterialization.rowMajor
              (fun (_ : Fin mX) (_ : Fin mY) => false))).contents⟩
    refine ⟨clock,?_,d,rfl,?_,?_⟩
    · exact failure_clock_le _ _ _ _ hclock
    · simpa only [Runs,d] using hrun
    · simp only [Outcome]
      exact ⟨a,wc,rfl⟩
  | some bytes =>
    obtain ⟨clock,a,hclock,hobs,htape,hrun⟩ := source_success
      n p s q₁ q₂ w Q k mX mY M B R N hs hM hMB hR hp tape bytes he
    let d : CodeTableFallback.Config :=
      ⟨none,CodeTableFallback.embedInterpreter a.var,
        Sum.elim a.stk (CodeTableFallback.writerData mX mY).contents⟩
    refine ⟨clock,?_,d,rfl,?_,?_⟩
    · exact success_clock_le _ _ _ _ _ hclock
    · simpa only [Runs,d] using hrun
    · simp only [Outcome]
      exact ⟨a,rfl,hobs,htape⟩

#print axioms every_tape_halts_with_source_outcome

end Paper2.CodeFallbackAllOutcomes
