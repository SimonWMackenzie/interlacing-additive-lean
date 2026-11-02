import Paper2.CodeGeneratorExponentPublic

/-! Public exponential clock for the literal scheduled-code compiler. -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

namespace Paper2.CodeGeneratorExponentScheduled

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorSource
open Paper2.CodeGeneratorExponentPublic
open Paper2.CodeGeneratorClockSum
open Paper2.CodeRecursiveLoop

theorem scheduled_clock_le_two_pow {n m : Nat} [NeZero n]
    (L Δ k : Nat) (γ : ℚ)
    (hc : Paper2.CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) L Δ γ) :
    CodeGeneratorComplete.clock n (LookupSeed.width L)
      (SourceProfileParameters.width L)
      (SourceProfileParameters.width L - 2)
      (SourceProfileParameters.outerWidth L)
      (ParameterizedCanonicalSource.restorationWidth L)
      (ParameterizedCanonicalSource.coverWidth n m L Δ γ) k ≤
    2^(exponentConstant*(k+1)*L) := by
  have hL : 1 ≤ L := by
    rcases hc with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hL, _⟩
    omega
  exact (scheduled_compiler_clock_le_public L Δ k γ hc).trans
    (publicCompilerClock_le_two_pow L k hL)

theorem run_scheduledCodes_two_pow {n m : Nat} [NeZero n]
    (L Δ k : Nat) (γ : ℚ)
    (hc : Paper2.CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) L Δ γ) :
    ∃ t ≤ 2^(exponentConstant*(k+1)*L),
      ((advance CodeGeneratorComplete.program)^[t])
        (⟨some (EthInapproximability.CurrentPaper.BitMachineRawSequence.leftLabel
            CodeGeneratorComplete.seedStart),
          (CodeGeneratorComplete.seedControl,CodeGeneratorComplete.loopControl),
          CodeRecursiveSeedPrep.publicBase n
            (SourceProfileParameters.width L)
            (SourceProfileParameters.width L - 2)
            (SourceProfileParameters.outerWidth L)
            (ParameterizedCanonicalSource.restorationWidth L)
            (ParameterizedCanonicalSource.coverWidth n m L Δ γ)
            (LookupSeed.width L) (List.replicate k true)⟩ :
          TM2.Cfg (fun _ : Paper2.CodeRecursiveLoop.Stack => Bool) _ _) =
        ⟨none,
          (CodeGeneratorComplete.seedControl,CodeGeneratorComplete.loopControl),
          (finished n (SourceProfileParameters.width L)
            (SourceProfileParameters.width L - 2)
            (SourceProfileParameters.outerWidth L)
            (ParameterizedCanonicalSource.restorationWidth L)
            (ParameterizedCanonicalSource.coverWidth n m L Δ γ)
            (scheduledCodes n m L Δ γ k).1
            (scheduledCodes n m L Δ γ k).2).stk⟩ := by
  have hs : 3 ≤ SourceProfileParameters.width L := by
    have h := SourceProfileParameters.width_admissible L
    omega
  obtain ⟨t,ht,hr⟩ := CodeGeneratorComplete.run_scheduledCodes
    n m L Δ k γ hs
  exact ⟨t, ht.trans (scheduled_clock_le_two_pow L Δ k γ hc), hr⟩

#print axioms scheduled_clock_le_two_pow
#print axioms run_scheduledCodes_two_pow

end Paper2.CodeGeneratorExponentScheduled
