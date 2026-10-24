import CurrentAdditive.QuarticInterpreterClock
import Paper2.CodeGeneratorClockSum

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

namespace Paper2.CurrentAdditive.QuarticCompilerClock

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorSource Paper2.CodeGeneratorClockSum
open Paper2.GeneratorCode
open Paper2.CodeRecursiveLoop Paper2.CodeGeneratorExponentPublic
open CurrentAdditive.RandomizedSchedule

theorem compiler_clock_le_public27
    {n m : Nat} [NeZero n] (L Δ k : Nat) (γ : ℚ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) L Δ γ) :
    CodeGeneratorComplete.clock n (LookupSeed.width L)
      (SourceProfileParameters.width L)
      (SourceProfileParameters.width L - 2)
      (SourceProfileParameters.outerWidth L)
      (width27 L)
      (Q27 (V := Fin n) (E := Fin m) L γ Δ) k ≤
    publicCompilerClock L k := by
  let M := GeneratorPublicCap.publicCap L
  let p := LookupSeed.width L
  let s := SourceProfileParameters.width L
  let q₁ := SourceProfileParameters.width L - 2
  let q₂ := SourceProfileParameters.outerWidth L
  let w := width27 L
  let Q := Q27 (V := Fin n) (E := Fin m) L γ Δ
  let A := (M+1)^(18*(k+1))
  obtain ⟨hM, hn, hp, hsM, hq₁, hq₂, hw, hQ, _, _⟩ :=
    QuarticClockCaps.scalar_caps27 L Δ γ hc
  have hs : 3 ≤ s := by
    dsimp [s]
    have h := SourceProfileParameters.width_admissible L
    omega
  have hloop := totalClock_seed_le_cap M n p s q₁ q₂ w Q k
    hM hn hp hs hsM hq₁ hq₂ hw hQ
  change totalClock n s q₁ q₂ w Q (copies p .bit) (.ticket p) k ≤
    1+k*(CodeGeneratorStepGrowth.roundPoly n s q₁ q₂ w Q A A + 1)
    at hloop
  have hpolyAll : CodeGeneratorStepGrowth.roundPoly
      n s q₁ q₂ w Q A A ≤
      CodeGeneratorStepGrowth.roundPoly M M M M M M A A := by
    dsimp [CodeGeneratorStepGrowth.roundPoly,
      CodeRecursiveStepClock.polynomialClock,
      CodeRecursiveStepClock.graphCap,
      CodeRecursiveStepClock.taggedCap,
      TaggedCompiler.polynomialClock]
    gcongr
  have hmul := Nat.mul_le_mul_left k
    (Nat.add_le_add_right hpolyAll 1)
  have hseed : CodeRecursiveSeedJoin.clock p ≤ 6*M+17 := by
    dsimp [CodeRecursiveSeedJoin.clock, CodeRecursiveSeedJoin.b₁]
    omega
  change CodeRecursiveSeedJoin.clock p +
      totalClock n s q₁ q₂ w Q (copies p .bit) (.ticket p) k + 1 ≤
    6*M+18+1+k*(CodeGeneratorStepGrowth.roundPoly M M M M M M A A + 1)
  omega

theorem compiler_clock_pow27 {n m : Nat} [NeZero n]
    (L Δ k : Nat) (γ : ℚ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) L Δ γ) :
    CodeGeneratorComplete.clock n (LookupSeed.width L)
      (SourceProfileParameters.width L)
      (SourceProfileParameters.width L - 2)
      (SourceProfileParameters.outerWidth L)
      (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ) k ≤
      2 ^ (CodeGeneratorExponentPublic.exponentConstant * (k + 1) * L) := by
  have hL : 1 ≤ L := by
    have h := hc
    dsimp only [CurrentAdditive.QuarticSchedule.Checks27] at h
    rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hL, _⟩
    omega
  exact (compiler_clock_le_public27 L Δ k γ hc).trans
    (CodeGeneratorExponentPublic.publicCompilerClock_le_two_pow L k hL)


end Paper2.CurrentAdditive.QuarticCompilerClock

#print axioms Paper2.CurrentAdditive.QuarticCompilerClock.compiler_clock_le_public27
#print axioms Paper2.CurrentAdditive.QuarticCompilerClock.compiler_clock_pow27
