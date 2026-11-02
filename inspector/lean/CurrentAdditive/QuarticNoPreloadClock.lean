import CurrentAdditive.QuarticUniformClock
import CurrentAdditive.QuarticAtoms
import Paper2.FallbackNoPreloadEndpoint

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

namespace Paper2.CurrentAdditive.QuarticNoPreloadClock

open Turing
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.SourceRecursiveNoSampling Paper2.ParameterizedCanonicalSource
open Paper2.FallbackNoPreloadClock Paper2.FallbackNoPreloadRun
open CurrentAdditive.RandomizedSchedule

theorem no_preload_clock27 {n m : Nat} [NeZero n]
    (L Δ : Nat) (γ : ℚ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) L Δ γ) (k : Nat) :
    SamplerFallbackJoin.clock n (LookupSeed.width L)
      (SourceProfileParameters.width L) (SourceProfileParameters.width L - 2)
      (SourceProfileParameters.outerWidth L) (width27 L)
      (Q27 (V := Fin n) (E := Fin m) L γ Δ) k
      (sourceRows L (4 * RestorationWidthScheduleScratch.ell L) (q27 (V := Fin n) (E := Fin m) L γ Δ) k)
      (sourceCols L (4 * RestorationWidthScheduleScratch.ell L) (q27 (V := Fin n) (E := Fin m) L γ Δ) k) ≤
      2 ^ (noPreloadExponent * (k + 1) * L) := by
  let T := (k + 1) * L
  have hL : 16 ≤ L := by
    rcases hc with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hL, _⟩
    exact hL
  have hT : 1 ≤ T := by
    have hp : 0 < (k + 1) * L := Nat.mul_pos (by omega) (by omega)
    dsimp [T]; omega
  have hspj := QuarticAtoms.atoms27 L Δ γ hc k
  dsimp only at hspj
  have hfb := QuarticUniformClock.outcome_clock27 L Δ γ hc k
  dsimp only at hfb
  have hZ3 : (2 ^ (60 * ((k + 1) * L))) ^ 3 ≤ 2 ^ (180 * T) := by
    rw [← pow_mul]; dsimp [T]; apply le_of_eq; congr 1; ring
  have hab := absorb2 (8 * cf + 27100) FallbackUniformClock.uniformExponent T
    ((2 ^ (60 * ((k + 1) * L))) ^ 3) hT hZ3
  have e1 : FallbackUniformClock.uniformExponent * (k + 1) * L =
      FallbackUniformClock.uniformExponent * T := by dsimp [T]; ring
  have e2 : noPreloadExponent * (k + 1) * L =
      (FallbackUniformClock.uniformExponent + (8 * cf + 27100) + 182) * T := by
    dsimp [T, noPreloadExponent]; ring
  rw [e1] at hfb
  rw [e2]
  have hfb' : SamplerFallbackJoin.fallbackCap n (LookupSeed.width L)
      (SourceProfileParameters.width L) (SourceProfileParameters.width L - 2)
      (SourceProfileParameters.outerWidth L) (width27 L)
      (Q27 (V := Fin n) (E := Fin m) L γ Δ) k
      (sourceRows L (4 * RestorationWidthScheduleScratch.ell L) (q27 (V := Fin n) (E := Fin m) L γ Δ) k)
      (sourceCols L (4 * RestorationWidthScheduleScratch.ell L) (q27 (V := Fin n) (E := Fin m) L γ Δ) k) ≤
      2 ^ (FallbackUniformClock.uniformExponent * T) := hfb
  unfold SamplerFallbackJoin.clock
  exact (Nat.add_le_add (Nat.add_le_add hspj le_rfl) hfb').trans hab


end Paper2.CurrentAdditive.QuarticNoPreloadClock

#print axioms Paper2.CurrentAdditive.QuarticNoPreloadClock.no_preload_clock27
