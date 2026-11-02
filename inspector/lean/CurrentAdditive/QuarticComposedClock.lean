import CurrentAdditive.QuarticNoPreloadClock
import CurrentAdditive.QuarticWriterClock
import Paper2.SuccessPremiseComposition

set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

namespace Paper2.CurrentAdditive.QuarticComposedClock

open Paper2.SourceRecursiveNoSampling Paper2.ParameterizedCanonicalSource
open CurrentAdditive.RandomizedSchedule

theorem composed_clock27 {n m : Nat} [NeZero n]
    (L Δ : Nat) (γ : ℚ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) L Δ γ) (k pre Tent cP cE : Nat)
    (hpre : pre ≤ 2 ^ (cP * (k + 1) * L))
    (hent : Tent ≤ 2 ^ (cE * (k + 1) * L)) :
    let p := LookupSeed.width L
    let s := SourceProfileParameters.width L
    let q₁ := SourceProfileParameters.width L - 2
    let q₂ := SourceProfileParameters.outerWidth L
    let w := width27 L
    let Q := Q27 (V := Fin n) (E := Fin m) L γ Δ
    let mX := sourceRows L (4 * RestorationWidthScheduleScratch.ell L) (q27 (V := Fin n) (E := Fin m) L γ Δ) k
    let mY := sourceCols L (4 * RestorationWidthScheduleScratch.ell L) (q27 (V := Fin n) (E := Fin m) L γ Δ) k
    SamplerFallbackJoin.clock n p s q₁ q₂ w Q k mX mY + pre +
        EthInapproximability.CurrentPaper.MatrixTableWriter.writerBound mX mY Tent ≤
      2 ^ ((FallbackNoPreloadRun.noPreloadExponent + cP + cE + 65) * (k + 1) * L) := by
  intro p s q₁ q₂ w Q mX mY
  let T := (k + 1) * L
  have hL : 16 ≤ L := by
    rcases hc with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hL, _⟩
    exact hL
  have hT : 1 ≤ T := by
    have hp : 0 < (k + 1) * L := Nat.mul_pos (by omega) (by omega)
    dsimp [T]; omega
  have h1 := QuarticNoPreloadClock.no_preload_clock27 L Δ γ hc k
  have h3 := QuarticWriterClock.writerBound_entry27 L Δ γ hc k Tent cE hent
  let K := FallbackNoPreloadRun.noPreloadExponent + cP + cE + 63
  have mono : ∀ e, e ≤ K → 2 ^ (e * (k + 1) * L) ≤ 2 ^ (K * T) := fun e he =>
    pow_le_pow_right₀ (by decide : 1 ≤ (2:Nat))
      (by dsimp [T]; rw [Nat.mul_assoc]; exact Nat.mul_le_mul_right _ he)
  have g1 := h1.trans (mono _ (by dsimp [K]; omega))
  have g2 := hpre.trans (mono _ (by dsimp [K]; omega))
  have g3 := h3.trans (mono _ (by dsimp [K]; omega))
  have h4 : 4 * 2 ^ (K * T) ≤
      2 ^ ((FallbackNoPreloadRun.noPreloadExponent + cP + cE + 65) * (k + 1) * L) := by
    calc
      4 * 2 ^ (K * T) = 2 ^ (2 + K * T) := by rw [pow_add]; norm_num
      _ ≤ _ := pow_le_pow_right₀ (by decide : 1 ≤ (2:Nat)) (by dsimp [K, T]; nlinarith)
  have g1' : SamplerFallbackJoin.clock n p s q₁ q₂ w Q k mX mY ≤ 2 ^ (K * T) := g1
  have g3' : EthInapproximability.CurrentPaper.MatrixTableWriter.writerBound mX mY Tent ≤
      2 ^ (K * T) := g3
  omega


end Paper2.CurrentAdditive.QuarticComposedClock

#print axioms Paper2.CurrentAdditive.QuarticComposedClock.composed_clock27
