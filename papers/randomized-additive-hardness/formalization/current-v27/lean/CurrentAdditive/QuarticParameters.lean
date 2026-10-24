import CurrentAdditive.QuarticRootCap

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

namespace Paper2.CurrentAdditive.QuarticParameters

open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.RecursiveSamplingExecution
open Paper2.SourceProfileParameters Paper2.SourceRecursiveNoSampling
open Paper2.ParameterizedCanonicalSource Paper2.CodeSamplerScheduledBounds
open Paper2.CurrentAdditive.QuarticRootCap
open CurrentAdditive.RandomizedSchedule

theorem parameters27 {n m : Nat} [NeZero n]
    (L Δ : Nat) (γ : Rat) (k : Nat)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) L Δ γ) :
    let mX := sourceRows L (4 * RestorationWidthScheduleScratch.ell L)
      (q27 (V := Fin n) (E := Fin m) L γ Δ) k
    let mY := sourceCols L (4 * RestorationWidthScheduleScratch.ell L)
      (q27 (V := Fin n) (E := Fin m) L γ Δ) k
    let root := CodeFallbackSourceResult.sampleRoot n (LookupSeed.width L)
      (width L) (width L - 2) (outerWidth L) (width27 L)
      (Q27 (V := Fin n) (E := Fin m) L γ Δ) k mX mY
    let B := Nat.clog 2 (alphabetCap (width L) (width L - 2) (outerWidth L)
      (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ) n (LookupSeed.width L))
    let N := drawCap (width L) (width L - 2) (outerWidth L)
      (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ)
      (LookupSeed.width L) k mX mY
    let R := Paper2.rejectionAttemptCap N
    codeSize root ≤ 2^(180*(k+1)*L) ∧
      B ≤ 2^(180*(k+1)*L) ∧
      R ≤ 2^(180*(k+1)*L) ∧
      N ≤ 2^(180*(k+1)*L) := by
  let mX := sourceRows L (4 * RestorationWidthScheduleScratch.ell L)
    (q27 (V := Fin n) (E := Fin m) L γ Δ) k
  let mY := sourceCols L (4 * RestorationWidthScheduleScratch.ell L)
    (q27 (V := Fin n) (E := Fin m) L γ Δ) k
  let T := (k+1)*L
  have hL : 16 ≤ L := by
    rcases hc with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hL, _⟩
    exact hL
  have hT : 1 ≤ T := by
    have hp : 0 < (k+1)*L :=
      Nat.mul_pos (by omega) (by omega)
    dsimp [T]
    omega
  have hLT : L ≤ T := by
    dsimp [T]
    nlinarith
  have hlinear := QuarticRootCap.linear_le_pow T hT
  have hpow : 2^(8*T) ≤ 2^(180*T) :=
    pow_le_pow_right₀ (by decide : 1 ≤ (2:Nat)) (by omega)
  have h73 : 73*T ≤ 2^(180*T) := hlinear.trans hpow
  have hroot := root_size27 L Δ γ k hc
  have hB := QuarticFairCap.bitWidth_le27 L Δ γ hc
  have hN := QuarticFairCap.drawCap_le27 L Δ γ hc k
  change drawCap (width L) (width L - 2) (outerWidth L)
      (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ)
      (LookupSeed.width L) k mX mY ≤
    2^(60*(k+1)*L) at hN
  have hR := FairBitCap.rejectionAttemptCap_le_of_pow
    (drawCap (width L) (width L - 2) (outerWidth L)
      (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ)
      (LookupSeed.width L) k mX mY)
    (60*T) (by
      convert hN using 1 <;> dsimp [T] <;> ring)
  have hNpow : 2^(60*T) ≤ 2^(180*T) :=
    pow_le_pow_right₀ (by decide : 1 ≤ (2:Nat)) (by omega)
  have hNfinal :
      drawCap (width L) (width L - 2) (outerWidth L)
      (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ)
      (LookupSeed.width L) k mX mY ≤
        2^(180*T) := by
    calc
      _ ≤ 2^(60*T) := by convert hN using 1 <;> dsimp [T] <;> ring
      _ ≤ _ := hNpow
  have hBfinal :
      Nat.clog 2 (alphabetCap (width L) (width L - 2) (outerWidth L)
      (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ) n (LookupSeed.width L)) ≤
        2^(180*T) := by
    have hB' :
        Nat.clog 2 (alphabetCap (width L) (width L - 2) (outerWidth L)
      (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ) n (LookupSeed.width L)) ≤
          8*L := by convert hB using 1
    exact hB'.trans (by calc
      8*L ≤ 73*T := by omega
      _ ≤ _ := h73)
  have hRfinal :
      Paper2.rejectionAttemptCap
        (drawCap (width L) (width L - 2) (outerWidth L)
      (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ)
      (LookupSeed.width L) k mX mY) ≤
          2^(180*T) := by
    exact hR.trans (by calc
      13+60*T ≤ 73*T := by omega
      _ ≤ _ := h73)
  dsimp only
  rw [show 180 * (k + 1) * L = 180 * T by dsimp [T]; ring]
  rw [show 180 * (k + 1) * L = 180 * T by dsimp [T]; ring] at hroot
  exact ⟨hroot, hBfinal, hRfinal, hNfinal⟩


end Paper2.CurrentAdditive.QuarticParameters

#print axioms Paper2.CurrentAdditive.QuarticParameters.parameters27
