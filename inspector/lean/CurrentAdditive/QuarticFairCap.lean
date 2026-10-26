import CurrentAdditive.QuarticWriterClock
import Paper2.FairBitCap

set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

namespace Paper2.CurrentAdditive.QuarticFairCap

open Paper2.FairBitCap Paper2.SourceRecursiveNoSampling Paper2.SourceProfileParameters
  Paper2.RecursiveSamplingExecution
open Paper2.ParameterizedCanonicalSource
open CurrentAdditive.RandomizedSchedule

theorem stepCap_le27 {n m : ℕ} [NeZero n]
    (L Δ : ℕ) (γ : ℚ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) L Δ γ) :
    stepCap (width L) (width L - 2) (outerWidth L)
      (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ) ≤ 2 ^ (25 * L) := by
  obtain ⟨_, _, _, hs, hq₁, hq₂, hw, hQ, _, hL⟩ :=
    QuarticClockCaps.scalar_caps27 L Δ γ hc
  dsimp [Paper2.GeneratorPublicCap.publicCap] at hs hq₁ hq₂ hw hQ
  let B := 2 ^ (7 * L)
  have hB1 : 1 ≤ B := by dsimp [B]; exact Nat.one_le_two_pow
  change width L ≤ B at hs
  change width L - 2 ≤ B at hq₁
  change outerWidth L ≤ B at hq₂
  change width27 L ≤ B at hw
  change Q27 (V := Fin n) (E := Fin m) L γ Δ ≤ B at hQ
  have hB2 : B ≤ B ^ 2 := by
    calc
      B = B * 1 := by omega
      _ ≤ B * B := Nat.mul_le_mul_left B hB1
      _ = B ^ 2 := by ring
  have hB3 : B ^ 2 ≤ B ^ 3 := by
    calc
      B ^ 2 = B ^ 2 * 1 := by omega
      _ ≤ B ^ 2 * B := Nat.mul_le_mul_left (B ^ 2) hB1
      _ = B ^ 3 := by ring
  have hrow : Q27 (V := Fin n) (E := Fin m) L γ Δ *
      (3 + 2 * width L + width L * ((width L - 2) + width L + 1)) ≤
      8 * B ^ 3 := by
    have hsub : Q27 (V := Fin n) (E := Fin m) L γ Δ *
        (3 + 2 * width L + width L * ((width L - 2) + width L + 1)) ≤
        B * (3 + 2 * B + B * (B + B + 1)) := by
      have hsum : (width L - 2) + width L + 1 ≤ B + B + 1 := by omega
      have hmul := Nat.mul_le_mul hs hsum
      have hinner : 3 + 2 * width L +
          width L * ((width L - 2) + width L + 1) ≤
          3 + 2 * B + B * (B + B + 1) := by omega
      exact Nat.mul_le_mul hQ hinner
    have hpoly : B * (3 + 2 * B + B * (B + B + 1)) ≤ 8 * B ^ 3 := by
      nlinarith only [hB2, hB3]
    exact hsub.trans hpoly
  have hcol : 1 + width27 L * (3 + 2 * outerWidth L) ≤
      8 * B ^ 3 := by
    have hsub : 1 + width27 L * (3 + 2 * outerWidth L) ≤
        1 + B * (3 + 2 * B) := by
      have hinner : 3 + 2 * outerWidth L ≤ 3 + 2 * B := by omega
      have hmul := Nat.mul_le_mul hw hinner
      omega
    have hpoly : 1 + B * (3 + 2 * B) ≤ 8 * B ^ 3 := by
      nlinarith only [hB1, hB2, hB3]
    exact hsub.trans hpoly
  have hT : stepCap (width L) (width L - 2) (outerWidth L)
      (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ) ≤ 16 * B ^ 3 := by
    unfold stepCap
    have hmax := max_le hrow hcol
    omega
  calc
    _ ≤ 16 * B ^ 3 := hT
    _ = 2 ^ (4 + 21 * L) := by
      calc
        16 * B ^ 3 = 2 ^ 4 * (2 ^ (7 * L)) ^ 3 := by norm_num [B]
        _ = 2 ^ (4 + 21 * L) := by
          rw [← pow_mul, ← pow_add]
          congr 1
          ring
    _ ≤ 2 ^ (25 * L) :=
      pow_le_pow_right₀ (by omega) (by omega)


theorem drawCap_le27 {n m : ℕ} [NeZero n]
    (L Δ : ℕ) (γ : ℚ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) L Δ γ) (k : ℕ) :
    drawCap (width L) (width L - 2) (outerWidth L)
      (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ)
      (LookupSeed.width L) k
      (sourceRows L (4 * RestorationWidthScheduleScratch.ell L) (q27 (V := Fin n) (E := Fin m) L γ Δ) k)
      (sourceCols L (4 * RestorationWidthScheduleScratch.ell L) (q27 (V := Fin n) (E := Fin m) L γ Δ) k) ≤
      2 ^ (60 * (k + 1) * L) := by
  have hc' := hc
  rcases hc' with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, hL, hseed⟩
  let mX := sourceRows L (4 * RestorationWidthScheduleScratch.ell L) (q27 (V := Fin n) (E := Fin m) L γ Δ) k
  let mY := sourceCols L (4 * RestorationWidthScheduleScratch.ell L) (q27 (V := Fin n) (E := Fin m) L γ Δ) k
  let p := LookupSeed.width L
  let T := stepCap (width L) (width L - 2) (outerWidth L)
    (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ)
  have hdim := QuarticClockCaps.dims_cap27 L Δ γ hc k
  have hT := stepCap_le27 L Δ γ hc
  have hpExp : LookupSeed.exponent L ≤ L := by omega
  have hp : p ≤ 2 ^ L := pow_le_pow_right₀ (by omega) hpExp
  have hTk : T ^ k ≤ (2 ^ (25 * L)) ^ k := Nat.pow_le_pow_left hT _
  have hraw := drawCap_le (width L) (width L - 2) (outerWidth L)
    (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ) p k mX mY
  have hpmax : max p 1 ≤ 2 ^ L := by
    apply max_le hp
    exact Nat.one_le_two_pow
  have hsum : mX + mY ≤ 2 * 2 ^ (29 * (k + 1) * L) := by
    dsimp [mX, mY]
    omega
  have hprod : (mX + mY) * (max p 1 * T ^ k) ≤
      (2 * 2 ^ (29 * (k + 1) * L)) *
        (2 ^ L * (2 ^ (25 * L)) ^ k) := by
    exact Nat.mul_le_mul hsum (Nat.mul_le_mul hpmax hTk)
  have hExp : 2 + 29 * (k + 1) * L + L + 25 * L * k ≤
      60 * (k + 1) * L := by nlinarith only [hL]
  calc
    _ ≤ 1 + (mX + mY) * (max p 1 * T ^ k) := hraw
    _ ≤ 1 + (2 * 2 ^ (29 * (k + 1) * L)) *
      (2 ^ L * (2 ^ (25 * L)) ^ k) := Nat.add_le_add_left hprod 1
    _ ≤ 2 ^ (2 + 29 * (k + 1) * L + L + 25 * L * k) := by
      let A := 29 * (k + 1) * L
      let E := 1 + A + L + 25 * L * k
      have heq : (2 * 2 ^ A) * (2 ^ L * (2 ^ (25 * L)) ^ k) = 2 ^ E := by
        dsimp [E]
        have htwo : 2 * 2 ^ A = 2 ^ (A + 1) := by
          rw [pow_succ]
          omega
        rw [htwo, ← pow_mul, ← pow_add, ← pow_add]
        congr 1
        omega
      rw [heq]
      have hpos : 1 ≤ 2 ^ E := Nat.one_le_two_pow
      have hpow : 2 ^ (2 + 29 * (k + 1) * L + L + 25 * L * k) =
          2 * 2 ^ E := by
        rw [show 2 + 29 * (k + 1) * L + L + 25 * L * k = 1 + E by
          dsimp [E, A]; omega, pow_add]
        norm_num
      rw [hpow]
      omega
    _ ≤ 2 ^ (60 * (k + 1) * L) :=
      pow_le_pow_right₀ (by omega) hExp

/-- The physical rejection sampler's alphabet and each attempted word width
for the actual quartic schedule. -/
theorem alphabetCap_le27 {n m : ℕ} [NeZero n]
    (L Δ : ℕ) (γ : ℚ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) L Δ γ) :
    alphabetCap (width L) (width L - 2) (outerWidth L)
      (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ)
      n (LookupSeed.width L) ≤ 2 ^ (8 * L) := by
  obtain ⟨_, hn, hp, hs, hq₁, hq₂, hw, hQ, _, hL⟩ :=
    QuarticClockCaps.scalar_caps27 L Δ γ hc
  dsimp [Paper2.GeneratorPublicCap.publicCap] at hn hp hs hq₁ hq₂ hw hQ
  let B := 2 ^ (7 * L)
  change n ≤ B at hn
  change LookupSeed.width L ≤ B at hp
  change width L ≤ B at hs
  change width L - 2 ≤ B at hq₁
  change outerWidth L ≤ B at hq₂
  change width27 L ≤ B at hw
  change Q27 (V := Fin n) (E := Fin m) L γ Δ ≤ B at hQ
  have hB512 : 512 ≤ B := by
    have he : 9 ≤ 7 * L := by omega
    have hp' : 2 ^ 9 ≤ B := pow_le_pow_right₀ (by omega) he
    norm_num at hp' ⊢
    exact hp'
  have hraw : alphabetCap (width L) (width L - 2) (outerWidth L)
      (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ)
      n (LookupSeed.width L) ≤ 16 * B := by
    unfold alphabetCap
    omega
  calc
    _ ≤ 16 * B := hraw
    _ = 2 ^ (4 + 7 * L) := by
      dsimp [B]
      norm_num [pow_add]
    _ ≤ 2 ^ (8 * L) :=
      pow_le_pow_right₀ (by omega) (by omega)

theorem bitWidth_le27 {n m : ℕ} [NeZero n]
    (L Δ : ℕ) (γ : ℚ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) L Δ γ) :
    Nat.clog 2 (alphabetCap (width L) (width L - 2) (outerWidth L)
      (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ)
      n (LookupSeed.width L)) ≤ 8 * L :=
  Nat.clog_le_of_le_pow (alphabetCap_le27 L Δ γ hc)

end Paper2.CurrentAdditive.QuarticFairCap

#print axioms Paper2.CurrentAdditive.QuarticFairCap.stepCap_le27
#print axioms Paper2.CurrentAdditive.QuarticFairCap.drawCap_le27
#print axioms Paper2.CurrentAdditive.QuarticFairCap.alphabetCap_le27
#print axioms Paper2.CurrentAdditive.QuarticFairCap.bitWidth_le27
