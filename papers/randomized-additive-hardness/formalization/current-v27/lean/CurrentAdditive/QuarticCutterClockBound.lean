import CurrentAdditive.QuarticAtoms
import CurrentAdditive.QuarticRawPrefixCutter
import Paper2.A3Clock

/-! Polynomial charging of the scheduled v27 physical prefix cutter. -/

namespace Paper2.CurrentAdditive.QuarticCutterClockBound

open EthInapproximability.CurrentPaper
open Paper2.CurrentAdditive.QuarticConstructor
open CurrentAdditive.RandomizedSchedule

noncomputable section

def cutCoefficient : ℕ :=
  8 * Paper2.FallbackNoPreloadClock.cf + 27100 +
    100 * (BitMachineStackGrowth.perStep SamplerParameterJoin.cutProgram + 1)

theorem prepared_cut_of_atoms
    (n p s q₁ q₂ w Q k mX mY Z : ℕ) (raw : List Bool)
    (hZ : 1 ≤ Z)
    (hprod : SamplerParameterJoin.clock n p s q₁ q₂ w Q k mX mY ≤
      (8 * Paper2.FallbackNoPreloadClock.cf + 27100) * Z ^ 3)
    (hR : SamplerParameterJoin.R p s q₁ q₂ w Q k mX mY ≤ Z)
    (hB : SamplerParameterJoin.B n p s q₁ q₂ w Q ≤ Z)
    (hN : SamplerNRProducer.N s q₁ q₂ w Q p k mX mY ≤ Z) :
    QuarticPreparedCut.clock n p s q₁ q₂ w Q k mX mY raw ≤
      cutCoefficient * (Z ^ 3 + raw.length + 1) := by
  let R := SamplerParameterJoin.R p s q₁ q₂ w Q k mX mY
  let B := SamplerParameterJoin.B n p s q₁ q₂ w Q
  let N := SamplerNRProducer.N s q₁ q₂ w Q p k mX mY
  let G := BitMachineStackGrowth.perStep SamplerParameterJoin.cutProgram
  let D := N * (R * B)
  have hZ2 : Z ^ 2 ≤ Z ^ 3 := by nlinarith
  have hZ1 : 1 ≤ Z ^ 3 := by nlinarith
  have hZle : Z ≤ Z ^ 3 := by nlinarith
  have hRB : R * B ≤ Z ^ 3 := by
    have h := Nat.mul_le_mul hR hB
    calc R * B ≤ Z ^ 2 := by simpa only [pow_two] using h
      _ ≤ Z ^ 3 := hZ2
  have hD : D ≤ Z ^ 3 := by
    have h := Nat.mul_le_mul hN (Nat.mul_le_mul hR hB)
    calc
      D = N * (R * B) := rfl
      _ ≤ Z * (Z * Z) := h
      _ = Z ^ 3 := by ring
  have he1 : MatrixAddressMachine.exactTime R B 0 ≤ 10 * Z ^ 3 := by
    have hmul : 2 * R * B ≤ 2 * Z ^ 3 := by
      calc
        2 * R * B = 2 * (R * B) := by ring
        _ ≤ 2 * Z ^ 3 := Nat.mul_le_mul_left 2 hRB
    unfold MatrixAddressMachine.exactTime
    nlinarith only [hmul, hR, hZ1, hZle]
  have he2 : MatrixAddressMachine.exactTime N (R * B) 0 ≤ 10 * Z ^ 3 := by
    have hmul : 2 * N * (R * B) ≤ 2 * Z ^ 3 := by
      calc
        2 * N * (R * B) = 2 * D := by dsimp [D]; ring
        _ ≤ 2 * Z ^ 3 := Nat.mul_le_mul_left 2 hD
    unfold MatrixAddressMachine.exactTime
    nlinarith only [hmul, hN, hZ1, hZle]
  change SamplerParameterJoin.clock n p s q₁ q₂ w Q k mX mY +
      MatrixAddressMachine.exactTime R B 0 +
      MatrixAddressMachine.exactTime N (R * B) 0 +
      D + raw.length + R * B + D +
      (D + raw.length + 4) * G +
      (D + raw.length + 4) * G + 14 ≤
        cutCoefficient * (Z ^ 3 + raw.length + 1)
  dsimp [cutCoefficient]
  have hGraw := Nat.zero_le (G * raw.length)
  nlinarith only [hprod, he1, he2, hRB, hD, hZ1, hGraw,
    Nat.mul_le_mul_left G hD]

#print axioms prepared_cut_of_atoms

theorem raw_prefix_clock_scheduled
    {n m : ℕ} (hn : 0 < n) (Δ : ℕ) (γ : ℚ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ)
    (k : ℕ) (raw : List Bool) :
    QuarticRawPrefixCutter.clock n m (Nat.clog 2 n) Δ γ k raw ≤
      cutCoefficient *
        ((n + 2) ^ (360 * (k + 1)) + raw.length + 1) := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let L := Nat.clog 2 n
  let T := (k + 1) * L
  let Z := 2 ^ (60 * T)
  let p := LookupSeed.width L
  let s := SourceProfileParameters.width L
  let q₁ := SourceProfileParameters.width L - 2
  let q₂ := SourceProfileParameters.outerWidth L
  let w := width27 L
  let Q := Q27 (V := Fin n) (E := Fin m) L γ Δ
  let mX := SourceRecursiveNoSampling.sourceRows L
    (4 * RestorationWidthScheduleScratch.ell L)
    (q27 (V := Fin n) (E := Fin m) L γ Δ) k
  let mY := SourceRecursiveNoSampling.sourceCols L
    (4 * RestorationWidthScheduleScratch.ell L)
    (q27 (V := Fin n) (E := Fin m) L γ Δ) k
  have hL : 16 ≤ L := by
    rcases hc with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hL, _⟩
    exact hL
  have hT : 1 ≤ T := by dsimp [T]; nlinarith
  have hZ : 1 ≤ Z := Nat.one_le_two_pow
  have hdraw : SamplerNRProducer.N s q₁ q₂ w Q p k mX mY ≤ Z := by
    have h := QuarticFairCap.drawCap_le27 L Δ γ hc k
    simpa only [SamplerNRProducer.N, SamplerNRProducer.N, s, q₁, q₂,
      w, Q, p, mX, mY, Z, T, Nat.mul_assoc] using h
  have hbit : SamplerParameterJoin.B n p s q₁ q₂ w Q ≤ Z := by
    have hb0 : SamplerParameterJoin.B n p s q₁ q₂ w Q ≤ 8 * L := by
      simpa only [SamplerParameterJoin.B, SamplerParameterJoin.M,
        p, s, q₁, q₂, w, Q] using
        (QuarticFairCap.bitWidth_le27 L Δ γ hc)
    have hlin := Paper2.CodeSamplerScheduledBounds.linear_le_pow T hT
    have hp : 2 ^ (8 * T) ≤ Z := by
      dsimp [Z]
      exact Nat.pow_le_pow_right (by omega) (by omega)
    have hLT : L ≤ T := by dsimp [T]; nlinarith
    omega
  have hR : SamplerParameterJoin.R p s q₁ q₂ w Q k mX mY ≤ Z := by
    have hraw := Paper2.FairBitCap.rejectionAttemptCap_le_of_pow
      (SamplerNRProducer.N s q₁ q₂ w Q p k mX mY) (60 * T) hdraw
    have hlin := Paper2.CodeSamplerScheduledBounds.linear_le_pow T hT
    have hp : 2 ^ (8 * T) ≤ Z := by
      dsimp [Z]
      exact Nat.pow_le_pow_right (by omega) (by omega)
    change Paper2.rejectionAttemptCap
      (SamplerNRProducer.N s q₁ q₂ w Q p k mX mY) ≤ Z
    omega
  have hprod : SamplerParameterJoin.clock n p s q₁ q₂ w Q k mX mY ≤
      (8 * Paper2.FallbackNoPreloadClock.cf + 27100) * Z ^ 3 := by
    have h := QuarticAtoms.atoms27 L Δ γ hc k
    simpa only [p, s, q₁, q₂, w, Q, mX, mY, Z, T, Nat.mul_assoc] using h
  have hcut := prepared_cut_of_atoms n p s q₁ q₂ w Q k mX mY Z raw
    hZ hprod hR hbit hdraw
  have hpow : Z ^ 3 ≤ (n + 2) ^ (360 * (k + 1)) := by
    have h := Paper2.A3Assembly.Clock.two_pow_mul_clog_le 180 k n
    dsimp [Z, T, L]
    convert h using 1 <;> ring
  have hmono : Z ^ 3 + raw.length + 1 ≤
      (n + 2) ^ (360 * (k + 1)) + raw.length + 1 := by omega
  calc
    QuarticRawPrefixCutter.clock n m (Nat.clog 2 n) Δ γ k raw =
        QuarticPreparedCut.clock n p s q₁ q₂ w Q k mX mY raw := rfl
    _ ≤ cutCoefficient * (Z ^ 3 + raw.length + 1) := hcut
    _ ≤ cutCoefficient *
          ((n + 2) ^ (360 * (k + 1)) + raw.length + 1) :=
      Nat.mul_le_mul_left _ hmono

#print axioms raw_prefix_clock_scheduled

end
end Paper2.CurrentAdditive.QuarticCutterClockBound
