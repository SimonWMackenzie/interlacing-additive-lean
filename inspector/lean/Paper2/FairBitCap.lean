import Paper2.RecursiveSamplingMaterialization
import Paper2.ScheduledOutputBounds

/-! Actual recursive draw caps and fair-bit allocations. These are counts
for the finite sampler, not machine-running-time bounds. -/

namespace Paper2.FairBitCap

open RecursiveSampling RecursiveSamplingExecution
  SourceProfileParameters SourceRecursiveNoSampling
  ParameterizedCanonicalSource

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- One explicit multiplier for both recursive label generators. -/
def stepCap (s q₁ q₂ w Q : ℕ) : ℕ :=
  max (Q * (3 + 2 * s + s * (q₁ + s + 1)))
    (1 + w * (3 + 2 * q₂)) + 1

/-- Every actual recursive row and column draw count is at most the same
step multiplier to the iteration depth, charged to the larger seed cap. -/
theorem drawBounds_le_stepCap_pow (s q₁ q₂ w Q row₀ col₀ k : ℕ)
    (hbase : 1 ≤ max row₀ col₀) :
    (drawBounds s q₁ q₂ w Q row₀ col₀ k).1 ≤
        max row₀ col₀ * (stepCap s q₁ q₂ w Q) ^ k ∧
    (drawBounds s q₁ q₂ w Q row₀ col₀ k).2 ≤
        max row₀ col₀ * (stepCap s q₁ q₂ w Q) ^ k := by
  induction k with
  | zero =>
      simp only [drawBounds, pow_zero, mul_one]
      exact ⟨le_max_left _ _, le_max_right _ _⟩
  | succ k ih =>
      let T := stepCap s q₁ q₂ w Q
      let M := max row₀ col₀
      let A := (s + 1) + s * (q₁ + s + 1)
      let prev := drawBounds s q₁ q₂ w Q row₀ col₀ k
      have hT : 0 < T := by dsimp [T, stepCap]; omega
      have hpow' : 1 ≤ T ^ k := by have := pow_pos hT k; omega
      have hpow : 1 ≤ M * T ^ k := by
        have := Nat.mul_le_mul hbase hpow'
        simpa only [mul_one] using this
      have hrow : prev.1 ≤ M * T ^ k := ih.1
      have hcol : prev.2 ≤ M * T ^ k := ih.2
      have hrowCoef : Q * (2 + s + A) ≤ T := by
        have heq : Q * (2 + s + A) =
            Q * (3 + 2 * s + s * (q₁ + s + 1)) := by
          dsimp [A]
          ring
        rw [heq]
        exact (le_max_left _ _).trans (Nat.le_add_right _ _)
      have hcolCoef : 1 + w * (3 + 2 * q₂) ≤ T := by
        dsimp [T, stepCap]
        omega
      constructor
      · change Q * (2 + s + A * prev.2) ≤ M * T ^ (k + 1)
        have hA := Nat.mul_le_mul_left A hcol
        have hbase' : 2 + s ≤ (2 + s) * (M * T ^ k) := by
          calc
            2 + s = (2 + s) * 1 := by omega
            _ ≤ (2 + s) * (M * T ^ k) := Nat.mul_le_mul_left _ hpow
        have hsum : 2 + s + A * prev.2 ≤
            (2 + s + A) * (M * T ^ k) := by
          calc
            _ ≤ (2 + s) * (M * T ^ k) + A * (M * T ^ k) := by omega
            _ = (2 + s + A) * (M * T ^ k) := by ring
        calc
          _ ≤ Q * ((2 + s + A) * (M * T ^ k)) := Nat.mul_le_mul_left Q hsum
          _ = (Q * (2 + s + A)) * (M * T ^ k) := by ring
          _ ≤ T * (M * T ^ k) := Nat.mul_le_mul_right _ hrowCoef
          _ = M * T ^ (k + 1) := by rw [pow_succ]; ring
      · change 1 + w * (3 + q₂ * (1 + prev.1)) ≤ M * T ^ (k + 1)
        have hinner : 1 + prev.1 ≤ 2 * (M * T ^ k) := by omega
        have hmult := Nat.mul_le_mul_left q₂ hinner
        have hbase' : 3 ≤ 3 * (M * T ^ k) := by
          calc
            3 = 3 * 1 := by omega
            _ ≤ 3 * (M * T ^ k) := Nat.mul_le_mul_left _ hpow
        have hsum : 3 + q₂ * (1 + prev.1) ≤
            (3 + 2 * q₂) * (M * T ^ k) := by
          calc
            _ ≤ 3 * (M * T ^ k) + q₂ * (2 * (M * T ^ k)) := by omega
            _ = (3 + 2 * q₂) * (M * T ^ k) := by ring
        have hwmult := Nat.mul_le_mul_left w hsum
        have hone : 1 ≤ M * T ^ k := hpow
        have htotal : 1 + w * (3 + q₂ * (1 + prev.1)) ≤
            (1 + w * (3 + 2 * q₂)) * (M * T ^ k) := by
          calc
            _ ≤ M * T ^ k + w * ((3 + 2 * q₂) * (M * T ^ k)) := by omega
            _ = (1 + w * (3 + 2 * q₂)) * (M * T ^ k) := by ring
        calc
          _ ≤ (1 + w * (3 + 2 * q₂)) * (M * T ^ k) := htotal
          _ ≤ T * (M * T ^ k) := Nat.mul_le_mul_right _ hcolCoef
          _ = M * T ^ (k + 1) := by rw [pow_succ]; ring

/-- The *actual final paired sampler* draw cap, with both independent
families of labels counted, not merely a one-entry generator cap. -/
theorem drawCap_le (s q₁ q₂ w Q p k mX mY : ℕ) :
    drawCap s q₁ q₂ w Q p k mX mY ≤
      1 + (mX + mY) * (max p 1 * (stepCap s q₁ q₂ w Q) ^ k) := by
  have hb := drawBounds_le_stepCap_pow s q₁ q₂ w Q p 1 k (by omega)
  unfold drawCap sampleDrawBound
  have hX := Nat.mul_le_mul_left mX hb.1
  have hY := Nat.mul_le_mul_left mY hb.2
  nlinarith

/-- Under the literal public arithmetic check, all five recursive
widths fit below `2^(7L)`. This bounds the actual per-level draw multiplier,
including both tagged-column and graph-row branches. -/
theorem scheduled_stepCap_le {n m : ℕ} [NeZero n]
    (L Δ : ℕ) (γ : ℚ)
    (hc : CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) L Δ γ) :
    stepCap (width L) (width L - 2) (outerWidth L)
      (restorationWidth L) (coverWidth n m L Δ γ) ≤ 2 ^ (25 * L) := by
  have hc' := hc
  rcases hc' with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    hover, hL, _⟩
  let B := 2 ^ (7 * L)
  have hB1 : 1 ≤ B := by dsimp [B]; exact Nat.one_le_two_pow
  have hExp : exponent L ≤ 7 * L := by
    unfold SourceOverheadBounds.overhead at hover
    omega
  have hOuter : outerExponent L ≤ 7 * L := by
    unfold SourceOverheadBounds.overhead at hover
    omega
  have hr : restorationDepth L ≤ 7 * L := by
    unfold SourceOverheadBounds.overhead at hover
    dsimp [restorationDepth]
    omega
  have hq : coverDepth n m L Δ γ ≤ 7 * L := by
    unfold SourceOverheadBounds.overhead at hover
    dsimp [coverDepth]
    omega
  have hs : width L ≤ B := by
    exact pow_le_pow_right₀ (by omega) hExp
  have hq₁ : width L - 2 ≤ B := (Nat.sub_le _ _).trans hs
  have hq₂ : outerWidth L ≤ B := by
    exact pow_le_pow_right₀ (by omega) hOuter
  have hw : restorationWidth L ≤ B := by
    exact pow_le_pow_right₀ (by omega) hr
  have hQ : coverWidth n m L Δ γ ≤ B := by
    rw [show coverWidth n m L Δ γ = 2 ^ coverDepth n m L Δ γ from
      SourceOverheadBounds.actualQ_pow (V := Fin n) (E := Fin m) L γ Δ]
    exact pow_le_pow_right₀ (by omega) hq
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
  have hrow : coverWidth n m L Δ γ *
      (3 + 2 * width L + width L * ((width L - 2) + width L + 1)) ≤
      8 * B ^ 3 := by
    have hsub : coverWidth n m L Δ γ *
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
  have hcol : 1 + restorationWidth L * (3 + 2 * outerWidth L) ≤
      8 * B ^ 3 := by
    have hsub : 1 + restorationWidth L * (3 + 2 * outerWidth L) ≤
        1 + B * (3 + 2 * B) := by
      have hinner : 3 + 2 * outerWidth L ≤ 3 + 2 * B := by omega
      have hmul := Nat.mul_le_mul hw hinner
      omega
    have hpoly : 1 + B * (3 + 2 * B) ≤ 8 * B ^ 3 := by
      nlinarith only [hB1, hB2, hB3]
    exact hsub.trans hpoly
  have hT : stepCap (width L) (width L - 2) (outerWidth L)
      (restorationWidth L) (coverWidth n m L Δ γ) ≤ 16 * B ^ 3 := by
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

/-- Each side of the actual sampled rectangle has a separate finite bound.
This charges the final iid sample counts used by `drawCap`. -/
theorem scheduled_each_dimension_le {n m : ℕ} [NeZero n]
    (L Δ : ℕ) (γ : ℚ)
    (hc : CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) L Δ γ) (k : ℕ) :
    sourceRows L (restorationDepth L) (coverDepth n m L Δ γ) k ≤
        2 ^ (29 * (k + 1) * L) ∧
    sourceCols L (restorationDepth L) (coverDepth n m L Δ γ) k ≤
        2 ^ (29 * (k + 1) * L) := by
  have hc' := hc
  rcases hc' with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    hover, hL, hseed⟩
  let d₀ := LookupSeed.exponent L + 1
  let h := SourceOverheadBounds.overhead
    (V := Fin n) (E := Fin m) L Δ γ
  let B := d₀ + k * h
  let H := d₀ + k * h + k
  have hL1 : 1 ≤ L := by omega
  have hb := ReductionDimensions.iteration_budgets d₀ h k L hseed hover hL1
  have hexp : 2 * B + H + 7 ≤ 29 * (k + 1) * L := by
    dsimp [B, H]
    nlinarith only [hb.1, hb.2, hL1]
  have hbudget : sourceBudget L (restorationDepth L)
      (coverDepth n m L Δ γ) k = B := by
    dsimp [sourceBudget, B, d₀, h, SourceOverheadBounds.overhead,
      restorationDepth, coverDepth]
  have hcost : sourceCost L (restorationDepth L)
      (coverDepth n m L Δ γ) k = H := by
    dsimp [sourceCost, H, d₀, h, SourceOverheadBounds.overhead,
      restorationDepth, coverDepth]
    ring
  have hcol : sourceCols L (restorationDepth L)
      (coverDepth n m L Δ γ) k ≤ 2 ^ (29 * (k + 1) * L) := by
    have hh := ReductionDimensions.columnDraws_le_pow B H
    have hh' := hh.trans (pow_le_pow_right₀ (by omega) hexp)
    simpa only [sourceCols, sourceRank, hbudget, hcost] using hh'
  constructor
  · have hrow := ReductionDimensions.rowDraws_le_columnDraws
      (compressionEntropy (sourceRank L (restorationDepth L)
        (coverDepth n m L Δ γ) k)
        (sourceCost L (restorationDepth L)
          (coverDepth n m L Δ γ) k)) L hL1
    exact hrow.trans hcol
  · exact hcol

/-- Actual final paired sampler draw requests under the public check,
including the `p` lookup-seed row draws and every sampled row/column. -/
theorem scheduled_drawCap_le {n m : ℕ} [NeZero n]
    (L Δ : ℕ) (γ : ℚ)
    (hc : CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) L Δ γ) (k : ℕ) :
    drawCap (width L) (width L - 2) (outerWidth L)
      (restorationWidth L) (coverWidth n m L Δ γ)
      (LookupSeed.width L) k
      (sourceRows L (restorationDepth L) (coverDepth n m L Δ γ) k)
      (sourceCols L (restorationDepth L) (coverDepth n m L Δ γ) k) ≤
      2 ^ (60 * (k + 1) * L) := by
  have hc' := hc
  rcases hc' with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, hL, hseed⟩
  let mX := sourceRows L (restorationDepth L) (coverDepth n m L Δ γ) k
  let mY := sourceCols L (restorationDepth L) (coverDepth n m L Δ γ) k
  let p := LookupSeed.width L
  let T := stepCap (width L) (width L - 2) (outerWidth L)
    (restorationWidth L) (coverWidth n m L Δ γ)
  have hdim := scheduled_each_dimension_le L Δ γ hc k
  have hT := scheduled_stepCap_le L Δ γ hc
  have hpExp : LookupSeed.exponent L ≤ L := by omega
  have hp : p ≤ 2 ^ L := pow_le_pow_right₀ (by omega) hpExp
  have hTk : T ^ k ≤ (2 ^ (25 * L)) ^ k := Nat.pow_le_pow_left hT _
  have hraw := drawCap_le (width L) (width L - 2) (outerWidth L)
    (restorationWidth L) (coverWidth n m L Δ γ) p k mX mY
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

/-- The actual alphabet cap of the final capped sampler is bounded by a
public dyadic power. The vertex count and seed-column width are included. -/
theorem scheduled_alphabetCap_le {n m : ℕ} [NeZero n]
    (L Δ : ℕ) (γ : ℚ)
    (hc : CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) L Δ γ) :
    alphabetCap (width L) (width L - 2) (outerWidth L)
      (restorationWidth L) (coverWidth n m L Δ γ)
      n (LookupSeed.width L) ≤ 2 ^ (8 * L) := by
  have hc' := hc
  rcases hc' with ⟨_, hsize, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    hover, hL, hseed⟩
  let B := 2 ^ (7 * L)
  have hExp : exponent L ≤ 7 * L := by
    unfold SourceOverheadBounds.overhead at hover
    omega
  have hOuter : outerExponent L ≤ 7 * L := by
    unfold SourceOverheadBounds.overhead at hover
    omega
  have hr : restorationDepth L ≤ 7 * L := by
    unfold SourceOverheadBounds.overhead at hover
    dsimp [restorationDepth]
    omega
  have hq : coverDepth n m L Δ γ ≤ 7 * L := by
    unfold SourceOverheadBounds.overhead at hover
    dsimp [coverDepth]
    omega
  have hs : width L ≤ B := pow_le_pow_right₀ (by omega) hExp
  have hq₁ : width L - 2 ≤ B := (Nat.sub_le _ _).trans hs
  have hq₂ : outerWidth L ≤ B := pow_le_pow_right₀ (by omega) hOuter
  have hw : restorationWidth L ≤ B := pow_le_pow_right₀ (by omega) hr
  have hQ : coverWidth n m L Δ γ ≤ B := by
    rw [show coverWidth n m L Δ γ = 2 ^ coverDepth n m L Δ γ from
      SourceOverheadBounds.actualQ_pow (V := Fin n) (E := Fin m) L γ Δ]
    exact pow_le_pow_right₀ (by omega) hq
  have hvertex : n ≤ B := by
    have hs4 := width_admissible L
    have hn : n ≤ outerWidth L := by
      simp only [Fintype.card_fin] at hsize
      omega
    exact hn.trans hq₂
  have hpExp : LookupSeed.exponent L ≤ 7 * L := by omega
  have hp : LookupSeed.width L ≤ B :=
    pow_le_pow_right₀ (by omega) hpExp
  have hB512 : 512 ≤ B := by
    have he : 9 ≤ 7 * L := by omega
    have hp' : 2 ^ 9 ≤ B := pow_le_pow_right₀ (by omega) he
    norm_num at hp' ⊢
    exact hp'
  have hB2 : 2 ≤ B := by omega
  have hraw : alphabetCap (width L) (width L - 2) (outerWidth L)
      (restorationWidth L) (coverWidth n m L Δ γ)
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

/-- The allocated bit width of each uniform-request attempt, not an
unbounded `log` idealization. -/
theorem scheduled_alphabet_bitWidth_le {n m : ℕ} [NeZero n]
    (L Δ : ℕ) (γ : ℚ)
    (hc : CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) L Δ γ) :
    Nat.clog 2 (alphabetCap (width L) (width L - 2) (outerWidth L)
      (restorationWidth L) (coverWidth n m L Δ γ)
      n (LookupSeed.width L)) ≤ 8 * L :=
  Nat.clog_le_of_le_pow (scheduled_alphabetCap_le L Δ γ hc)

/-- A power bound on actual draw requests yields the exact rejection-cap
logarithm bound, including its `2^12` slack and final `+1`. -/
theorem rejectionAttemptCap_le_of_pow (N X : ℕ) (hN : N ≤ 2 ^ X) :
    rejectionAttemptCap N ≤ 13 + X := by
  have hraw : 2 ^ 12 * N ≤ 2 ^ (12 + X) := by
    rw [pow_add]
    exact Nat.mul_le_mul_left _ hN
  have hclog : Nat.clog 2 (2 ^ 12 * N) ≤ 12 + X :=
    Nat.clog_le_of_le_pow hraw
  unfold rejectionAttemptCap
  omega

/-- The polynomial overhead from rejection attempts and the alphabet
bit-width is absorbed into a fixed extra exponential allowance. -/
private theorem allocation_factor_le (K L : ℕ) (hK : 1 ≤ K) (hL : 16 ≤ L) :
    (73 * K * L) * (8 * L) ≤ 2 ^ (20 * K * L) := by
  have hKpow := WidthDomination.nat_le_two_pow K
  have hLpow := WidthDomination.nat_le_two_pow L
  have hA : 584 * K ≤ 2 ^ 10 * 2 ^ K :=
    Nat.mul_le_mul (by norm_num : 584 ≤ 2 ^ 10) hKpow
  have hB : L * L ≤ 2 ^ L * 2 ^ L := Nat.mul_le_mul hLpow hLpow
  have hmul := Nat.mul_le_mul hA hB
  have hExp : 10 + K + 2 * L ≤ 20 * K * L := by
    nlinarith only [hK, hL]
  calc
    _ = (584 * K) * (L * L) := by ring
    _ ≤ (2 ^ 10 * 2 ^ K) * (2 ^ L * 2 ^ L) := hmul
    _ = 2 ^ (10 + K + 2 * L) := by
      rw [pow_add, pow_add]
      ring
    _ ≤ 2 ^ (20 * K * L) :=
      pow_le_pow_right₀ (by omega) hExp

/-- Generic arithmetic for the actual fair-bit allocation. Both the
final draw count and alphabet-ticket width are explicit inputs here; the
scheduled theorem below proves them from the public check. -/
theorem inputBitCount_le_of_caps (V : Type) [Fintype V]
    (s q₁ q₂ w Q p k mX mY L K : ℕ)
    (hK : 1 ≤ K) (hL : 16 ≤ L)
    (hN : drawCap s q₁ q₂ w Q p k mX mY ≤ 2 ^ (60 * K * L))
    (hB : Nat.clog 2 (alphabetCap s q₁ q₂ w Q (Fintype.card V) p) ≤ 8 * L) :
    RecursiveSamplingMaterialization.inputBitCount V
      s q₁ q₂ w Q p k mX mY ≤ 2 ^ (80 * K * L) := by
  let X := 60 * K * L
  let N := drawCap s q₁ q₂ w Q p k mX mY
  let R := rejectionAttemptCap N
  have hR : R ≤ 13 + X := rejectionAttemptCap_le_of_pow N X hN
  have hR' : R ≤ 73 * K * L := by
    dsimp [X] at hR
    nlinarith only [hR, hK, hL]
  have hfactor := allocation_factor_le K L hK hL
  have hprod : N * (R * Nat.clog 2
      (alphabetCap s q₁ q₂ w Q (Fintype.card V) p)) ≤
      2 ^ X * ((73 * K * L) * (8 * L)) :=
    Nat.mul_le_mul hN (Nat.mul_le_mul hR' hB)
  have htotal : N * (R * Nat.clog 2
      (alphabetCap s q₁ q₂ w Q (Fintype.card V) p)) ≤
      2 ^ X * 2 ^ (20 * K * L) :=
    hprod.trans (Nat.mul_le_mul_left _ hfactor)
  have hcalc : N * (R * Nat.clog 2
      (alphabetCap s q₁ q₂ w Q (Fintype.card V) p)) ≤
      2 ^ (80 * K * L) := by
    calc
      _ ≤ 2 ^ X * 2 ^ (20 * K * L) := htotal
      _ = 2 ^ (80 * K * L) := by
        rw [← pow_add]
        congr 1
        dsimp [X]
        ring
  simpa only [RecursiveSamplingMaterialization.inputBitCount,
    RecursiveSamplingTape.bitCount] using hcalc

/-- The length of the actual capped sampler's allocated fair-bit list.
This includes every final iid row and column, the seed-row draw cap `p`,
the rejection-attempt logarithm, and the alphabet ticket bit-width. -/
theorem scheduled_inputBitCount_le {n m : ℕ} [NeZero n]
    (L Δ : ℕ) (γ : ℚ)
    (hc : CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) L Δ γ) (k : ℕ) :
    RecursiveSamplingMaterialization.inputBitCount (Fin n)
      (width L) (width L - 2) (outerWidth L)
      (restorationWidth L) (coverWidth n m L Δ γ)
      (LookupSeed.width L) k
      (sourceRows L (restorationDepth L) (coverDepth n m L Δ γ) k)
      (sourceCols L (restorationDepth L) (coverDepth n m L Δ γ) k) ≤
      2 ^ (80 * (k + 1) * L) := by
  have hc' := hc
  rcases hc' with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, hL, _⟩
  exact inputBitCount_le_of_caps (Fin n)
    (width L) (width L - 2) (outerWidth L)
    (restorationWidth L) (coverWidth n m L Δ γ)
    (LookupSeed.width L) k
    (sourceRows L (restorationDepth L) (coverDepth n m L Δ γ) k)
    (sourceCols L (restorationDepth L) (coverDepth n m L Δ γ) k)
    L (k + 1) (by omega) hL
    (scheduled_drawCap_le L Δ γ hc k)
    (by simpa only [Fintype.card_fin] using
      scheduled_alphabet_bitWidth_le L Δ γ hc)

/-- At the actual graph-size exponent, the public size cutoff supplies
the check needed for the same fair-bit allocation bound. -/
theorem at_size_inputBitCount_le {n m : ℕ} [NeZero n]
    (Δ : ℕ) (γ : ℚ) (edge : Fin m → Bool → Fin n)
    (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hsize : CompletePublicScheduleScratch.sizeThreshold Δ γ ≤ n)
    (k : ℕ) :
    RecursiveSamplingMaterialization.inputBitCount (Fin n)
      (width (Nat.clog 2 n)) (width (Nat.clog 2 n) - 2)
      (outerWidth (Nat.clog 2 n))
      (restorationWidth (Nat.clog 2 n))
      (coverWidth n m (Nat.clog 2 n) Δ γ)
      (LookupSeed.width (Nat.clog 2 n)) k
      (sourceRows (Nat.clog 2 n) (restorationDepth (Nat.clog 2 n))
        (coverDepth n m (Nat.clog 2 n) Δ γ) k)
      (sourceCols (Nat.clog 2 n) (restorationDepth (Nat.clog 2 n))
        (coverDepth n m (Nat.clog 2 n) Δ γ) k) ≤
      2 ^ (80 * (k + 1) * Nat.clog 2 n) :=
  scheduled_inputBitCount_le (Nat.clog 2 n) Δ γ
    (checksAtSize Δ γ edge hγ hΔ hincident hdegree hsize) k

/-- A conservative polynomial form for the actual fair-bit list, distinct
from the printed table entry count and from any machine-time statement. -/
theorem at_size_inputBitCount_le_poly {n m : ℕ} [NeZero n]
    (Δ : ℕ) (γ : ℚ) (edge : Fin m → Bool → Fin n)
    (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hsize : CompletePublicScheduleScratch.sizeThreshold Δ γ ≤ n)
    (hn : 2 ≤ n) (k : ℕ) :
    RecursiveSamplingMaterialization.inputBitCount (Fin n)
      (width (Nat.clog 2 n)) (width (Nat.clog 2 n) - 2)
      (outerWidth (Nat.clog 2 n))
      (restorationWidth (Nat.clog 2 n))
      (coverWidth n m (Nat.clog 2 n) Δ γ)
      (LookupSeed.width (Nat.clog 2 n)) k
      (sourceRows (Nat.clog 2 n) (restorationDepth (Nat.clog 2 n))
        (coverDepth n m (Nat.clog 2 n) Δ γ) k)
      (sourceCols (Nat.clog 2 n) (restorationDepth (Nat.clog 2 n))
        (coverDepth n m (Nat.clog 2 n) Δ γ) k) ≤
      n ^ (160 * (k + 1)) := by
  have hceil : 2 ^ Nat.clog 2 n ≤ n ^ 2 := by
    have h := CappedSampler.ticketSize_le_twice n (by omega)
    change 2 ^ Nat.clog 2 n ≤ 2 * n at h
    have htwice : 2 * n ≤ n ^ 2 := by nlinarith
    exact h.trans htwice
  calc
    _ ≤ 2 ^ (80 * (k + 1) * Nat.clog 2 n) :=
      at_size_inputBitCount_le Δ γ edge hγ hΔ hincident hdegree hsize k
    _ = (2 ^ Nat.clog 2 n) ^ (80 * (k + 1)) := by
      rw [← pow_mul]
      congr 1
      ring
    _ ≤ (n ^ 2) ^ (80 * (k + 1)) := Nat.pow_le_pow_left hceil _
    _ = n ^ (160 * (k + 1)) := by
      rw [← pow_mul]
      congr 1
      ring

/-- The underlying Boolean list in every correctly sized actual
`TapeList` has the same polynomial length bound. This is a storage/input
length statement, not an execution-time bound. -/
theorem at_size_tapeList_length_le_poly {n m : ℕ} [NeZero n]
    (Δ : ℕ) (γ : ℚ) (edge : Fin m → Bool → Fin n)
    (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hsize : CompletePublicScheduleScratch.sizeThreshold Δ γ ≤ n)
    (hn : 2 ≤ n) (k : ℕ)
    (bits : RecursiveSamplingMaterialization.TapeList (Fin n)
      (width (Nat.clog 2 n)) (width (Nat.clog 2 n) - 2)
      (outerWidth (Nat.clog 2 n))
      (restorationWidth (Nat.clog 2 n))
      (coverWidth n m (Nat.clog 2 n) Δ γ)
      (LookupSeed.width (Nat.clog 2 n)) k
      (sourceRows (Nat.clog 2 n) (restorationDepth (Nat.clog 2 n))
        (coverDepth n m (Nat.clog 2 n) Δ γ) k)
      (sourceCols (Nat.clog 2 n) (restorationDepth (Nat.clog 2 n))
        (coverDepth n m (Nat.clog 2 n) Δ γ) k)) :
    bits.val.length ≤ n ^ (160 * (k + 1)) := by
  have hlen : bits.val.length =
      RecursiveSamplingMaterialization.inputBitCount (Fin n)
        (width (Nat.clog 2 n)) (width (Nat.clog 2 n) - 2)
        (outerWidth (Nat.clog 2 n))
        (restorationWidth (Nat.clog 2 n))
        (coverWidth n m (Nat.clog 2 n) Δ γ)
        (LookupSeed.width (Nat.clog 2 n)) k
        (sourceRows (Nat.clog 2 n) (restorationDepth (Nat.clog 2 n))
          (coverDepth n m (Nat.clog 2 n) Δ γ) k)
        (sourceCols (Nat.clog 2 n) (restorationDepth (Nat.clog 2 n))
          (coverDepth n m (Nat.clog 2 n) Δ γ) k) := bits.property
  exact hlen.le.trans (at_size_inputBitCount_le_poly
    Δ γ edge hγ hΔ hincident hdegree hsize hn k)

end Paper2.FairBitCap
