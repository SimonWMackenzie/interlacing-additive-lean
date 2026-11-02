import CurrentAdditive.QuarticThrMain
import Paper2.SCCaps

/-! Source-faithful v27 scalar and code-size bounds for physical-machine
clock transfer. -/

namespace Paper2.CurrentAdditive.QuarticClockCaps

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

open Paper2.CurrentAdditive.QuarticConstructor
open Paper2.GeneratorCode Paper2.GeneratorSource Paper2.GeneratorSerialization
  Paper2.GeneratorSize
open CurrentAdditive.RandomizedSchedule

/-- Every public v27 scalar is bounded by the same coarse `2^(7L)` cap used
by the generic generator arithmetic. -/
theorem scalar_caps27 {n m : ℕ} [NeZero n] (L Δ : ℕ) (γ : ℚ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) L Δ γ) :
    let M := Paper2.GeneratorPublicCap.publicCap L
    512 ≤ M ∧ n ≤ M ∧ LookupSeed.width L ≤ M ∧
      SourceProfileParameters.width L ≤ M ∧
      SourceProfileParameters.width L - 2 ≤ M ∧
      SourceProfileParameters.outerWidth L ≤ M ∧
      width27 L ≤ M ∧
      Q27 (V := Fin n) (E := Fin m) L γ Δ ≤ M ∧
      m ≤ M ∧ 16 ≤ L := by
  have h := hc
  dsimp only [CurrentAdditive.QuarticSchedule.Checks27] at h
  rcases h with ⟨hcoord, hpopulation, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    hover, hL, hseed⟩
  let M := Paper2.GeneratorPublicCap.publicCap L
  have hM : 512 ≤ M := by
    dsimp [M, Paper2.GeneratorPublicCap.publicCap]
    have h9 : 9 ≤ 7 * L := by omega
    exact (show 512 = 2 ^ 9 by norm_num).trans_le
      (pow_le_pow_right₀ (by omega) h9)
  have hExp : SourceProfileParameters.exponent L ≤ 7 * L := by
    unfold CurrentAdditive.RandomizedSchedule.overhead27 at hover
    omega
  have hOuter : SourceProfileParameters.outerExponent L ≤ 7 * L := by
    unfold CurrentAdditive.RandomizedSchedule.overhead27 at hover
    omega
  have hRest : 4 * RestorationWidthScheduleScratch.ell L ≤ 7 * L := by
    unfold CurrentAdditive.RandomizedSchedule.overhead27 at hover
    omega
  have hCover : q27 (V := Fin n) (E := Fin m) L γ Δ ≤ 7 * L := by
    unfold CurrentAdditive.RandomizedSchedule.overhead27 at hover
    omega
  have hp : LookupSeed.width L ≤ M := by
    have he : LookupSeed.exponent L ≤ 7 * L := by omega
    unfold LookupSeed.width M Paper2.GeneratorPublicCap.publicCap
    exact pow_le_pow_right₀ (by omega) he
  have hs : SourceProfileParameters.width L ≤ M := by
    unfold SourceProfileParameters.width M Paper2.GeneratorPublicCap.publicCap
    exact pow_le_pow_right₀ (by omega) hExp
  have hq₁ : SourceProfileParameters.width L - 2 ≤ M :=
    (Nat.sub_le _ _).trans hs
  have hq₂ : SourceProfileParameters.outerWidth L ≤ M := by
    unfold SourceProfileParameters.outerWidth M Paper2.GeneratorPublicCap.publicCap
    exact pow_le_pow_right₀ (by omega) hOuter
  have hw : width27 L ≤ M := by
    unfold width27 M Paper2.GeneratorPublicCap.publicCap
    exact pow_le_pow_right₀ (by omega) hRest
  have hQ : Q27 (V := Fin n) (E := Fin m) L γ Δ ≤ M := by
    rw [Q27_dyadic (V := Fin n) (E := Fin m) L γ Δ]
    dsimp [M, Paper2.GeneratorPublicCap.publicCap]
    exact pow_le_pow_right₀ (by omega) hCover
  have hs4 : 4 ≤ SourceProfileParameters.width L := by
    have hwide := SourceProfileParameters.width_admissible L
    omega
  have hnq₂ : n ≤ SourceProfileParameters.outerWidth L := by
    simp only [Fintype.card_fin] at hpopulation
    omega
  unfold SourceRepetitionScratch.coordinateAdmissible at hcoord
  have h1 := SourcePadding.le_powTwoCeil
    (12 * SourceProfileParameters.width L * Fintype.card (Fin m))
  simp only [Fintype.card_fin] at h1 hcoord
  have hs1 : 1 ≤ SourceProfileParameters.width L := by omega
  have hm : m ≤ SourceProfileParameters.outerWidth L := by
    have hmul : 1 * m ≤ (12 * SourceProfileParameters.width L) * m :=
      Nat.mul_le_mul_right m (by omega : 1 ≤ 12 * SourceProfileParameters.width L)
    have : m ≤ 12 * SourceProfileParameters.width L * m := by simpa using hmul
    omega
  exact ⟨hM, hnq₂.trans hq₂, hp, hs, hq₁, hq₂, hw, hQ, hm.trans hq₂, hL⟩

/-- The actual quartic-schedule recursive codes fit a uniform exponential
length bound, at every recursive depth. -/
theorem code_size27 {n m : ℕ} [NeZero n] (L Δ : ℕ) (γ : ℚ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) L Δ γ) (k : ℕ) :
    let c := seedRecursiveCodes n (LookupSeed.width L)
      (SourceProfileParameters.width L)
      (SourceProfileParameters.width L - 2)
      (SourceProfileParameters.outerWidth L)
      (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ) k
    codeSize c.1 + codeSize c.2 + 1 ≤ 2 ^ (144 * (k + 1) * L) := by
  obtain ⟨hM, hn, hp, hs, hq₁, hq₂, hw, hQ, _, hL⟩ :=
    scalar_caps27 L Δ γ hc
  let M := Paper2.GeneratorPublicCap.publicCap L
  have hsize := seed_total_le_cap M n (LookupSeed.width L)
    (SourceProfileParameters.width L)
    (SourceProfileParameters.width L - 2)
    (SourceProfileParameters.outerWidth L)
    (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ) k
    hM hn hp hs hq₁ hq₂ hw hQ
  have hM1 : 1 ≤ M := by omega
  have hplus : M + 1 ≤ 2 ^ (8 * L) := by
    calc
      M + 1 ≤ 2 * M := by omega
      _ = 2 ^ (7 * L + 1) := by
        dsimp [M, Paper2.GeneratorPublicCap.publicCap]
        rw [pow_add]
        ring
      _ ≤ 2 ^ (8 * L) := pow_le_pow_right₀ (by omega) (by omega)
  have hpow := Nat.pow_le_pow_left hplus (18 * (k + 1))
  calc
    codeSize (seedRecursiveCodes n (LookupSeed.width L)
        (SourceProfileParameters.width L) (SourceProfileParameters.width L - 2)
        (SourceProfileParameters.outerWidth L) (width27 L)
        (Q27 (V := Fin n) (E := Fin m) L γ Δ) k).1 +
        codeSize (seedRecursiveCodes n (LookupSeed.width L)
        (SourceProfileParameters.width L) (SourceProfileParameters.width L - 2)
        (SourceProfileParameters.outerWidth L) (width27 L)
        (Q27 (V := Fin n) (E := Fin m) L γ Δ) k).2 + 1
      ≤ (M + 1) ^ (18 * (k + 1)) := hsize
    _ ≤ (2 ^ (8 * L)) ^ (18 * (k + 1)) := hpow
    _ = 2 ^ (144 * (k + 1) * L) := by
      rw [← pow_mul]
      congr 1
      ring

theorem code_cap27 {n m : ℕ} [NeZero n] (L Δ : ℕ) (γ : ℚ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) L Δ γ)
    (K k : ℕ) (hk : k ≤ K + 1) :
    let c := seedRecursiveCodes n (LookupSeed.width L)
      (SourceProfileParameters.width L)
      (SourceProfileParameters.width L - 2)
      (SourceProfileParameters.outerWidth L)
      (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ) k
    codeSize c.1 + codeSize c.2 + 1 ≤ 2 ^ (288 * ((K + 1) * L)) := by
  have h := code_size27 L Δ γ hc k
  exact h.trans (pow_le_pow_right₀ (by norm_num) (by nlinarith))

/-- Both literal v27 sampled matrix dimensions fit the same bound as the
generic row and column counting argument, using v27's own overhead. -/
theorem dims_cap27 {n m : ℕ} [NeZero n] (L Δ : ℕ) (γ : ℚ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) L Δ γ) (k : ℕ) :
    SourceRecursiveNoSampling.sourceRows L
      (4 * RestorationWidthScheduleScratch.ell L)
      (q27 (V := Fin n) (E := Fin m) L γ Δ) k ≤
        2 ^ (29 * (k + 1) * L) ∧
    SourceRecursiveNoSampling.sourceCols L
      (4 * RestorationWidthScheduleScratch.ell L)
      (q27 (V := Fin n) (E := Fin m) L γ Δ) k ≤
        2 ^ (29 * (k + 1) * L) := by
  have h := hc
  dsimp only [CurrentAdditive.QuarticSchedule.Checks27] at h
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    hover, hL, hseed⟩
  let d₀ := LookupSeed.exponent L + 1
  let h := overhead27 (V := Fin n) (E := Fin m) L Δ γ
  let B := d₀ + k * h
  let H := d₀ + k * h + k
  have hL1 : 1 ≤ L := by omega
  have hb := ReductionDimensions.iteration_budgets d₀ h k L hseed hover hL1
  have hexp : 2 * B + H + 7 ≤ 29 * (k + 1) * L := by
    dsimp [B, H]
    nlinarith only [hb.1, hb.2, hL1]
  have hbudget : SourceRecursiveNoSampling.sourceBudget L
      (4 * RestorationWidthScheduleScratch.ell L)
      (q27 (V := Fin n) (E := Fin m) L γ Δ) k = B := by
    dsimp [SourceRecursiveNoSampling.sourceBudget, B, d₀, h, overhead27]
  have hcost : SourceRecursiveNoSampling.sourceCost L
      (4 * RestorationWidthScheduleScratch.ell L)
      (q27 (V := Fin n) (E := Fin m) L γ Δ) k = H := by
    dsimp [SourceRecursiveNoSampling.sourceCost, H, d₀, h, overhead27]
    ring
  have hcol : SourceRecursiveNoSampling.sourceCols L
      (4 * RestorationWidthScheduleScratch.ell L)
      (q27 (V := Fin n) (E := Fin m) L γ Δ) k ≤
      2 ^ (29 * (k + 1) * L) := by
    have hh := ReductionDimensions.columnDraws_le_pow B H
    have hh' := hh.trans (pow_le_pow_right₀ (by omega) hexp)
    simpa only [SourceRecursiveNoSampling.sourceCols,
      SourceRecursiveNoSampling.sourceRank, hbudget, hcost] using hh'
  constructor
  · have hrow := ReductionDimensions.rowDraws_le_columnDraws
      (compressionEntropy
        (SourceRecursiveNoSampling.sourceRank L
          (4 * RestorationWidthScheduleScratch.ell L)
          (q27 (V := Fin n) (E := Fin m) L γ Δ) k)
        (SourceRecursiveNoSampling.sourceCost L
          (4 * RestorationWidthScheduleScratch.ell L)
          (q27 (V := Fin n) (E := Fin m) L γ Δ) k)) L hL1
    exact hrow.trans hcol
  · exact hcol

#print axioms scalar_caps27
#print axioms code_size27
#print axioms code_cap27
#print axioms dims_cap27

end Paper2.CurrentAdditive.QuarticClockCaps
