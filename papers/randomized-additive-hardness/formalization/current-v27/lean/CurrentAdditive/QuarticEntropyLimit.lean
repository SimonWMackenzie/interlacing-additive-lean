import CurrentAdditive.QuarticExactLimit

/-! The precursor entropy asymptotic printed just before the final output
dimension display. Its relative error is an exact rational expression. -/

namespace CurrentAdditive.QuarticExactAsymptotics

open Filter Paper2

theorem entropy_relative_exact (B k : ℕ) :
    let r : ℕ := 2^(B-1)
    let v : ℕ := 2^(B+k-1)
    let A : ℕ := r*r*v
    let Z : ℕ := compressionEntropy r (B+k)
    (Z:ℝ)/(A:ℝ) = 1 + 1/(r:ℝ) + 2/(r:ℝ)^2 := by
  let r : ℕ := 2^(B-1)
  let v : ℕ := 2^(B+k-1)
  have hr : (r:ℝ) ≠ 0 := by dsimp [r]; positivity
  have hv : (v:ℝ) ≠ 0 := by dsimp [v]; positivity
  have hZ : compressionEntropy r (B+k) = r*r*v + r*v + 2*v := by
    dsimp [compressionEntropy]
    ring
  change ((compressionEntropy r (B+k):ℕ):ℝ) / ((r*r*v:ℕ):ℝ) =
    1 + 1/(r:ℝ) + 2/(r:ℝ)^2
  rw [hZ]
  push_cast
  field_simp [hr, hv]

theorem entropy_relative_error_tendsto_zero
    (B k : ℕ → ℕ) (hB : Tendsto B atTop atTop) :
    Tendsto (fun i : ℕ =>
      let r : ℕ := 2^(B i-1)
      let v : ℕ := 2^(B i+k i-1)
      let A : ℕ := r*r*v
      let Z : ℕ := compressionEntropy r (B i+k i)
      (Z:ℝ)/(A:ℝ)-1) atTop (nhds 0) := by
  let R (i : ℕ) : ℝ := ((2^(B i-1):ℕ):ℝ)
  have hBm : Tendsto (fun i => B i - 1) atTop atTop :=
    (tendsto_sub_atTop_nat 1).comp hB
  have hPow : Tendsto (fun i => (2:ℝ)^(B i-1)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).comp hBm
  have hInv : Tendsto (fun i => (R i)⁻¹) atTop (nhds 0) := by
    simpa only [R, Nat.cast_pow, Nat.cast_ofNat] using
      (tendsto_inv_atTop_zero.comp hPow)
  have hBound : Tendsto (fun i => (R i)⁻¹ + 2*((R i)⁻¹)^2)
      atTop (nhds 0) := by
    simpa using (hInv.add (tendsto_const_nhds.mul (hInv.pow 2)) :
      Tendsto (fun i => (R i)⁻¹ + 2*((R i)⁻¹)^2) atTop
        (nhds (0 + 2*0^2)))
  apply hBound.congr'
  filter_upwards [] with i
  have hh := entropy_relative_exact (B i) (k i)
  dsimp at hh ⊢
  rw [hh]
  dsimp [R]
  ring

theorem source_entropy_relative_error_tendsto_zero
    (L r q k : ℕ → ℕ)
    (hL : Tendsto L atTop atTop)
    (hk : ∀ᶠ i in atTop, 1 ≤ k i) :
    Tendsto (fun i : ℕ =>
      let R := SourceRecursiveNoSampling.sourceRank
        (L i) (r i) (q i) (k i)
      let H := SourceRecursiveNoSampling.sourceCost
        (L i) (r i) (q i) (k i)
      let Z := compressionEntropy R H
      (Z:ℝ)/((R*R*2^(H-1):ℕ):ℝ)-1) atTop (nhds 0) := by
  let B (i : ℕ) := SourceRecursiveNoSampling.sourceBudget
    (L i) (r i) (q i) (k i)
  have hB : Tendsto B atTop atTop :=
    source_budget_tendsto_atTop L r q k hL hk
  have hh := entropy_relative_error_tendsto_zero B k hB
  apply hh.congr'
  filter_upwards [] with i
  have hH : SourceRecursiveNoSampling.sourceCost
      (L i) (r i) (q i) (k i) = B i + k i := by
    dsimp [B, SourceRecursiveNoSampling.sourceCost,
      SourceRecursiveNoSampling.sourceBudget]
    ring
  dsimp [B, SourceRecursiveNoSampling.sourceRank]
  rw [hH]

theorem printedZ27_relative_error_tendsto_zero
    (n m k : ℕ → ℕ) (Δ : ℕ) (γ : ℚ)
    (hn : Tendsto n atTop atTop)
    (hk : ∀ᶠ i in atTop, 1 ≤ k i) :
    Tendsto (fun i : ℕ =>
      let L := Nat.clog 2 (n i)
      let r := 4 * RestorationWidthScheduleScratch.ell L
      let q := CurrentAdditive.RandomizedSchedule.q27
        (V := Fin (n i)) (E := Fin (m i)) L γ Δ
      let R := SourceRecursiveNoSampling.sourceRank L r q (k i)
      let H := SourceRecursiveNoSampling.sourceCost L r q (k i)
      let Z := compressionEntropy R H
      (Z:ℝ)/((R*R*2^(H-1):ℕ):ℝ)-1) atTop (nhds 0) := by
  let L (i : ℕ) := Nat.clog 2 (n i)
  let r (i : ℕ) := 4 * RestorationWidthScheduleScratch.ell (L i)
  let q (i : ℕ) := CurrentAdditive.RandomizedSchedule.q27
    (V := Fin (n i)) (E := Fin (m i)) (L i) γ Δ
  have hh := source_entropy_relative_error_tendsto_zero L r q k
    (clog_two_tendsto_atTop n hn) hk
  simpa only [L, r, q] using hh

end CurrentAdditive.QuarticExactAsymptotics
