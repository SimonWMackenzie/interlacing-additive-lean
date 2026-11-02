import Paper2.SharpOutputSize

/-!
# Unit 4 (Paper A), segment A4-S7: T24 asymptotics with the exact coefficient 6

Owner lane `owner:a-unit4-shell` (private, 25 September 2026).
Source: lock v12 `06-reduction.tex`, proof of `thm:quantitative`:
`k = ⌊N/⌈log N⌉²⌋`, `L = ⌈log n⌉ = (1+o(1)) log N`, `log T = (6+o(1)) k log N`,
`log log T = (1+o(1)) log N`, "for every fixed `c < 1/12` the gap `k` eventually exceeds
twice the proposed error".

The sharp printed-entry upper bound `clog₂ T ≤ (6+ε) k L` is the banked
`SharpOutputSize.at_graph_size_printed_entries_le_six_plus` (which already contains the
sharp public-schedule overhead `h ≤ (1+ε/12)L`, `SharpRelative.relative_overhead`, and
`d₀ ≤ L`). This module adds: the lower bound `2^k ≤ T` from the exact
`eq:final-dimensions` definitions, the explicit-threshold growth lemmas for
`L ≤ (1+ε) log₂ N` and `log₂ k ≥ (1-ε) log₂ N`, and the final comparison
`2c · log₂T / log₂log₂T < k`. Logarithms are base 2 (the ratio `log T / log log T` is
base-invariant to first order).

The T45 size relations (`N ≤ m`, `2m ≤ Δ n`, `n ≤ N·⌈log₂(N+2)⌉^p`) enter as hypotheses: T45
is A4-S4, not proved here.

**None of these statements closes a ledger row** (T24, T03, T45, D04 stay open).
-/

namespace Paper2.Unit4Shell.Asymptotics

open Paper2 Paper2.SourceRecursiveNoSampling Paper2.ParameterizedCanonicalSource

/-! ## Elementary real bounds -/

/-- `log₂ x ≤ 3 √x` for `x > 0`. Does not close a ledger row. -/
theorem logb_le_three_sqrt {x : ℝ} (hx : 0 < x) : Real.logb 2 x ≤ 3 * Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := Real.log_le_sub_one_of_pos hs
  have h2 : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [Real.log_sqrt hx.le]; ring
  have hl2 := Real.log_two_gt_d9
  have hlog2pos : 0 < Real.log 2 := by linarith
  rw [Real.logb, div_le_iff₀ hlog2pos]
  nlinarith [mul_pos hs (by linarith : (0 : ℝ) < 3 * Real.log 2 - 2)]

/-- Explicit threshold: `a log₂(y+2) + b ≤ ε y` once `y + 2 ≥ ((3a+b+2)/ε + 1)²`.
Does not close a ledger row. -/
theorem small_log (a b ε y : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hy : 0 ≤ y) (hlarge : ((3 * a + b + 2) / ε + 1) ^ 2 ≤ y + 2) :
    a * Real.logb 2 (y + 2) + b ≤ ε * y := by
  have hy2 : 0 < y + 2 := by linarith
  set s := Real.sqrt (y + 2) with hsdef
  have hs2 : s ^ 2 = y + 2 := Real.sq_sqrt hy2.le
  have hM0 : 0 ≤ (3 * a + b + 2) / ε := by positivity
  have hM : (3 * a + b + 2) / ε + 1 ≤ s := by
    rw [hsdef]
    apply Real.le_sqrt_of_sq_le
    exact hlarge
  have hs1 : 1 ≤ s := by linarith
  have hlog : Real.logb 2 (y + 2) ≤ 3 * s := logb_le_three_sqrt hy2
  have hM' : 3 * a + b + 2 ≤ (s - 1) * ε := by
    have := (div_le_iff₀ hε).mp (show (3 * a + b + 2) / ε ≤ s - 1 by linarith)
    linarith
  have hmul : (3 * a + b + 2) * s ≤ (s - 1) * ε * s :=
    mul_le_mul_of_nonneg_right hM' (by linarith)
  have hal : a * Real.logb 2 (y + 2) ≤ a * (3 * s) := mul_le_mul_of_nonneg_left hlog ha
  nlinarith

/-- The printed rectangle has at least `2^k` entries (exact `eq:final-dimensions`).
Does not close a ledger row. -/
theorem two_pow_le_entries (L r q k : ℕ) (hL : 1 ≤ L) :
    2 ^ k ≤ sourceRows L r q k * sourceCols L r q k := by
  have hrow := compressionRowDraws_pos
    (compressionEntropy (sourceRank L r q k) (sourceCost L r q k)) L hL
  have hH : k ≤ sourceCost L r q k - 1 := by
    unfold sourceCost
    have h1 : k ≤ k * (SourceProfileParameters.exponent L +
        SourceProfileParameters.outerExponent L + SourceProfileParameters.exponent L +
        r + q + 1) := Nat.le_mul_of_pos_right k (Nat.succ_pos _)
    omega
  have hpow : 2 ^ k ≤ 2 ^ (sourceCost L r q k - 1) := Nat.pow_le_pow_right (by decide) hH
  have hE : 2 ^ (sourceCost L r q k - 1) ≤
      compressionEntropy (sourceRank L r q k) (sourceCost L r q k) := by
    unfold compressionEntropy
    exact Nat.le_mul_of_pos_left _ (by omega)
  have hcol : compressionEntropy (sourceRank L r q k) (sourceCost L r q k) ≤
      sourceCols L r q k := by
    unfold sourceCols compressionColumnDraws
    omega
  calc 2 ^ k ≤ sourceCols L r q k := hpow.trans (hE.trans hcol)
    _ ≤ sourceRows L r q k * sourceCols L r q k := Nat.le_mul_of_pos_left _ hrow

/-- Real logarithm below the natural ceiling logarithm. Does not close a ledger row. -/
theorem logb_le_clog (T : ℕ) (hT : 1 ≤ T) : Real.logb 2 T ≤ Nat.clog 2 T := by
  have hle : (T : ℝ) ≤ (2 : ℝ) ^ (Nat.clog 2 T) := by exact_mod_cast Nat.le_pow_clog (by decide) T
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have h := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) hTpos (by positivity)).mpr hle
  rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at h

/-- The final comparison, pure real form. Does not close a ledger row. -/
theorem core (c ε X k ℓ L : ℝ) (hc0 : 0 ≤ c) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hcε : 2 * c * ((6 + ε) * (1 + ε)) < 1 - ε)
    (hX : X ≤ (6 + ε) * k * L) (hL : L ≤ (1 + ε) * ℓ) (hXk : k ≤ X)
    (hk : (1 - ε) * ℓ ≤ Real.logb 2 k) (hℓ : 0 < ℓ) (hk1 : 1 ≤ k) :
    2 * c * (X / Real.logb 2 X) < k := by
  have hkpos : 0 < k := by linarith
  have hlk : 0 < Real.logb 2 k := lt_of_lt_of_le (by nlinarith) hk
  have hlX : Real.logb 2 k ≤ Real.logb 2 X :=
    (Real.logb_le_logb (by norm_num) hkpos (by linarith)).mpr hXk
  have hlXpos : 0 < Real.logb 2 X := lt_of_lt_of_le hlk hlX
  have hLpos : 0 ≤ L := by
    by_contra hneg
    push Not at hneg
    have : (6 + ε) * k * L < 0 := by
      have : 0 < (6 + ε) * k := by positivity
      nlinarith
    linarith
  have hX2 : X ≤ (6 + ε) * (1 + ε) * k * ℓ := by
    have h6k : 0 ≤ (6 + ε) * k := by positivity
    have := mul_le_mul_of_nonneg_left hL h6k
    nlinarith
  have hden : (1 - ε) * ℓ ≤ Real.logb 2 X := hk.trans hlX
  rw [mul_div_assoc', div_lt_iff₀ hlXpos]
  have hstep : 2 * c * X ≤ 2 * c * ((6 + ε) * (1 + ε) * k * ℓ) :=
    mul_le_mul_of_nonneg_left hX2 (by positivity)
  have hstep2 : k * ((1 - ε) * ℓ) ≤ k * Real.logb 2 X :=
    mul_le_mul_of_nonneg_left hden hkpos.le
  have hkl : 0 < k * ℓ := mul_pos hkpos hℓ
  nlinarith [mul_lt_mul_of_pos_right hcε hkl]

/-- A rational accuracy that makes `core` applicable for a fixed `c < 1/12`.
Does not close a ledger row. -/
theorem exists_accuracy (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12) :
    ∃ ε : ℚ, 0 < ε ∧ ε ≤ 1 / 100 ∧ 2 * c * ((6 + (ε : ℝ)) * (1 + (ε : ℝ))) < 1 - (ε : ℝ) := by
  have hpos : (0 : ℝ) < (1 - 12 * c) / 100 := by linarith
  obtain ⟨ε, hε0, hε1⟩ := exists_rat_btwn hpos
  refine ⟨ε, by exact_mod_cast hε0, ?_, ?_⟩
  · have : ((ε : ℚ) : ℝ) ≤ ((1 / 100 : ℚ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · have hε0' : (0 : ℝ) < ε := hε0
    have h2c : 2 * c < (1 - 100 * (ε : ℝ)) / 6 := by linarith
    have hq : (0 : ℝ) < (6 + (ε : ℝ)) * (1 + (ε : ℝ)) := by positivity
    have hlt := mul_lt_mul_of_pos_right h2c hq
    have hcube : (0 : ℝ) ≤ (ε : ℝ) ^ 3 := by positivity
    nlinarith

/-! ## Growth in the number `N` of source variables -/

/-- `⌈log₂ x⌉ ≤ log₂ x + 1`. Does not close a ledger row. -/
theorem clog_le_logb_add_one (x : ℕ) (hx : 1 ≤ x) :
    (Nat.clog 2 x : ℝ) ≤ Real.logb 2 x + 1 := by
  rcases Nat.lt_or_ge x 2 with hlt | h2
  · have hx1 : x = 1 := by omega
    subst hx1
    simp
  · have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) (by omega : 1 < x)
    have hpR : (2 : ℝ) ^ (Nat.clog 2 x).pred < x := by exact_mod_cast hp
    have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
    have hlt := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) (by positivity) hpR
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hlt
    have hc1 : 1 ≤ Nat.clog 2 x := Nat.succ_le_of_lt (Nat.clog_pos (by decide) (by omega))
    have hpred : ((Nat.clog 2 x).pred : ℝ) = (Nat.clog 2 x : ℝ) - 1 := by
      rw [Nat.pred_eq_sub_one, Nat.cast_sub hc1]; simp
    rw [hpred] at hlt
    linarith

/-- DRAFT name for the manuscript's `k = ⌊N/⌈log N⌉²⌋`. -/
def kOf (N : ℕ) : ℕ := N / (Nat.clog 2 N) ^ 2

/-- `L = ⌈log₂ n⌉ ≤ (1+ε) log₂ N` under the T45 upper size bound, beyond an explicit
threshold. Does not close a ledger row. -/
theorem L_le (p N n : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hN : 2 ≤ N) (hn : 1 ≤ n)
    (hsize : n ≤ N * (Nat.clog 2 (N + 2)) ^ p)
    (hlarge : ((3 * (p : ℝ) + 1 + 2) / ε + 1) ^ 2 ≤ Real.logb 2 N + 2) :
    (Nat.clog 2 n : ℝ) ≤ (1 + ε) * Real.logb 2 N := by
  set ℓ := Real.logb 2 N with hℓ
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓ, Real.le_logb_iff_rpow_le (by norm_num) hNpos]
    simpa using (show (2 : ℝ) ≤ N by exact_mod_cast hN)
  have hC1 : 1 ≤ Nat.clog 2 (N + 2) := Nat.succ_le_of_lt (Nat.clog_pos (by decide) (by omega))
  have hCR : (1 : ℝ) ≤ Nat.clog 2 (N + 2) := by exact_mod_cast hC1
  have hC : (Nat.clog 2 (N + 2) : ℝ) ≤ ℓ + 2 := by
    have h1 := clog_le_logb_add_one (N + 2) (by omega)
    have h2 : Real.logb 2 ((N + 2 : ℕ) : ℝ) ≤ ℓ + 1 := by
      have hle : ((N + 2 : ℕ) : ℝ) ≤ 2 * N := by push_cast; exact_mod_cast (by omega : N + 2 ≤ 2 * N)
      have := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) (by positivity) (by positivity)).mpr hle
      rw [Real.logb_mul (by norm_num) hNpos.ne', Real.logb_self_eq_one (by norm_num)] at this
      linarith
    linarith
  have hlogC : Real.logb 2 (Nat.clog 2 (N + 2) : ℝ) ≤ Real.logb 2 (ℓ + 2) :=
    (Real.logb_le_logb (by norm_num) (by linarith) (by linarith)).mpr hC
  have hnR : (n : ℝ) ≤ N * (Nat.clog 2 (N + 2) : ℝ) ^ p := by exact_mod_cast hsize
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hlogn : Real.logb 2 n ≤ ℓ + p * Real.logb 2 (Nat.clog 2 (N + 2) : ℝ) := by
    have := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) hnpos (by positivity)).mpr hnR
    rw [Real.logb_mul hNpos.ne' (by positivity), Real.logb_pow] at this
    linarith
  have hsmall := small_log (p : ℝ) 1 ε ℓ (by positivity) (by norm_num) hε hε1 (by linarith) hlarge
  have hL := clog_le_logb_add_one n hn
  have hp0 : (0 : ℝ) ≤ p := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hlogC hp0]

/-- `log₂ k ≥ (1-ε) log₂ N` and `k ≥ 1` for `k = ⌊N/⌈log₂N⌉²⌋`, beyond an explicit threshold.
Does not close a ledger row. -/
theorem k_log_ge (N : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hN : 2 ≤ N)
    (hlarge : ((3 * 2 + 1 + 2) / ε + 1) ^ 2 ≤ Real.logb 2 N + 2) :
    1 ≤ kOf N ∧ (1 - ε) * Real.logb 2 N ≤ Real.logb 2 (kOf N) := by
  set ℓ := Real.logb 2 N with hℓ
  set C := Nat.clog 2 N with hCdef
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓ, Real.le_logb_iff_rpow_le (by norm_num) hNpos]
    simpa using (show (2 : ℝ) ≤ N by exact_mod_cast hN)
  have hC1 : 1 ≤ C := Nat.succ_le_of_lt (Nat.clog_pos (by decide) (by omega))
  have hCR1 : (1 : ℝ) ≤ C := by exact_mod_cast hC1
  have hCle : (C : ℝ) ≤ ℓ + 1 := clog_le_logb_add_one N (by omega)
  have hlogC : Real.logb 2 (C : ℝ) ≤ Real.logb 2 (ℓ + 2) :=
    (Real.logb_le_logb (by norm_num) (by linarith) (by linarith)).mpr (by linarith)
  have hsmall := small_log 2 1 ε ℓ (by norm_num) (by norm_num) hε hε1 (by linarith) hlarge
  have hCsqpos : (0 : ℝ) < 2 * (C : ℝ) ^ 2 := by positivity
  have hlog2C : Real.logb 2 (2 * (C : ℝ) ^ 2) = 1 + 2 * Real.logb 2 (C : ℝ) := by
    rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one (by norm_num),
      Real.logb_pow]
    push_cast; ring
  -- `2 C² ≤ N`
  have h2C : 2 * (C : ℝ) ^ 2 ≤ N := by
    have : Real.logb 2 (2 * (C : ℝ) ^ 2) ≤ ℓ := by
      rw [hlog2C]; nlinarith
    exact (Real.logb_le_logb (by norm_num) hCsqpos hNpos).mp this
  -- `N < C² (k + 1)`
  have hdiv : N < C ^ 2 * (N / C ^ 2 + 1) := Nat.lt_mul_div_succ N (by positivity)
  have hdivR : (N : ℝ) < (C : ℝ) ^ 2 * ((kOf N : ℕ) + 1) := by
    have : ((N : ℕ) : ℝ) < ((C ^ 2 * (N / C ^ 2 + 1) : ℕ) : ℝ) := by exact_mod_cast hdiv
    simpa [kOf, hCdef] using this
  have hCsq : (0 : ℝ) < (C : ℝ) ^ 2 := by positivity
  have hkR : (N : ℝ) / (2 * (C : ℝ) ^ 2) ≤ kOf N := by
    rw [div_le_iff₀ hCsqpos]
    nlinarith
  have hk1R : (1 : ℝ) ≤ kOf N := by
    have : (1 : ℝ) ≤ (N : ℝ) / (2 * (C : ℝ) ^ 2) := by
      rw [le_div_iff₀ hCsqpos]; linarith
    linarith
  refine ⟨by exact_mod_cast hk1R, ?_⟩
  have hkpos : (0 : ℝ) < kOf N := by linarith
  have hmono := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2)
    (div_pos hNpos hCsqpos) hkpos).mpr hkR
  rw [Real.logb_div hNpos.ne' hCsqpos.ne', hlog2C] at hmono
  nlinarith

/-! ## The T24 comparison on the actual printed rectangle -/

/-- The actual printed-entry count of the scheduled reduction on an `n`-vertex, `m`-edge source
at gap `k`, with `L = ⌈log₂ n⌉` (exact `eq:final-dimensions`, banked definitions). -/
def printedT (n m Δ : ℕ) (γ : ℚ) (k : ℕ) : ℕ :=
  sourceRows (Nat.clog 2 n) (restorationDepth (Nat.clog 2 n))
      (coverDepth n m (Nat.clog 2 n) Δ γ) k *
    sourceCols (Nat.clog 2 n) (restorationDepth (Nat.clog 2 n))
      (coverDepth n m (Nat.clog 2 n) Δ γ) k

/-- `log₂ N ≥ Y` from `N ≥ ⌈2^Y⌉`. -/
theorem logb_ge_of_ge (Y : ℝ) (N : ℕ) (hN : ⌈(2 : ℝ) ^ Y⌉₊ ≤ N) : Y ≤ Real.logb 2 N := by
  have h1 : (2 : ℝ) ^ Y ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) h1
  exact (Real.le_logb_iff_rpow_le (by norm_num) hNpos).mpr h1

/-- **T24 asymptotic core (rectangular output).** For fixed source constants `Δ, γ`, fixed
polylog exponent `p` of the T45 size bound and fixed `0 ≤ c < 1/12`, there is an explicit `N₀`
such that for every `N ≥ N₀` and every source graph satisfying the T45 relations, the gap
`k = ⌊N/⌈log₂N⌉²⌋` exceeds `2c · log₂T / log₂log₂T`, where `T` is the actual printed-entry count.
Does not close a ledger row (T24 also needs H-A3, the estimator composition and D04). -/
theorem gap_exceeds_twice_error (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ) (p : ℕ)
    (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (n m : ℕ) [NeZero n] (edge : Fin m → Bool → Fin n),
      (∀ v, ∃ e b, edge e b = v) → (∀ v, SourceItems.degree edge v ≤ Δ) →
      N ≤ m → 2 * m ≤ Δ * n → n ≤ N * (Nat.clog 2 (N + 2)) ^ p →
      2 * c * (Real.logb 2 (printedT n m Δ γ (kOf N)) /
        Real.logb 2 (Real.logb 2 (printedT n m Δ γ (kOf N)))) < (kOf N : ℝ) := by
  obtain ⟨ε, hε0, hε1, hcε⟩ := exists_accuracy c hc0 hc
  set εr : ℝ := (ε : ℝ) with hεr
  have hεr0 : 0 < εr := by rw [hεr]; exact_mod_cast hε0
  have hεr1 : εr ≤ 1 / 100 := by
    rw [hεr]; have : ((ε : ℚ) : ℝ) ≤ ((1 / 100 : ℚ) : ℝ) := by exact_mod_cast hε1
    simpa using this
  set Icut : ℕ := max 1 (SharpOutputSize.iterationCutoff ε) with hIcut
  set Y1 : ℝ := ((3 * (p : ℝ) + 1 + 2) / εr + 1) ^ 2
  set Y2 : ℝ := ((3 * 2 + 1 + 2) / εr + 1) ^ 2
  set Y3 : ℝ := 2 * Real.logb 2 Icut + 1
  set Y : ℝ := max Y1 (max Y2 Y3)
  refine ⟨max (max 2 (Δ * SharpOutputSize.graphSizeCutoff Δ γ ε)) ⌈(2 : ℝ) ^ Y⌉₊, ?_⟩
  intro N hN n m _ edge hincident hdegree hNm hmn hsize
  have hN2 : 2 ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)
  have hNG : Δ * SharpOutputSize.graphSizeCutoff Δ γ ε ≤ N :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
  have hℓY : Y ≤ Real.logb 2 N := logb_ge_of_ge Y N (le_trans (le_max_right _ _) hN)
  have hY1 : Y1 ≤ Y := le_max_left _ _
  have hY2 : Y2 ≤ Y := le_trans (le_max_left _ _) (le_max_right _ _)
  have hY3 : Y3 ≤ Y := le_trans (le_max_right _ _) (le_max_right _ _)
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  -- graph-size cutoff
  have hnG : SharpOutputSize.graphSizeCutoff Δ γ ε ≤ n := by
    have h1 : Δ * SharpOutputSize.graphSizeCutoff Δ γ ε ≤ Δ * n := by
      have : 2 * N ≤ Δ * n := le_trans (by omega) hmn
      omega
    exact Nat.le_of_mul_le_mul_left h1 hΔ
  -- growth facts
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hℓ0 : 0 ≤ Real.logb 2 N := Real.logb_nonneg (by norm_num) (by exact_mod_cast (by omega : 1 ≤ N))
  have hY1' : Y1 ≤ Real.logb 2 N + 2 := by linarith
  have hY2' : Y2 ≤ Real.logb 2 N + 2 := by linarith
  have hL := L_le p N n εr hεr0 (by linarith) hN2 hn1 hsize hY1'
  obtain ⟨hk1, hklog⟩ := k_log_ge N εr hεr0 (by linarith) hN2 hY2'
  have hY2pos : (1 : ℝ) ≤ Y2 := by
    have : (1 : ℝ) ≤ (3 * 2 + 1 + 2) / εr + 1 := by
      have : (0 : ℝ) ≤ (3 * 2 + 1 + 2) / εr := by positivity
      linarith
    show (1 : ℝ) ≤ ((3 * 2 + 1 + 2) / εr + 1) ^ 2
    exact one_le_pow₀ this
  have hℓpos : 0 < Real.logb 2 N := by linarith
  -- iteration cutoff
  have hkI : SharpOutputSize.iterationCutoff ε ≤ kOf N := by
    have hIcR : (1 : ℝ) ≤ Icut := by exact_mod_cast (le_max_left 1 _)
    have hkpos : (0 : ℝ) < kOf N := by exact_mod_cast hk1
    have hlog : Real.logb 2 Icut ≤ Real.logb 2 (kOf N) := by
      have : Real.logb 2 Icut ≤ (1 - εr) * Real.logb 2 N := by
        have h3 : 2 * Real.logb 2 Icut + 1 ≤ Real.logb 2 N := by linarith
        nlinarith
      linarith
    have hle := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) (by linarith) hkpos).mp hlog
    have : Icut ≤ kOf N := by exact_mod_cast hle
    exact le_trans (le_max_right _ _) this
  -- sharp upper bound (banked)
  have hsharp := SharpOutputSize.at_graph_size_printed_entries_le_six_plus n m Δ (kOf N) γ ε
    edge hγ hΔ hε0 hincident hdegree hnG hkI
  have hsharpR : (Nat.clog 2 (printedT n m Δ γ (kOf N)) : ℝ) ≤
      (6 + εr) * (kOf N : ℝ) * (Nat.clog 2 n : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hsharp
    push_cast at h
    simpa [printedT, hεr] using h
  -- lower bound
  have hL1 : 1 ≤ Nat.clog 2 n ∨ Nat.clog 2 n = 0 := by omega
  have hT1 : 1 ≤ printedT n m Δ γ (kOf N) := by
    rcases hL1 with h | h
    · exact le_trans Nat.one_le_two_pow (two_pow_le_entries _ _ _ _ h)
    · -- `n = 1` is excluded by the size cutoff (the cutoff is at least 2 when positive)
      have : 2 ≤ n := by
        have hG : 2 ≤ SharpOutputSize.graphSizeCutoff Δ γ ε := by
          unfold SharpOutputSize.graphSizeCutoff
          have : 2 ≤ 2 ^ SharpOutputSize.lengthCutoff Δ γ ε := by
            have : 1 ≤ SharpOutputSize.lengthCutoff Δ γ ε := by
              unfold SharpOutputSize.lengthCutoff; omega
            calc 2 = 2 ^ 1 := by norm_num
              _ ≤ _ := Nat.pow_le_pow_right (by decide) this
          omega
        omega
      have := Nat.clog_pos (b := 2) (by decide) (by omega : 1 < n)
      omega
  have hLpos : 1 ≤ Nat.clog 2 n := by
    have hG : 2 ≤ SharpOutputSize.graphSizeCutoff Δ γ ε := by
      unfold SharpOutputSize.graphSizeCutoff
      have : 2 ≤ 2 ^ SharpOutputSize.lengthCutoff Δ γ ε := by
        have : 1 ≤ SharpOutputSize.lengthCutoff Δ γ ε := by
          unfold SharpOutputSize.lengthCutoff; omega
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ _ := Nat.pow_le_pow_right (by decide) this
      omega
    exact Nat.succ_le_of_lt (Nat.clog_pos (by decide) (by omega))
  have hlow := two_pow_le_entries (Nat.clog 2 n) (restorationDepth (Nat.clog 2 n))
    (coverDepth n m (Nat.clog 2 n) Δ γ) (kOf N) hLpos
  have hXk : (kOf N : ℝ) ≤ Real.logb 2 (printedT n m Δ γ (kOf N)) := by
    have hTR : (2 : ℝ) ^ (kOf N) ≤ (printedT n m Δ γ (kOf N) : ℝ) := by
      exact_mod_cast hlow
    have := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) (by positivity)
      (lt_of_lt_of_le (by positivity) hTR)).mpr hTR
    rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at this
  have hX := (logb_le_clog _ hT1).trans hsharpR
  exact core c εr _ _ _ _ hc0 hεr0 (by linarith) hcε hX hL hXk hklog hℓpos
    (by exact_mod_cast hk1)

/-! ## Square power-of-two output (`SquarePadding`, U17) -/

/-- The square padded printed-entry count (least power-of-two side above both dimensions). -/
def printedTsq (n m Δ : ℕ) (γ : ℚ) (k : ℕ) : ℕ :=
  SquarePadding.entries
    (sourceRows (Nat.clog 2 n) (restorationDepth (Nat.clog 2 n))
      (coverDepth n m (Nat.clog 2 n) Δ γ) k)
    (sourceCols (Nat.clog 2 n) (restorationDepth (Nat.clog 2 n))
      (coverDepth n m (Nat.clog 2 n) Δ γ) k)

/-- Square padding costs at most `3 + log₂ L` in `log₂` of the entry count, and keeps `2^k ≤ T`.
Reuses the banked `ReductionDimensions.square_entries_lt`. Does not close a ledger row. -/
theorem square_log_bounds (n m Δ : ℕ) (γ : ℚ) (k : ℕ) (hL : 1 ≤ Nat.clog 2 n) :
    Real.logb 2 (printedTsq n m Δ γ k) ≤
        Real.logb 2 (printedT n m Δ γ k) + 3 + Real.logb 2 (Nat.clog 2 n) ∧
      2 ^ k ≤ printedTsq n m Δ γ k := by
  set L := Nat.clog 2 n
  set r := restorationDepth L
  set q := coverDepth n m L Δ γ
  have hlt := ReductionDimensions.square_entries_lt
    (compressionEntropy (sourceRank L r q k) (sourceCost L r q k)) L hL
  have hlt' : printedTsq n m Δ γ k < 8 * L * printedT n m Δ γ k := by
    simpa [printedTsq, printedT, ReductionDimensions.entries, sourceRows, sourceCols] using hlt
  have hlow := two_pow_le_entries L r q k hL
  have hT1 : 1 ≤ printedT n m Δ γ k := le_trans Nat.one_le_two_pow hlow
  have hsq : 2 ^ k ≤ printedTsq n m Δ γ k := by
    have hcol := SquarePadding.cols_le_side (sourceRows L r q k) (sourceCols L r q k)
    have hside := SquarePadding.side_pos (sourceRows L r q k) (sourceCols L r q k)
    have hc : 2 ^ k ≤ sourceCols L r q k := by
      have hrow := compressionRowDraws_pos
        (compressionEntropy (sourceRank L r q k) (sourceCost L r q k)) L hL
      have := two_pow_le_entries L r q k hL
      -- `2^k ≤ cols` from the proof of `two_pow_le_entries`: re-derive via the column count
      have hH : k ≤ sourceCost L r q k - 1 := by
        unfold sourceCost
        have h1 : k ≤ k * (SourceProfileParameters.exponent L +
            SourceProfileParameters.outerExponent L + SourceProfileParameters.exponent L +
            r + q + 1) := Nat.le_mul_of_pos_right k (Nat.succ_pos _)
        omega
      have hpow : 2 ^ k ≤ 2 ^ (sourceCost L r q k - 1) := Nat.pow_le_pow_right (by decide) hH
      have hE : 2 ^ (sourceCost L r q k - 1) ≤
          compressionEntropy (sourceRank L r q k) (sourceCost L r q k) := by
        unfold compressionEntropy
        exact Nat.le_mul_of_pos_left _ (by omega)
      have hcol' : compressionEntropy (sourceRank L r q k) (sourceCost L r q k) ≤
          sourceCols L r q k := by
        unfold sourceCols compressionColumnDraws
        omega
      exact hpow.trans (hE.trans hcol')
    unfold printedTsq SquarePadding.entries
    calc 2 ^ k ≤ sourceCols L r q k := hc
      _ ≤ SquarePadding.side (sourceRows L r q k) (sourceCols L r q k) := hcol
      _ ≤ _ := Nat.le_mul_of_pos_left _ hside
  refine ⟨?_, hsq⟩
  have hTsqpos : (0 : ℝ) < printedTsq n m Δ γ k := by
    have : 0 < printedTsq n m Δ γ k := lt_of_lt_of_le Nat.one_le_two_pow hsq
    exact_mod_cast this
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hTR : (0 : ℝ) < printedT n m Δ γ k := by exact_mod_cast hT1
  have hle : (printedTsq n m Δ γ k : ℝ) ≤ 8 * L * printedT n m Δ γ k := by
    exact_mod_cast hlt'.le
  have := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) hTsqpos (by positivity)).mpr hle
  rw [Real.logb_mul (by positivity) hTR.ne', Real.logb_mul (by norm_num) hLR.ne'] at this
  have h8 : Real.logb 2 (8 : ℝ) = 3 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    norm_num
  linarith

/-- **T24 asymptotic core, square power-of-two output.** Same conclusion as
`gap_exceeds_twice_error` for the square padded entry count `printedTsq`. Does not close a
ledger row. -/
theorem gap_exceeds_twice_error_square (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ) (p : ℕ)
    (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (n m : ℕ) [NeZero n] (edge : Fin m → Bool → Fin n),
      (∀ v, ∃ e b, edge e b = v) → (∀ v, SourceItems.degree edge v ≤ Δ) →
      N ≤ m → 2 * m ≤ Δ * n → n ≤ N * (Nat.clog 2 (N + 2)) ^ p →
      2 * c * (Real.logb 2 (printedTsq n m Δ γ (kOf N)) /
        Real.logb 2 (Real.logb 2 (printedTsq n m Δ γ (kOf N)))) < (kOf N : ℝ) := by
  obtain ⟨ε, hε0, hε1, hcε⟩ := exists_accuracy c hc0 hc
  set εr : ℝ := (ε : ℝ) with hεr
  have hεr0 : 0 < εr := by rw [hεr]; exact_mod_cast hε0
  have hεr1 : εr ≤ 1 / 100 := by
    rw [hεr]; have : ((ε : ℚ) : ℝ) ≤ ((1 / 100 : ℚ) : ℝ) := by exact_mod_cast hε1
    simpa using this
  set ε₂ : ℚ := ε / 2 with hε₂
  have hε₂0 : 0 < ε₂ := by rw [hε₂]; positivity
  set Icut : ℕ := max 1 (max (SharpOutputSize.iterationCutoff ε₂) ⌈(8 : ℚ) / ε⌉₊) with hIcut
  set Y1 : ℝ := ((3 * (p : ℝ) + 1 + 2) / εr + 1) ^ 2
  set Y2 : ℝ := ((3 * 2 + 1 + 2) / εr + 1) ^ 2
  set Y3 : ℝ := 2 * Real.logb 2 Icut + 1
  set Y : ℝ := max Y1 (max Y2 Y3)
  refine ⟨max (max 2 (Δ * SharpOutputSize.graphSizeCutoff Δ γ ε₂)) ⌈(2 : ℝ) ^ Y⌉₊, ?_⟩
  intro N hN n m _ edge hincident hdegree hNm hmn hsize
  have hN2 : 2 ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)
  have hNG : Δ * SharpOutputSize.graphSizeCutoff Δ γ ε₂ ≤ N :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
  have hℓY : Y ≤ Real.logb 2 N := logb_ge_of_ge Y N (le_trans (le_max_right _ _) hN)
  have hY1 : Y1 ≤ Y := le_max_left _ _
  have hY2 : Y2 ≤ Y := le_trans (le_max_left _ _) (le_max_right _ _)
  have hY3 : Y3 ≤ Y := le_trans (le_max_right _ _) (le_max_right _ _)
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have hnG : SharpOutputSize.graphSizeCutoff Δ γ ε₂ ≤ n := by
    have h1 : Δ * SharpOutputSize.graphSizeCutoff Δ γ ε₂ ≤ Δ * n := by
      have : 2 * N ≤ Δ * n := le_trans (by omega) hmn
      omega
    exact Nat.le_of_mul_le_mul_left h1 hΔ
  have hℓ0 : 0 ≤ Real.logb 2 N :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast (by omega : 1 ≤ N))
  have hY1' : Y1 ≤ Real.logb 2 N + 2 := by linarith
  have hY2' : Y2 ≤ Real.logb 2 N + 2 := by linarith
  have hL := L_le p N n εr hεr0 (by linarith) hN2 hn1 hsize hY1'
  obtain ⟨hk1, hklog⟩ := k_log_ge N εr hεr0 (by linarith) hN2 hY2'
  have hY2pos : (1 : ℝ) ≤ Y2 := by
    have : (1 : ℝ) ≤ (3 * 2 + 1 + 2) / εr + 1 := by
      have : (0 : ℝ) ≤ (3 * 2 + 1 + 2) / εr := by positivity
      linarith
    show (1 : ℝ) ≤ ((3 * 2 + 1 + 2) / εr + 1) ^ 2
    exact one_le_pow₀ this
  have hℓpos : 0 < Real.logb 2 N := by linarith
  have hkIcut : Icut ≤ kOf N := by
    have hIcR : (1 : ℝ) ≤ Icut := by exact_mod_cast (le_max_left 1 _)
    have hkpos : (0 : ℝ) < kOf N := by exact_mod_cast hk1
    have hlog : Real.logb 2 Icut ≤ Real.logb 2 (kOf N) := by
      have : Real.logb 2 Icut ≤ (1 - εr) * Real.logb 2 N := by
        have h3 : 2 * Real.logb 2 Icut + 1 ≤ Real.logb 2 N := by linarith
        nlinarith
      linarith
    have hle := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) (by linarith) hkpos).mp hlog
    exact_mod_cast hle
  have hkI : SharpOutputSize.iterationCutoff ε₂ ≤ kOf N :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hkIcut
  have hk8 : 8 ≤ εr * (kOf N : ℝ) := by
    have h1 : ⌈(8 : ℚ) / ε⌉₊ ≤ kOf N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hkIcut
    have h2 : (8 : ℚ) / ε ≤ (kOf N : ℚ) := (Nat.le_ceil _).trans (by exact_mod_cast h1)
    have h3 : (8 : ℚ) ≤ ε * (kOf N : ℚ) := by
      have := (div_le_iff₀ hε0).mp h2; linarith
    have h4 : ((8 : ℚ) : ℝ) ≤ ((ε * (kOf N : ℚ) : ℚ) : ℝ) := by exact_mod_cast h3
    push_cast at h4
    simpa [hεr] using h4
  have hsharp := SharpOutputSize.at_graph_size_printed_entries_le_six_plus n m Δ (kOf N) γ ε₂
    edge hγ hΔ hε₂0 hincident hdegree hnG hkI
  have hsharpR : (Nat.clog 2 (printedT n m Δ γ (kOf N)) : ℝ) ≤
      (6 + εr / 2) * (kOf N : ℝ) * (Nat.clog 2 n : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hsharp
    push_cast at h
    simpa [printedT, hεr, hε₂] using h
  have hLpos : 1 ≤ Nat.clog 2 n := by
    have hG : 2 ≤ SharpOutputSize.graphSizeCutoff Δ γ ε₂ := by
      unfold SharpOutputSize.graphSizeCutoff
      have : 2 ≤ 2 ^ SharpOutputSize.lengthCutoff Δ γ ε₂ := by
        have : 1 ≤ SharpOutputSize.lengthCutoff Δ γ ε₂ := by
          unfold SharpOutputSize.lengthCutoff; omega
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ _ := Nat.pow_le_pow_right (by decide) this
      omega
    exact Nat.succ_le_of_lt (Nat.clog_pos (by decide) (by omega))
  obtain ⟨hsqlog, hsqlow⟩ := square_log_bounds n m Δ γ (kOf N) hLpos
  have hT1 : 1 ≤ printedT n m Δ γ (kOf N) :=
    le_trans Nat.one_le_two_pow (two_pow_le_entries _ _ _ _ hLpos)
  have hXrect := (logb_le_clog _ hT1).trans hsharpR
  have hLR : (1 : ℝ) ≤ Nat.clog 2 n := by exact_mod_cast hLpos
  have hlogL : Real.logb 2 (Nat.clog 2 n : ℝ) ≤ (Nat.clog 2 n : ℝ) := by
    have h := clog_le_logb_add_one (Nat.clog 2 n) hLpos
    have hlt : Real.logb 2 (Nat.clog 2 n : ℝ) < (Nat.clog 2 n : ℝ) := by
      have hx : (0 : ℝ) < Nat.clog 2 n := by linarith
      have h2 : (Nat.clog 2 n : ℝ) < (2 : ℝ) ^ (Nat.clog 2 n) := by
        exact_mod_cast Nat.lt_two_pow_self
      have := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) hx h2
      rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at this
    exact hlt.le
  have hX : Real.logb 2 (printedTsq n m Δ γ (kOf N)) ≤
      (6 + εr) * (kOf N : ℝ) * (Nat.clog 2 n : ℝ) := by
    have hextra : 3 + Real.logb 2 (Nat.clog 2 n : ℝ) ≤
        (εr / 2) * (kOf N : ℝ) * (Nat.clog 2 n : ℝ) := by
      have h8L := mul_le_mul_of_nonneg_right hk8 (by linarith : (0 : ℝ) ≤ Nat.clog 2 n)
      have e1 : εr * (kOf N : ℝ) * (Nat.clog 2 n : ℝ) =
          2 * ((εr / 2) * (kOf N : ℝ) * (Nat.clog 2 n : ℝ)) := by ring
      linarith
    have e : (6 + εr / 2) * (kOf N : ℝ) * (Nat.clog 2 n : ℝ) +
        (εr / 2) * (kOf N : ℝ) * (Nat.clog 2 n : ℝ) =
        (6 + εr) * (kOf N : ℝ) * (Nat.clog 2 n : ℝ) := by ring
    linarith
  have hXk : (kOf N : ℝ) ≤ Real.logb 2 (printedTsq n m Δ γ (kOf N)) := by
    have hTR : (2 : ℝ) ^ (kOf N) ≤ (printedTsq n m Δ γ (kOf N) : ℝ) := by
      exact_mod_cast hsqlow
    have := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) (by positivity)
      (lt_of_lt_of_le (by positivity) hTR)).mpr hTR
    rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at this
  exact core c εr _ _ _ _ hc0 hεr0 (by linarith) hcε hX hL hXk hklog hℓpos
    (by exact_mod_cast hk1)

end Paper2.Unit4Shell.Asymptotics
