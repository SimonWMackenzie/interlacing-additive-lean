import Paper2.A4Asymptotics

/-!
# Unit 4 (Paper A), segment A4-S7/S10 support: `n^{O(k+1)} = 2^{o(N)}` for `k = ⌊N/⌈log₂N⌉²⌋`

Owner lane `owner:a-unit4-shell` (private, 25 September 2026).
Source: lock v12 `06-reduction.tex`, proof of `thm:quantitative`: "Both the construction and any
fixed polynomial-time estimator take `n^{O(k+1)}=2^{O(N/\log N)}=2^{o(N)}`". The exponent `E₀`
must be ABSOLUTE (independent of `k`), as in H-A3 (06-reduction.tex:30-31).

Pure analysis with explicit thresholds. **Does not close a ledger row.**
-/

namespace Paper2.Unit4Shell.T24Runtime

open Paper2.Unit4Shell.Asymptotics

/-- For every absolute exponent `E₀`, polylog exponent `p` and `ε > 0`, beyond an explicit `N₀`,
every `1 ≤ n ≤ N·⌈log₂(N+2)⌉^p` satisfies `(n+2)^(E₀·(k+1)) ≤ 2^(εN)` with `k = ⌊N/⌈log₂N⌉²⌋`.
Does not close a ledger row. -/
theorem subexponential (E₀ p : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ n : ℕ, 1 ≤ n → n ≤ N * (Nat.clog 2 (N + 2)) ^ p →
      ((n + 2 : ℕ) : ℝ) ^ (E₀ * (kOf N + 1)) ≤ (2 : ℝ) ^ (ε * N) := by
  set δ : ℝ := min 1 (ε / (8 * (E₀ + 1))) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ ≤ ε / (8 * (E₀ + 1)) := min_le_right _ _
  set Y1 : ℝ := ((3 * (p : ℝ) + 0 + 2) / 1 + 1) ^ 2 with hY1d
  set Y2 : ℝ := 16 * (E₀ + 1) / ε + 2 with hY2d
  set Y : ℝ := max Y1 Y2
  set Z : ℝ := ((3 * (2 * 2) + 2 + 2) / δ + 1) ^ 2 with hZd
  refine ⟨max (max 2 ⌈Z⌉₊) ⌈(2 : ℝ) ^ Y⌉₊, ?_⟩
  intro N hN n hn hsize
  have hN2 : 2 ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)
  have hNZ : Z ≤ (N : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN))
  have hℓY : Y ≤ Real.logb 2 N := logb_ge_of_ge Y N (le_trans (le_max_right _ _) hN)
  set ℓ := Real.logb 2 N with hℓ
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hY1 : Y1 ≤ ℓ := le_trans (le_max_left _ _) hℓY
  have hY2 : Y2 ≤ ℓ := le_trans (le_max_right _ _) hℓY
  have hY2two : (2 : ℝ) ≤ Y2 := by
    have : 0 ≤ 16 * ((E₀ : ℝ) + 1) / ε := by positivity
    show (2 : ℝ) ≤ 16 * ((E₀ : ℝ) + 1) / ε + 2
    linarith
  have hℓ2 : 2 ≤ ℓ := le_trans hY2two hY2
  -- `log₂(n+2) ≤ 2ℓ + 2`
  have hlogn : Real.logb 2 ((n + 2 : ℕ) : ℝ) ≤ 2 * ℓ + 2 := by
    have hY1' : ((3 * (p : ℝ) + 0 + 2) / 1 + 1) ^ 2 ≤ ℓ + 2 := by
      have h0 : Y1 ≤ ℓ := hY1
      rw [hY1d] at h0
      linarith
    have hsmall := small_log (p : ℝ) 0 1 ℓ (by positivity) le_rfl one_pos le_rfl (by linarith)
      hY1'
    have hC : (Nat.clog 2 (N + 2) : ℝ) ≤ ℓ + 2 := by
      have h1 := clog_le_logb_add_one (N + 2) (by omega)
      have h2 : Real.logb 2 ((N + 2 : ℕ) : ℝ) ≤ ℓ + 1 := by
        have hle : ((N + 2 : ℕ) : ℝ) ≤ 2 * N := by
          push_cast; exact_mod_cast (by omega : N + 2 ≤ 2 * N)
        have := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) (by positivity)
          (by positivity)).mpr hle
        rw [Real.logb_mul (by norm_num) hNpos.ne', Real.logb_self_eq_one (by norm_num)] at this
        linarith
      linarith
    have hC1 : (1 : ℝ) ≤ Nat.clog 2 (N + 2) := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.clog_pos (by decide) (by omega))
    have hlogC : Real.logb 2 (Nat.clog 2 (N + 2) : ℝ) ≤ Real.logb 2 (ℓ + 2) :=
      (Real.logb_le_logb (by norm_num) (by linarith) (by linarith)).mpr hC
    have hn2 : ((n + 2 : ℕ) : ℝ) ≤ 4 * (N * (Nat.clog 2 (N + 2) : ℝ) ^ p) := by
      have h0 : (n : ℝ) ≤ N * (Nat.clog 2 (N + 2) : ℝ) ^ p := by exact_mod_cast hsize
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      push_cast; linarith
    have hpos : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
    have hmono := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) hpos (by positivity)).mpr hn2
    rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_mul hNpos.ne' (by positivity),
      Real.logb_pow] at hmono
    have h4 : Real.logb 2 (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow,
        Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]; norm_num
    have hp0 : (0 : ℝ) ≤ p := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hlogC hp0]
  -- `k + 1 ≤ N/ℓ² + 1`
  have hk : ((kOf N : ℕ) : ℝ) + 1 ≤ (N : ℝ) / ℓ ^ 2 + 1 := by
    have hCge : ℓ ≤ (Nat.clog 2 N : ℝ) := by
      have h0 := Nat.le_pow_clog (by decide : 1 < 2) N
      have hR : (N : ℝ) ≤ (2 : ℝ) ^ (Nat.clog 2 N) := by exact_mod_cast h0
      have h1 := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) hNpos (by positivity)).mpr hR
      rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at h1
    have hdiv : ((kOf N : ℕ) : ℝ) ≤ (N : ℝ) / (Nat.clog 2 N : ℝ) ^ 2 := by
      unfold kOf
      have := Nat.cast_div_le (α := ℝ) (m := N) (n := (Nat.clog 2 N) ^ 2)
      simpa using this
    have hsq : ℓ ^ 2 ≤ (Nat.clog 2 N : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith) hCge 2
    have h2 : (N : ℝ) / (Nat.clog 2 N : ℝ) ^ 2 ≤ (N : ℝ) / ℓ ^ 2 :=
      div_le_div_of_nonneg_left hNpos.le (by positivity) hsq
    linarith
  -- main estimate on the exponent of 2
  have hZ := small_log (2 * 2) 2 δ (N : ℝ) (by norm_num) (by norm_num) hδ0 hδ1 hNpos.le
    (by have h0 : Z ≤ (N : ℝ) := hNZ
        rw [hZd] at h0
        linarith)
  have hlogN : ℓ ≤ Real.logb 2 ((N : ℝ) + 2) :=
    (Real.logb_le_logb (by norm_num) hNpos (by linarith)).mpr (by linarith)
  have hℓpos : 0 < ℓ := by linarith
  have hl0 : 0 ≤ Real.logb 2 ((n + 2 : ℕ) : ℝ) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast (by omega : 1 ≤ n + 2))
  have h1 : ((kOf N : ℝ) + 1) * Real.logb 2 ((n + 2 : ℕ) : ℝ) ≤
      ((N : ℝ) / ℓ ^ 2 + 1) * (2 * ℓ + 2) := by
    calc ((kOf N : ℝ) + 1) * Real.logb 2 ((n + 2 : ℕ) : ℝ)
        ≤ ((N : ℝ) / ℓ ^ 2 + 1) * Real.logb 2 ((n + 2 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right hk hl0
      _ ≤ ((N : ℝ) / ℓ ^ 2 + 1) * (2 * ℓ + 2) :=
          mul_le_mul_of_nonneg_left hlogn (by positivity)
  have h2 : ((N : ℝ) / ℓ ^ 2 + 1) * (2 * ℓ + 2) ≤ 4 * (N : ℝ) / ℓ + (2 * ℓ + 2) := by
    rw [add_mul, one_mul]
    have h3 : (N : ℝ) / ℓ ^ 2 * (2 * ℓ + 2) ≤ 4 * (N : ℝ) / ℓ := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hℓpos]
      have hh := mul_le_mul_of_nonneg_left (show 2 * ℓ + 2 ≤ 4 * ℓ by linarith)
        (mul_nonneg hNpos.le hℓpos.le)
      have e1 : (N : ℝ) * (2 * ℓ + 2) * ℓ = (N : ℝ) * ℓ * (2 * ℓ + 2) := by ring
      have e2 : 4 * (N : ℝ) * ℓ ^ 2 = (N : ℝ) * ℓ * (4 * ℓ) := by ring
      rw [e1, e2]; exact hh
    linarith
  have h3 : 4 * (N : ℝ) / ℓ ≤ ε * N / (4 * (E₀ + 1)) := by
    rw [div_le_div_iff₀ hℓpos (by positivity)]
    have h16 : 16 * ((E₀ : ℝ) + 1) / ε ≤ ℓ := by
      have h0 : Y2 ≤ ℓ := hY2
      rw [hY2d] at h0
      linarith
    have h' := (div_le_iff₀ hε).mp h16
    nlinarith
  have h4 : 2 * ℓ + 2 ≤ ε * N / (4 * (E₀ + 1)) := by
    have hδN : δ * N ≤ ε / (8 * (E₀ + 1)) * N := mul_le_mul_of_nonneg_right hδε hNpos.le
    have h5 : ε / (8 * (E₀ + 1)) * N ≤ ε * N / (4 * (E₀ + 1)) := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos hε hNpos]
    linarith
  have hsum : ((kOf N : ℝ) + 1) * Real.logb 2 ((n + 2 : ℕ) : ℝ) ≤
      ε * N / (2 * (E₀ + 1)) := by
    have e : ε * N / (4 * (E₀ + 1)) + ε * N / (4 * (E₀ + 1)) = ε * N / (2 * (E₀ + 1)) := by
      field_simp; ring
    linarith
  have hE : (E₀ : ℝ) * (ε * N / (2 * (E₀ + 1))) ≤ ε * N := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    have hE0 : (0 : ℝ) ≤ E₀ := by positivity
    have hq := mul_le_mul_of_nonneg_right (show (E₀ : ℝ) ≤ 2 * (E₀ + 1) by linarith)
      (le_of_lt (mul_pos hε hNpos))
    have e3 : ε * (N : ℝ) * (2 * ((E₀ : ℝ) + 1)) = 2 * ((E₀ : ℝ) + 1) * (ε * N) := by ring
    rw [e3]; exact hq
  have hexp : ((E₀ * (kOf N + 1) : ℕ) : ℝ) * Real.logb 2 ((n + 2 : ℕ) : ℝ) ≤ ε * N := by
    have hc : ((E₀ * (kOf N + 1) : ℕ) : ℝ) = (E₀ : ℝ) * ((kOf N : ℝ) + 1) := by push_cast; ring
    rw [hc]
    calc ((E₀ : ℝ) * ((kOf N : ℝ) + 1)) * Real.logb 2 ((n + 2 : ℕ) : ℝ)
        = (E₀ : ℝ) * (((kOf N : ℝ) + 1) * Real.logb 2 ((n + 2 : ℕ) : ℝ)) := by ring
      _ ≤ (E₀ : ℝ) * (ε * N / (2 * (E₀ + 1))) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ ε * N := hE
  have hpos : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
  have hL : Real.logb 2 (((n + 2 : ℕ) : ℝ) ^ (E₀ * (kOf N + 1))) ≤ ε * N := by
    rw [Real.logb_pow]; exact hexp
  exact (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) (by positivity)).mp hL

end Paper2.Unit4Shell.T24Runtime
