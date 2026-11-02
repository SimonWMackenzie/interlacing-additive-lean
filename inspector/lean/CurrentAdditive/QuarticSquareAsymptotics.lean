import CurrentAdditive.QuarticSquareLog

namespace CurrentAdditive.QuarticAsymptotics

open Paper2 Paper2.Unit4Shell.Asymptotics Paper2.SourceRecursiveNoSampling
  Paper2.SourceProfileParameters CurrentAdditive.RandomizedSchedule

set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

theorem gap_exceeds_twice_error_square27 (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ) (p : ℕ)
    (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (n m : ℕ) [NeZero n] (edge : Fin m → Bool → Fin n),
      (∀ v, ∃ e b, edge e b = v) → (∀ v, SourceItems.degree edge v ≤ Δ) →
      N ≤ m → 2 * m ≤ Δ * n → n ≤ N * (Nat.clog 2 (N + 2)) ^ p →
      2 * c * (Real.logb 2 (printedTsq27 n m Δ γ (kOf N)) /
        Real.logb 2 (Real.logb 2 (printedTsq27 n m Δ γ (kOf N)))) < (kOf N : ℝ) := by
  obtain ⟨ε, hε0, hε1, hcε⟩ := exists_accuracy c hc0 hc
  set εr : ℝ := (ε : ℝ) with hεr
  have hεr0 : 0 < εr := by rw [hεr]; exact_mod_cast hε0
  have hεr1 : εr ≤ 1 / 100 := by
    rw [hεr]; have : ((ε : ℚ) : ℝ) ≤ ((1 / 100 : ℚ) : ℝ) := by exact_mod_cast hε1
    simpa using this
  set ε₂ : ℚ := ε / 2 with hε₂
  have hε₂0 : 0 < ε₂ := by rw [hε₂]; positivity
  set Icut : ℕ := max 1 (max (QuarticSharpOutputSize.iterationCutoff27 ε₂) ⌈(8 : ℚ) / ε⌉₊) with hIcut
  set Y1 : ℝ := ((3 * (p : ℝ) + 1 + 2) / εr + 1) ^ 2
  set Y2 : ℝ := ((3 * 2 + 1 + 2) / εr + 1) ^ 2
  set Y3 : ℝ := 2 * Real.logb 2 Icut + 1
  set Y : ℝ := max Y1 (max Y2 Y3)
  refine ⟨max (max 2 (Δ * QuarticSharpOutputSize.graphSizeCutoff27 Δ γ ε₂)) ⌈(2 : ℝ) ^ Y⌉₊, ?_⟩
  intro N hN n m _ edge hincident hdegree hNm hmn hsize
  have hN2 : 2 ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)
  have hNG : Δ * QuarticSharpOutputSize.graphSizeCutoff27 Δ γ ε₂ ≤ N :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
  have hℓY : Y ≤ Real.logb 2 N := logb_ge_of_ge Y N (le_trans (le_max_right _ _) hN)
  have hY1 : Y1 ≤ Y := le_max_left _ _
  have hY2 : Y2 ≤ Y := le_trans (le_max_left _ _) (le_max_right _ _)
  have hY3 : Y3 ≤ Y := le_trans (le_max_right _ _) (le_max_right _ _)
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have hnG : QuarticSharpOutputSize.graphSizeCutoff27 Δ γ ε₂ ≤ n := by
    have h1 : Δ * QuarticSharpOutputSize.graphSizeCutoff27 Δ γ ε₂ ≤ Δ * n := by
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
  have hkI : QuarticSharpOutputSize.iterationCutoff27 ε₂ ≤ kOf N :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hkIcut
  have hk8 : 8 ≤ εr * (kOf N : ℝ) := by
    have h1 : ⌈(8 : ℚ) / ε⌉₊ ≤ kOf N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hkIcut
    have h2 : (8 : ℚ) / ε ≤ (kOf N : ℚ) := (Nat.le_ceil _).trans (by exact_mod_cast h1)
    have h3 : (8 : ℚ) ≤ ε * (kOf N : ℚ) := by
      have := (div_le_iff₀ hε0).mp h2; linarith
    have h4 : ((8 : ℚ) : ℝ) ≤ ((ε * (kOf N : ℚ) : ℚ) : ℝ) := by exact_mod_cast h3
    push_cast at h4
    simpa [hεr] using h4
  have hsharp := QuarticSharpOutputSize.at_graph_size_printed_entries_le_six_plus27 n m Δ (kOf N) γ ε₂
    edge hγ hΔ hε₂0 hincident hdegree hnG hkI
  have hsharpR : (Nat.clog 2 (printedT27 n m Δ γ (kOf N)) : ℝ) ≤
      (6 + εr / 2) * (kOf N : ℝ) * (Nat.clog 2 n : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hsharp
    push_cast at h
    simpa [printedT27, hεr, hε₂] using h
  have hLpos : 1 ≤ Nat.clog 2 n := by
    have hG : 2 ≤ QuarticSharpOutputSize.graphSizeCutoff27 Δ γ ε₂ := by
      have hlen : 1 ≤ QuarticSharpOutputSize.lengthCutoff27 Δ γ ε₂ := by
        unfold QuarticSharpOutputSize.lengthCutoff27
        omega
      have hpow : 2 ≤ 2 ^ QuarticSharpOutputSize.lengthCutoff27 Δ γ ε₂ := by
        calc
          2 = 2 ^ 1 := by norm_num
          _ ≤ _ := Nat.pow_le_pow_right (by decide) hlen
      exact hpow.trans (le_max_right _ _)
    exact Nat.succ_le_of_lt (Nat.clog_pos (by decide) (by omega))
  obtain ⟨hsqlog, hsqlow⟩ := square_log_bounds27 n m Δ γ (kOf N) hLpos
  have hT1 : 1 ≤ printedT27 n m Δ γ (kOf N) :=
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
  have hX : Real.logb 2 (printedTsq27 n m Δ γ (kOf N)) ≤
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
  have hXk : (kOf N : ℝ) ≤ Real.logb 2 (printedTsq27 n m Δ γ (kOf N)) := by
    have hTR : (2 : ℝ) ^ (kOf N) ≤ (printedTsq27 n m Δ γ (kOf N) : ℝ) := by
      exact_mod_cast hsqlow
    have := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) (by positivity)
      (lt_of_lt_of_le (by positivity) hTR)).mpr hTR
    rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at this
  exact core c εr _ _ _ _ hc0 hεr0 (by linarith) hcε hX hL hXk hklog hℓpos
    (by exact_mod_cast hk1)

#print axioms gap_exceeds_twice_error_square27

end CurrentAdditive.QuarticAsymptotics
