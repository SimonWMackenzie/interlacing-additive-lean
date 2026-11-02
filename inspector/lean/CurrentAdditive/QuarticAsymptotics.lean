import CurrentAdditive.QuarticSharpOutputSize
import Paper2.A4Asymptotics

namespace CurrentAdditive.QuarticAsymptotics

open Paper2 Paper2.Unit4Shell.Asymptotics
  Paper2.SourceRecursiveNoSampling Paper2.SourceProfileParameters
  CurrentAdditive.RandomizedSchedule

/-- Actual quartic source-rectangle entry count at L = ceil(log2 n). -/
def printedT27 (n m Δ : ℕ) (γ : ℚ) (k : ℕ) : ℕ :=
  sourceRows (Nat.clog 2 n)
    (4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 n))
    (q27 (V := Fin n) (E := Fin m) (Nat.clog 2 n) γ Δ) k *
  sourceCols (Nat.clog 2 n)
    (4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 n))
    (q27 (V := Fin n) (E := Fin m) (Nat.clog 2 n) γ Δ) k

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
/-- At the actual quartic printed entry count, the growing gap defeats
twice every accuracy constant below 1/12. -/
theorem gap_exceeds_twice_error27 (Δ : ℕ) (γ : ℚ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (p : ℕ)
    (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (n m : ℕ) [NeZero n] (edge : Fin m → Bool → Fin n),
      (∀ v, ∃ e b, edge e b = v) →
      (∀ v, SourceItems.degree edge v ≤ Δ) →
      N ≤ m → 2 * m ≤ Δ * n →
      n ≤ N * (Nat.clog 2 (N + 2)) ^ p →
      2 * c * (Real.logb 2 (printedT27 n m Δ γ (kOf N)) /
        Real.logb 2 (Real.logb 2 (printedT27 n m Δ γ (kOf N)))) <
        (kOf N : ℝ) := by
  obtain ⟨ε, hε0, hε1, hcε⟩ := exists_accuracy c hc0 hc
  set εr : ℝ := (ε : ℝ) with hεr
  have hεr0 : 0 < εr := by rw [hεr]; exact_mod_cast hε0
  have hεr1 : εr ≤ 1 / 100 := by
    rw [hεr]
    have : ((ε : ℚ) : ℝ) ≤ ((1 / 100 : ℚ) : ℝ) := by exact_mod_cast hε1
    simpa using this
  set Icut : ℕ := max 1 (QuarticSharpOutputSize.iterationCutoff27 ε) with hIcut
  set Y1 : ℝ := ((3 * (p : ℝ) + 1 + 2) / εr + 1) ^ 2
  set Y2 : ℝ := ((3 * 2 + 1 + 2) / εr + 1) ^ 2
  set Y3 : ℝ := 2 * Real.logb 2 Icut + 1
  set Y : ℝ := max Y1 (max Y2 Y3)
  refine ⟨max (max 2 (Δ * QuarticSharpOutputSize.graphSizeCutoff27 Δ γ ε))
    ⌈(2 : ℝ) ^ Y⌉₊, ?_⟩
  intro N hN n m _ edge hincident hdegree hNm hmn hsize
  have hN2 : 2 ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)
  have hNG : Δ * QuarticSharpOutputSize.graphSizeCutoff27 Δ γ ε ≤ N :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
  have hℓY : Y ≤ Real.logb 2 N := logb_ge_of_ge Y N
    (le_trans (le_max_right _ _) hN)
  have hY1 : Y1 ≤ Y := le_max_left _ _
  have hY2 : Y2 ≤ Y := le_trans (le_max_left _ _) (le_max_right _ _)
  have hY3 : Y3 ≤ Y := le_trans (le_max_right _ _) (le_max_right _ _)
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have hnG : QuarticSharpOutputSize.graphSizeCutoff27 Δ γ ε ≤ n := by
    have h1 : Δ * QuarticSharpOutputSize.graphSizeCutoff27 Δ γ ε ≤ Δ * n := by
      have : 2 * N ≤ Δ * n := le_trans (by omega) hmn
      omega
    exact Nat.le_of_mul_le_mul_left h1 hΔ
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
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
  have hkI : QuarticSharpOutputSize.iterationCutoff27 ε ≤ kOf N := by
    have hIcR : (1 : ℝ) ≤ Icut := by exact_mod_cast (le_max_left 1 _)
    have hkpos : (0 : ℝ) < kOf N := by exact_mod_cast hk1
    have hlog : Real.logb 2 Icut ≤ Real.logb 2 (kOf N) := by
      have : Real.logb 2 Icut ≤ (1 - εr) * Real.logb 2 N := by
        have h3 : 2 * Real.logb 2 Icut + 1 ≤ Real.logb 2 N := by linarith
        nlinarith
      linarith
    have hle := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2)
      (by linarith) hkpos).mp hlog
    have : Icut ≤ kOf N := by exact_mod_cast hle
    exact le_trans (le_max_right _ _) this
  have hsharp := QuarticSharpOutputSize.at_graph_size_printed_entries_le_six_plus27
    n m Δ (kOf N) γ ε edge hγ hΔ hε0 hincident hdegree hnG hkI
  have hsharpR : (Nat.clog 2 (printedT27 n m Δ γ (kOf N)) : ℝ) ≤
      (6 + εr) * (kOf N : ℝ) * (Nat.clog 2 n : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hsharp
    push_cast at h
    simpa [printedT27, hεr] using h
  have hG : 2 ≤ QuarticSharpOutputSize.graphSizeCutoff27 Δ γ ε := by
    have hlen : 1 ≤ QuarticSharpOutputSize.lengthCutoff27 Δ γ ε := by
      unfold QuarticSharpOutputSize.lengthCutoff27
      omega
    have hpow : 2 ≤ 2 ^ QuarticSharpOutputSize.lengthCutoff27 Δ γ ε := by
      calc
        2 = 2 ^ 1 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by decide) hlen
    exact hpow.trans (le_max_right _ _)
  have hLpos : 1 ≤ Nat.clog 2 n :=
    Nat.succ_le_of_lt (Nat.clog_pos (by decide) (by omega))
  have hlow := two_pow_le_entries (Nat.clog 2 n)
    (4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 n))
    (q27 (V := Fin n) (E := Fin m) (Nat.clog 2 n) γ Δ)
    (kOf N) hLpos
  have hT1 : 1 ≤ printedT27 n m Δ γ (kOf N) := by
    exact le_trans Nat.one_le_two_pow hlow
  have hXk : (kOf N : ℝ) ≤ Real.logb 2 (printedT27 n m Δ γ (kOf N)) := by
    have hTR : (2 : ℝ) ^ (kOf N) ≤
        (printedT27 n m Δ γ (kOf N) : ℝ) := by
      exact_mod_cast hlow
    have := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2)
      (by positivity) (lt_of_lt_of_le (by positivity) hTR)).mpr hTR
    rwa [Real.logb_pow, Real.logb_self_eq_one
      (by norm_num : (1 : ℝ) < 2), mul_one] at this
  have hX := (logb_le_clog _ hT1).trans hsharpR
  exact core c εr _ _ _ _ hc0 hεr0 (by linarith) hcε
    hX hL hXk hklog hℓpos (by exact_mod_cast hk1)

#print axioms gap_exceeds_twice_error27

end CurrentAdditive.QuarticAsymptotics
