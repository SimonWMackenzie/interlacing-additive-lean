import CurrentAdditive.V39ETHAsymptotics
import CurrentAdditive.V42PublicSize

/-! Exact c<1/8 quantitative arithmetic for the literal v42 sample recipe.
The sparse-source graph size bounds remain source assumptions; this module
constructs no source graph and claims no machine execution. -/
namespace CurrentAdditive.V42ETHArithmetic
noncomputable section
open Paper2.Unit4Shell.Asymptotics
open V39ETHArithmetic
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
theorem iterations_eventually_ge (K : ℕ) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → K ≤ kOf N := by
  let I : ℕ := max 1 K
  let Y : ℝ := max 361 (2 * Real.logb 2 I + 1)
  refine ⟨max 2 ⌈(2 : ℝ)^Y⌉₊, ?_⟩
  intro N hN
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hY : Y ≤ Real.logb 2 N := logb_ge_of_ge Y N ((le_max_right _ _).trans hN)
  have hlarge : (361 : ℝ) ≤ Real.logb 2 N + 2 := by
    have := le_max_left (361 : ℝ) (2 * Real.logb 2 I + 1)
    linarith
  obtain ⟨hk1, hklog⟩ := k_log_ge N (1/2 : ℝ) (by norm_num)
    (by norm_num) hN2 (by norm_num; exact hlarge)
  have hI : 1 ≤ I := le_max_left _ _
  have hIk : Real.logb 2 I ≤ Real.logb 2 (kOf N) := by
    have := le_max_right (361 : ℝ) (2 * Real.logb 2 I + 1)
    linarith
  have hIpos : (0 : ℝ) < I := by exact_mod_cast hI
  have hkpos : (0 : ℝ) < kOf N := by exact_mod_cast hk1
  have hnat : I ≤ kOf N := by
    exact_mod_cast (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) hIpos hkpos).1 hIk
  exact (le_max_right 1 K).trans hnat

/-- The literal sample eventually meets any entry-count threshold, uniformly
over all choices of the logarithmic graph-size parameter. -/
theorem entries_eventually_ge (T₀ : ℕ) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ L,
      T₀ ≤ V42PublicSchedule.sampleEntries L (kOf N) := by
  obtain ⟨N₀, hN₀⟩ := iterations_eventually_ge T₀
  refine ⟨N₀, ?_⟩
  intro N hN L
  calc
    T₀ ≤ 2 ^ T₀ := Nat.le_of_lt Nat.lt_two_pow_self
    _ ≤ 2 ^ kOf N := Nat.pow_le_pow_right (by decide) (hN₀ N hN)
    _ ≤ V42PublicSchedule.sampleEntries L (kOf N) := V42PublicSchedule.sampleEntries_lower L _

/-- Exact `c<1/8` gap separation at the actual power-of-two square sample.
The two graph-size premises are the lower and upper sparse-source accounting;
the logarithmic overhead and sample-size conclusions are proved here.
-/
theorem gap_exceeds_twice_error (Δ p : ℕ) (hΔ : 0 < Δ)
    (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1/8) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ n,
      1 ≤ n → N ≤ Δ*n → n ≤ N*(Nat.clog 2 (N+2))^p →
      2*c*(Real.logb 2 (V42PublicSchedule.sampleEntries (Nat.clog 2 n) (kOf N)) /
        Real.logb 2 (Real.logb 2 (V42PublicSchedule.sampleEntries (Nat.clog 2 n) (kOf N))))
        < (kOf N : ℝ) := by
  obtain ⟨εq, hεq, hεq1, hcε⟩ := exists_accuracy c hc0 hc
  let ε : ℝ := εq
  have hε : 0 < ε := by dsimp [ε]; exact_mod_cast hεq
  have hε1 : ε ≤ 1/100 := by
    have hr : ((εq : ℚ) : ℝ) ≤ ((1/100 : ℚ) : ℝ) := by exact_mod_cast hεq1
    norm_num at hr
    exact hr
  obtain ⟨Nk, hNk⟩ := iterations_eventually_ge (V42PublicSize.iterationCutoff ε)
  let Y1 : ℝ := ((3*(p : ℝ)+1+2)/ε+1)^2
  let Y2 : ℝ := ((3*2+1+2)/ε+1)^2
  let Y : ℝ := max Y1 Y2
  refine ⟨max Nk (max (Δ*2^(V42PublicSize.lengthCutoff ε)) (max 4 ⌈(2 : ℝ)^Y⌉₊)), ?_⟩
  intro N hN n hn hlow hsize
  have hN4 : 4 ≤ N := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hNY : ⌈(2 : ℝ)^Y⌉₊ ≤ N := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hY : Y ≤ Real.logb 2 N := logb_ge_of_ge Y N hNY
  have hY1 : Y1 ≤ Real.logb 2 N := (le_max_left _ _).trans hY
  have hY2 : Y2 ≤ Real.logb 2 N := (le_max_right _ _).trans hY
  have hkcut := hNk N ((le_max_left _ _).trans hN)
  have hcutn : 2^(V42PublicSize.lengthCutoff ε) ≤ n := by
    have hcut : Δ*2^(V42PublicSize.lengthCutoff ε) ≤ N := (le_max_left _ _).trans
      ((le_max_right _ _).trans hN)
    exact Nat.le_of_mul_le_mul_left (hcut.trans hlow) hΔ
  have hLcut : V42PublicSize.lengthCutoff ε ≤ Nat.clog 2 n := by
    have hm := Nat.clog_mono_right 2 hcutn
    simpa only [Nat.clog_pow 2 _ (by decide)] using hm
  have hL := L_le p N n ε hε (by linarith) (by omega) hn hsize (by dsimp [Y1] at hY1; linarith)
  obtain ⟨hk1, hklog⟩ := k_log_ge N ε hε (by linarith) (by omega)
    (by dsimp [Y2] at hY2; linarith)
  have hsharp := V42PublicSize.sample_sharp ε hε (by linarith) (Nat.clog 2 n) (kOf N) hLcut hkcut
  let T := V42PublicSchedule.sampleEntries (Nat.clog 2 n) (kOf N)
  have hTlow : 2^kOf N ≤ T := V42PublicSchedule.sampleEntries_lower _ _
  have hT1 : 1 ≤ T := Nat.one_le_two_pow.trans hTlow
  have hX : Real.logb 2 T ≤ (4+ε)*(kOf N : ℝ)*(Nat.clog 2 n : ℝ) :=
    (logb_le_clog T hT1).trans hsharp
  have hXk : (kOf N : ℝ) ≤ Real.logb 2 T := by
    have hr : (2 : ℝ)^(kOf N) ≤ T := by exact_mod_cast hTlow
    have hh := (Real.logb_le_logb (by norm_num : (1 : ℝ)<2)
      (by positivity) (by exact_mod_cast (by omega : 0<T))).2 hr
    rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ)<2), mul_one] at hh
  exact core c ε _ _ _ _ hc0 hε (by linarith) hcε hX hL hXk hklog
    (Real.logb_pos (by norm_num) (by exact_mod_cast (by omega : 1<N)))
    (by exact_mod_cast hk1)

#print axioms schedule_budget_eq
#print axioms sample_sharp
#print axioms iterations_eventually_ge
#print axioms entries_eventually_ge
#print axioms gap_exceeds_twice_error

end
end CurrentAdditive.V42ETHArithmetic

