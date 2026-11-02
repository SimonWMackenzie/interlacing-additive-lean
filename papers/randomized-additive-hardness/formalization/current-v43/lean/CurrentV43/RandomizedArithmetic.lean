import CurrentAdditive.V42ETHAsymptotics

/-! Private v43 quantitative-rate candidate. Source: v43 main.tex lines
338--348 and 3306--3365, SHA256
bfde23b90f50785939095a6d37b7b247965ee6c45beaca9011a8963dec3cc9d6.
This file proves arithmetic only; it does not postulate a SAT algorithm. -/

namespace CurrentAdditive.V43RandomizedRate
noncomputable section
open Paper2.Unit4Shell.Asymptotics
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

/-- Dyadic rational-power numerator; all arithmetic is over natural numbers. -/
def numerator (a b N : ℕ) : ℕ := 2 ^ ((a * Nat.clog 2 N) / b)

/-- Fixed rational-power iteration recipe, computed using natural arithmetic. -/
def iterations (a b N : ℕ) : ℕ := numerator a b N / Nat.clog 2 N

theorem numerator_pos (a b N : ℕ) : 1 ≤ numerator a b N := Nat.one_le_two_pow

/-- The dyadic numerator has exponent beta=a/b up to a fixed additive error. -/
theorem numerator_log_bounds (a b N : ℕ) (hb : 0 < b) (hN : 1 ≤ N) :
    (a:ℝ)/(b:ℝ)*Real.logb 2 N-1 ≤ Real.logb 2 (numerator a b N) ∧
    Real.logb 2 (numerator a b N) ≤ (a:ℝ)/(b:ℝ)*(Real.logb 2 N+1) := by
  let C := Nat.clog 2 N
  let M := a*C/b
  have hbR : (0:ℝ) < b := by exact_mod_cast hb
  have hlo : a*C < (M+1)*b := by
    have hm := Nat.mod_lt (a*C) hb
    have hd := Nat.div_add_mod (a*C) b
    dsimp [M]
    nlinarith
  have hhi : M*b ≤ a*C := Nat.div_mul_le_self _ _
  have hloR : (a:ℝ)*C < ((M:ℝ)+1)*b := by exact_mod_cast hlo
  have hhiR : (M:ℝ)*b ≤ (a:ℝ)*C := by exact_mod_cast hhi
  have hCl : Real.logb 2 N ≤ (C:ℝ) := logb_le_clog N hN
  have hCu : (C:ℝ) ≤ Real.logb 2 N+1 := clog_le_logb_add_one N hN
  have hm1 : (a:ℝ)/b*Real.logb 2 N-1 ≤ M := by
    have hm := mul_le_mul_of_nonneg_left hCl (show (0:ℝ) ≤ a by positivity)
    rw [sub_le_iff_le_add,div_mul_eq_mul_div,div_le_iff₀ hbR]
    nlinarith
  have hm2 : (M:ℝ) ≤ (a:ℝ)/b*(Real.logb 2 N+1) := by
    have hm := mul_le_mul_of_nonneg_left hCu (show (0:ℝ) ≤ a by positivity)
    rw [div_mul_eq_mul_div,le_div_iff₀ hbR]
    nlinarith
  have he : Real.logb 2 (numerator a b N) = M := by
    simp [numerator,M,C,Real.logb_pow]
  rw [he]
  exact ⟨hm1,hm2⟩

/-- The dyadic quotient recipe has logarithmic slope beta=a/b, with arbitrary
positive slack. The explicit cutoff is only in log N. -/
theorem iterations_log_lower (a b N : ℕ) (hb : 0<b) (hN : 2≤N)
    (ε : ℝ) (hε : 0<ε) (hε1 : ε≤1) (hεβ : ε≤(a:ℝ)/(b:ℝ))
    (hlarge : ((7:ℝ)/ε+1)^2 ≤ Real.logb 2 N+2) :
    1 ≤ iterations a b N ∧
    ((a:ℝ)/(b:ℝ)-ε)*Real.logb 2 N ≤ Real.logb 2 (iterations a b N) := by
  let R := numerator a b N
  let C := Nat.clog 2 N
  let ℓ := Real.logb 2 N
  have hNp : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hℓ : 1≤ℓ := by
    dsimp [ℓ]
    rw [Real.le_logb_iff_rpow_le (by norm_num) hNp]
    simpa using (show (2:ℝ)≤N by exact_mod_cast hN)
  have hC : 1≤C := Nat.succ_le_of_lt (Nat.clog_pos (by decide) (by omega))
  have hCp : (0:ℝ)<C := by exact_mod_cast hC
  have hCl : (C:ℝ)≤ℓ+1 := clog_le_logb_add_one N (by omega)
  have hlogC : Real.logb 2 C ≤ Real.logb 2 (ℓ+2) :=
    (Real.logb_le_logb (by norm_num) hCp (by linarith)).2 (by linarith)
  have hsmall := small_log 1 2 ε ℓ (by norm_num) (by norm_num)
    hε hε1 (by linarith) (by norm_num [ℓ] at *; exact hlarge)
  have hr := (numerator_log_bounds a b N hb (by omega)).1
  have hRp : (0:ℝ)<R := by exact_mod_cast numerator_pos a b N
  have h2Clog : Real.logb 2 (2*(C:ℝ))≤Real.logb 2 R := by
    rw [Real.logb_mul (by norm_num) hCp.ne',Real.logb_self_eq_one (by norm_num : (1:ℝ)<2)]
    have hm := mul_le_mul_of_nonneg_right hεβ (show 0≤ℓ by linarith)
    dsimp [R,ℓ] at *
    linarith
  have h2C : 2*C≤R := by
    exact_mod_cast (Real.logb_le_logb (by norm_num : (1:ℝ)<2)
      (by positivity) hRp).1 h2Clog
  have hk : 1≤R/C := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  have hRk : R≤2*(R/C)*C := by
    have hd := Nat.mod_lt R (show 0<C by omega)
    have he := Nat.mod_add_div R C
    have hm := Nat.mul_le_mul_right C hk
    nlinarith
  have hRkR : (R:ℝ)≤2*(R/C:ℕ)*C := by exact_mod_cast hRk
  have hkp : (0:ℝ)<(R/C:ℕ) := by exact_mod_cast hk
  have hlog := (Real.logb_le_logb (by norm_num : (1:ℝ)<2) hRp (by positivity)).2 hRkR
  rw [Real.logb_mul (by positivity) hCp.ne',Real.logb_mul (by norm_num) hkp.ne',
    Real.logb_self_eq_one (by norm_num : (1:ℝ)<2)] at hlog
  refine ⟨hk,?_⟩
  change ((a:ℝ)/(b:ℝ)-ε)*ℓ ≤ Real.logb 2 (R/C:ℕ)
  dsimp [R,ℓ] at *
  nlinarith

theorem rate_core (c ε β X k ℓ L : ℝ) (hc0 : 0≤c) (hε : 0<ε)
    (hβε : ε<β) (hcε : 2*c*((4+ε)*(1+ε))<β-ε)
    (hX : X≤(4+ε)*k*L) (hL : L≤(1+ε)*ℓ)
    (hXk : k≤X) (hk : (β-ε)*ℓ≤Real.logb 2 k) (hℓ : 0<ℓ) (hk1 : 1≤k) :
    2*c*(X/Real.logb 2 X)<k := by
  have hkp : 0<k := by linarith
  have hlkp : 0<Real.logb 2 k := lt_of_lt_of_le (by positivity) hk
  have hlX := (Real.logb_le_logb (by norm_num : (1:ℝ)<2) hkp (by linarith)).2 hXk
  have hlXp : 0<Real.logb 2 X := hlkp.trans_le hlX
  have hXX : X≤(4+ε)*(1+ε)*k*ℓ := by
    have hm := mul_le_mul_of_nonneg_left hL (show 0≤(4+ε)*k by positivity)
    nlinarith
  have hden : (β-ε)*ℓ≤Real.logb 2 X := hk.trans hlX
  rw [mul_div_assoc',div_lt_iff₀ hlXp]
  have hs := mul_le_mul_of_nonneg_left hXX (show 0≤2*c by positivity)
  have ht := mul_le_mul_of_nonneg_left hden hkp.le
  have hkl : 0<k*ℓ := mul_pos hkp hℓ
  nlinarith [mul_lt_mul_of_pos_right hcε hkl]

/-- For every desired exponent above 8c there is strictly positive rational
slack for the sharp coefficient-four sample estimate. -/
theorem exists_accuracy (c β : ℝ) (hc0 : 0 ≤ c) (hβ : β ≤ 1) (hc : 8*c < β) :
    ∃ ε : ℚ, 0 < ε ∧ ε ≤ 1/100 ∧ (ε:ℝ) < β ∧
      2*c*((4+(ε:ℝ))*(1+(ε:ℝ))) < β-(ε:ℝ) := by
  obtain ⟨ε,hε0,hεlt⟩ := exists_rat_btwn (show (0:ℝ) < (β-8*c)/100 by linarith)
  have hε1 : (ε:ℝ) ≤ 1/100 := by linarith
  have hεβ : (ε:ℝ) < β := by linarith
  have hclt : c < 1/8 := by linarith
  have hsq : (ε:ℝ)^2 ≤ (ε:ℝ) := by nlinarith
  have hfac : (4+(ε:ℝ))*(1+(ε:ℝ)) ≤ 4+6*(ε:ℝ) := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hfac (show 0 ≤ 2*c by positivity)
  have hcε := mul_nonneg (show 0 ≤ 1/4-2*c by linarith) (show 0 ≤ (ε:ℝ) by linarith)
  refine ⟨ε,by exact_mod_cast hε0,?_,hεβ,?_⟩
  · exact (Rat.cast_le (K := ℝ)).mp (by norm_num; exact hε1)
  · nlinarith

/-- Any fixed iteration cutoff is eventually reached by the computable
dyadic schedule, for every positive rational exponent. -/
theorem iterations_eventually_ge (a b K : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → K ≤ iterations a b N := by
  let β : ℝ := (a:ℝ)/(b:ℝ)
  let ε : ℝ := min 1 (β/2)
  have hβ : 0 < β := by dsimp [β]; positivity
  have hε : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεβ : ε ≤ β/2 := min_le_right _ _
  let I := max 1 K
  let Y := max (((7:ℝ)/ε+1)^2) (2*Real.logb 2 I/β+1)
  refine ⟨max 2 ⌈(2:ℝ)^Y⌉₊,?_⟩
  intro N hN
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hNY := logb_ge_of_ge Y N ((le_max_right _ _).trans hN)
  have hs : ((7:ℝ)/ε+1)^2 ≤ Real.logb 2 N+2 := by
    have := (le_max_left _ _).trans hNY
    linarith
  obtain ⟨hk,hlog⟩ := iterations_log_lower a b N hb hN2 ε hε hε1 (by dsimp [β] at *; linarith) hs
  have hI : 1 ≤ I := le_max_left _ _
  have hIp : (0:ℝ) < I := by exact_mod_cast hI
  have hkp : (0:ℝ) < iterations a b N := by exact_mod_cast hk
  have hY2 : 2*Real.logb 2 I/β+1 ≤ Real.logb 2 N := (le_max_right _ _).trans hNY
  have hℓ : 0 ≤ Real.logb 2 N := Real.logb_nonneg (by norm_num) (by exact_mod_cast (by omega : 1 ≤ N))
  have hIlog : Real.logb 2 I ≤ Real.logb 2 (iterations a b N) := by
    have hx := (div_le_iff₀ hβ).1 (show 2*Real.logb 2 I/β ≤ Real.logb 2 N by linarith)
    have hsl := mul_le_mul_of_nonneg_right hεβ hℓ
    change (β-ε)*Real.logb 2 N ≤ _ at hlog
    nlinarith
  have hIk : I ≤ iterations a b N := by
    exact_mod_cast (Real.logb_le_logb (by norm_num : (1:ℝ)<2) hIp hkp).1 hIlog
  exact (le_max_right 1 K).trans hIk

/-- The actual sample eventually exceeds any fixed table-size threshold,
uniformly over the graph logarithmic-size parameter. -/
theorem entries_eventually_ge (a b T₀ : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ L,
      T₀ ≤ V42PublicSchedule.sampleEntries L (iterations a b N) := by
  obtain ⟨N₀,h⟩ := iterations_eventually_ge a b T₀ ha hb
  refine ⟨N₀,?_⟩
  intro N hN L
  exact ((h N hN).trans (Nat.le_of_lt Nat.lt_two_pow_self)).trans
    (V42PublicSchedule.sampleEntries_lower _ _)

/-- The literal v42 square sample at the new schedule beats twice the
estimator error whenever beta=a/b exceeds 8c. No printed-size estimate is
assumed: coefficient four comes from the checked public sample recipe. -/
theorem gap_exceeds_twice_error (a b Δ p : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hβ1 : (a:ℝ)/(b:ℝ) ≤ 1) (hΔ : 0 < Δ)
    (c : ℝ) (hc0 : 0 ≤ c) (hc : 8*c < (a:ℝ)/(b:ℝ)) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ n,
      1 ≤ n → N ≤ Δ*n → n ≤ N*(Nat.clog 2 (N+2))^p →
      2*c*(Real.logb 2 (V42PublicSchedule.sampleEntries (Nat.clog 2 n) (iterations a b N)) /
        Real.logb 2 (Real.logb 2 (V42PublicSchedule.sampleEntries (Nat.clog 2 n) (iterations a b N))))
        < (iterations a b N:ℝ) := by
  obtain ⟨εq,hεq,hεq1,hεβ,hcε⟩ := exists_accuracy c ((a:ℝ)/(b:ℝ)) hc0 hβ1 hc
  let ε : ℝ := εq
  have hε : 0 < ε := by dsimp [ε]; exact_mod_cast hεq
  have hε1 : ε ≤ 1/100 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hεq1
    norm_num at h
    exact h
  obtain ⟨Nk,hNk⟩ := iterations_eventually_ge a b (V42PublicSize.iterationCutoff ε) ha hb
  let Y1 : ℝ := ((3*(p:ℝ)+3)/ε+1)^2
  let Y2 : ℝ := ((7:ℝ)/ε+1)^2
  let Y := max Y1 Y2
  refine ⟨max Nk (max (Δ*2^(V42PublicSize.lengthCutoff ε)) (max 4 ⌈(2:ℝ)^Y⌉₊)),?_⟩
  intro N hN n hn hlow hsize
  have hN4 : 4 ≤ N := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hNY : ⌈(2:ℝ)^Y⌉₊ ≤ N := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hY := logb_ge_of_ge Y N hNY
  have hY1 := (le_max_left _ _).trans hY
  have hY2 := (le_max_right _ _).trans hY
  have hkcut := hNk N ((le_max_left _ _).trans hN)
  have hcutn : 2^(V42PublicSize.lengthCutoff ε) ≤ n := by
    have ht : Δ*2^(V42PublicSize.lengthCutoff ε) ≤ N := (le_max_left _ _).trans
      ((le_max_right _ _).trans hN)
    exact Nat.le_of_mul_le_mul_left (ht.trans hlow) hΔ
  have hLcut : V42PublicSize.lengthCutoff ε ≤ Nat.clog 2 n := by
    have hm := Nat.clog_mono_right 2 hcutn
    simpa only [Nat.clog_pow 2 _ (by decide)] using hm
  have hL := L_le p N n ε hε (by linarith) (by omega) hn hsize (by
    have he : 3*(p:ℝ)+1+2=3*p+3 := by ring
    rw [he]
    exact hY1.trans (by linarith))
  obtain ⟨hk1,hklog⟩ := iterations_log_lower a b N hb (by omega) ε hε (by linarith) (by exact hεβ.le)
    (by dsimp [Y2] at hY2; linarith)
  have hsharp := V42PublicSize.sample_sharp ε hε (by linarith) (Nat.clog 2 n) (iterations a b N) hLcut hkcut
  let T := V42PublicSchedule.sampleEntries (Nat.clog 2 n) (iterations a b N)
  have hTlow : 2^iterations a b N ≤ T := V42PublicSchedule.sampleEntries_lower _ _
  have hT1 : 1 ≤ T := Nat.one_le_two_pow.trans hTlow
  have hX : Real.logb 2 T ≤ (4+ε)*(iterations a b N:ℝ)*(Nat.clog 2 n:ℝ) :=
    (logb_le_clog T hT1).trans hsharp
  have hXk : (iterations a b N:ℝ) ≤ Real.logb 2 T := by
    have hr : (2:ℝ)^iterations a b N ≤ T := by exact_mod_cast hTlow
    have hh := (Real.logb_le_logb (by norm_num : (1:ℝ)<2) (by positivity)
      (by exact_mod_cast (by omega : 0 < T))).2 hr
    rwa [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1:ℝ)<2),mul_one] at hh
  exact rate_core c ε ((a:ℝ)/(b:ℝ)) _ _ _ _ hc0 hε hεβ hcε hX hL hXk hklog
    (Real.logb_pos (by norm_num) (by exact_mod_cast (by omega : 1 < N)))
    (by exact_mod_cast hk1)

/-- The dyadic numerator is within a factor two of the rational real power. -/
theorem numerator_le_power (a b N : ℕ) (hb : 0 < b) (hN : 1 ≤ N)
    (hβ1 : (a:ℝ)/(b:ℝ) ≤ 1) :
    (numerator a b N:ℝ) ≤ 2*(N:ℝ)^((a:ℝ)/(b:ℝ)) := by
  let β : ℝ := (a:ℝ)/(b:ℝ)
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  have hRp : (0:ℝ) < numerator a b N := by exact_mod_cast numerator_pos a b N
  have hQp : 0 < (N:ℝ)^β := Real.rpow_pos_of_pos hNp _
  have hlog := (numerator_log_bounds a b N hb hN).2
  apply (Real.logb_le_logb (by norm_num : (1:ℝ)<2) hRp (by positivity)).1
  rw [Real.logb_mul (by norm_num) hQp.ne',Real.logb_self_eq_one (by norm_num : (1:ℝ)<2),
    Real.logb_rpow_eq_mul_logb_of_pos hNp]
  change Real.logb 2 (numerator a b N) ≤ β*(Real.logb 2 N+1) at hlog
  dsimp [β] at *
  nlinarith

/-- A positive real power dominates the logarithm, with an explicit constant. -/
theorem log_le_power (N : ℕ) (hN : 1 ≤ N) (β : ℝ) (hβ : 0 < β) :
    Real.logb 2 N ≤ (2/β)*(N:ℝ)^β := by
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  have hQp : 0 < (N:ℝ)^β := Real.rpow_pos_of_pos hNp _
  have hlog := Real.log_le_sub_one_of_pos hQp
  rw [Real.log_rpow hNp] at hlog
  have hl : 0 ≤ Real.logb 2 N := Real.logb_nonneg (by norm_num) (by exact_mod_cast hN)
  have hlog2 : 1/2 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have he : Real.log N = Real.logb 2 N * Real.log 2 := by
    rw [Real.logb,div_mul_cancel₀ _ (ne_of_gt (Real.log_pos (by norm_num : (1:ℝ)<2)))]
  rw [he] at hlog
  rw [div_mul_eq_mul_div,le_div_iff₀ hβ]
  nlinarith [mul_nonneg (mul_nonneg hβ.le hl) (show 0 ≤ Real.log 2-1/2 by linarith)]

/-- The actual schedule cancels one factor log N in construction time. -/
theorem iterations_log_product (a b N : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hN : 2 ≤ N) (hβ1 : (a:ℝ)/(b:ℝ) ≤ 1) :
    ((iterations a b N:ℝ)+1)*Real.logb 2 N ≤
      (2+2/((a:ℝ)/(b:ℝ)))*(N:ℝ)^((a:ℝ)/(b:ℝ)) := by
  have hβ : 0 < (a:ℝ)/(b:ℝ) := by positivity
  have hnum := numerator_le_power a b N hb (by omega) hβ1
  have hℓ := log_le_power N (by omega) ((a:ℝ)/(b:ℝ)) hβ
  have hclog : Real.logb 2 N ≤ (Nat.clog 2 N:ℝ) := logb_le_clog N (by omega)
  have hk : (0:ℝ) ≤ iterations a b N := by positivity
  have hdiv : (iterations a b N:ℝ)*(Nat.clog 2 N:ℝ) ≤ numerator a b N := by
    exact_mod_cast Nat.div_mul_le_self (numerator a b N) (Nat.clog 2 N)
  have hm := mul_le_mul_of_nonneg_left hclog hk
  nlinarith

/-- Explicit exponential-power construction clock, with the leading power
valid for every requested alpha above beta. The ordinary polynomial clock
exponent E is fixed independently of N and k. -/
theorem construction_power_time (a b E p : ℕ) (ha : 0 < a) (hb : 0 < b)
    (α : ℝ) (hβα : (a:ℝ)/(b:ℝ) ≤ α) (hβ1 : (a:ℝ)/(b:ℝ) ≤ 1) :
    ∃ K N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ n,
      1 ≤ n → n ≤ N*(Nat.clog 2 (N+2))^p →
      (n+2)^(E*(iterations a b N+1)) ≤ ⌈(2:ℝ)^((K:ℝ)*(N:ℝ)^α)⌉₊ := by
  let β : ℝ := (a:ℝ)/(b:ℝ)
  let K : ℕ := ⌈4*(E:ℝ)*(2+2/β)⌉₊
  let Y : ℝ := (3*(p:ℝ)+4)^2
  refine ⟨K,max 2 ⌈(2:ℝ)^Y⌉₊,?_⟩
  intro N hN n hn hsize
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hNp : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hℓ1 : 1 ≤ Real.logb 2 N := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hNp]
    simpa using (show (2:ℝ) ≤ N by exact_mod_cast hN2)
  have hY := logb_ge_of_ge Y N ((le_max_right _ _).trans hN)
  have hL := L_le p N n 1 (by norm_num) le_rfl hN2 hn hsize (by
    norm_num
    have he : 3*(p:ℝ)+1+2+1=3*p+4 := by ring
    norm_num [Y] at hY
    nlinarith)
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hnn : ((n+2:ℕ):ℝ) ≤ 4*(n:ℝ) := by
    have h : (1:ℝ) ≤ n := by exact_mod_cast hn
    push_cast
    linarith
  have hlogn := (Real.logb_le_logb (by norm_num : (1:ℝ)<2) (by positivity) (by positivity)).2 hnn
  have h4 : Real.logb 2 (4:ℝ)=2 := by
    rw [show (4:ℝ)=2^(2:ℕ) by norm_num,Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1:ℝ)<2)]
    norm_num
  rw [Real.logb_mul (by norm_num) hnR.ne',h4] at hlogn
  have hlogn' := logb_le_clog n hn
  have hgraph : Real.logb 2 ((n+2:ℕ):ℝ) ≤ 4*Real.logb 2 N := by linarith
  have hprod := iterations_log_product a b N ha hb hN2 hβ1
  have hconst : 4*(E:ℝ)*(2+2/β) ≤ K := Nat.le_ceil _
  have hQ : 0 ≤ (N:ℝ)^β := Real.rpow_nonneg (by positivity) _
  have hα : (N:ℝ)^β ≤ (N:ℝ)^α := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ N)) hβα
  have hexp : ((E*(iterations a b N+1):ℕ):ℝ)*Real.logb 2 ((n+2:ℕ):ℝ) ≤ (K:ℝ)*(N:ℝ)^α := by
    have h1 := mul_le_mul_of_nonneg_left hgraph (show 0 ≤ (E:ℝ)*((iterations a b N:ℝ)+1) by positivity)
    have h2 := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 4*(E:ℝ) by positivity)
    have h3 := mul_le_mul_of_nonneg_right hconst hQ
    have h4 := mul_le_mul_of_nonneg_left hα (show (0:ℝ) ≤ K by positivity)
    push_cast at h1 h2 h3 h4 ⊢
    dsimp [β] at *
    nlinarith
  have hr : (((n+2)^(E*(iterations a b N+1)):ℕ):ℝ) ≤ (2:ℝ)^((K:ℝ)*(N:ℝ)^α) := by
    apply (Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) (by positivity)).1
    push_cast
    rw [Real.logb_pow]
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hexp
  exact_mod_cast hr.trans (Nat.le_ceil _)

/-- Fixed polynomial overheads on input bytes and the source-resource
bound are paid by enlarging the fixed exponent. The input length m is only
assumed to satisfy an ordinary numerical source-size estimate. -/
theorem polynomial_clock_power_time (a b E p C d q : ℕ)
    (ha : 0 < a) (hb : 0 < b) (α : ℝ)
    (hβα : (a:ℝ)/(b:ℝ) ≤ α) (hβ1 : (a:ℝ)/(b:ℝ) ≤ 1) :
    ∃ K N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ n m,
      1 ≤ n → n ≤ N*(Nat.clog 2 (N+2))^p →
      m ≤ (n+2)^(q*(iterations a b N+1)) →
      C*(m+(n+2)^(E*(iterations a b N+1))+1)^d ≤
        ⌈(2:ℝ)^((K:ℝ)*(N:ℝ)^α)⌉₊ := by
  let R := max E q
  obtain ⟨K,N₀,h⟩ := construction_power_time a b (C+d*(R+2)) p ha hb α hβα hβ1
  refine ⟨K,N₀,?_⟩
  intro N hN n m hn hsize hm
  let k := iterations a b N
  let Y := (n+2)^(R*(k+1))
  have hbase : 1 ≤ n+2 := by omega
  have hY : 1 ≤ Y := Nat.one_le_pow _ _ hbase
  have hE : (n+2)^(E*(k+1)) ≤ Y := Nat.pow_le_pow_right hbase
    (Nat.mul_le_mul_right _ (le_max_left _ _))
  have hmY : m ≤ Y := hm.trans (Nat.pow_le_pow_right hbase
    (Nat.mul_le_mul_right _ (le_max_right _ _)))
  have hsum : m+(n+2)^(E*(k+1))+1 ≤ (n+2)^2*Y := by
    have hb : 3 ≤ (n+2)^2 := by nlinarith
    have hh := Nat.mul_le_mul_right Y hb
    omega
  have hC : C ≤ (n+2)^C :=
    (Nat.le_of_lt Nat.lt_two_pow_self).trans (Nat.pow_le_pow_left (by omega) _)
  have hclock : C*(m+(n+2)^(E*(k+1))+1)^d ≤
      (n+2)^((C+d*(R+2))*(k+1)) := by
    calc
      _ ≤ (n+2)^C*((n+2)^2*Y)^d := Nat.mul_le_mul hC (Nat.pow_le_pow_left hsum _)
      _ = (n+2)^(C+d*(R*(k+1)+2)) := by
        dsimp [Y]
        rw [mul_pow,←pow_mul,←pow_mul,←pow_add,←pow_add]
        congr 1
        ring
      _ ≤ _ := Nat.pow_le_pow_right hbase (by nlinarith)
  exact hclock.trans (h N hN n hn hsize)

/-- Rational density selects an actual pair of positive integers strictly
between 8c and every requested exponent alpha. -/
theorem exists_rational_rate (c α : ℝ) (hc0 : 0 ≤ c) (hcα : 8*c < α) (hα1 : α < 1) :
    ∃ a b : ℕ, 0 < a ∧ a < b ∧ 8*c < (a:ℝ)/(b:ℝ) ∧ (a:ℝ)/(b:ℝ) < α := by
  obtain ⟨q,hql,hqu⟩ := exists_rat_btwn hcα
  have hqposR : 0 < (q:ℝ) := by linarith
  have hqpos : 0 < q := by exact_mod_cast hqposR
  have hnum : 0 < q.num := Rat.num_pos.mpr hqpos
  have hnumEq : (q.num.natAbs:ℝ) = (q.num:ℝ) := by
    have hInt : (q.num.natAbs:ℤ)=q.num := Int.natAbs_of_nonneg hnum.le
    have hcast := congrArg (fun z:ℤ => (z:ℝ)) hInt
    simpa only [Int.cast_natCast] using hcast
  have he : (q.num.natAbs:ℝ)/(q.den:ℝ) = (q:ℝ) := by
    rw [hnumEq,Rat.cast_def]
  have ha : 0 < q.num.natAbs := Int.natAbs_pos.mpr (ne_of_gt hnum)
  have hab : q.num.natAbs < q.den := by
    have h : (q.num.natAbs:ℝ)/(q.den:ℝ) < 1 := by rw [he]; linarith
    have hd : (0:ℝ) < q.den := by exact_mod_cast q.den_pos
    rw [div_lt_one hd] at h
    exact_mod_cast h
  exact ⟨q.num.natAbs,q.den,ha,hab,by simpa only [he] using hql,by simpa only [he] using hqu⟩

/-- Arithmetic part of v43 Corollary 1.4 for *every* 8c<alpha<1.
The output contains one concrete integer-arithmetic schedule, a fixed clock
constant, and one cutoff meeting all numeric requirements simultaneously.
It supplies no hypothesis asserting a SAT algorithm or the desired clock. -/
theorem quantitative_rate_arithmetic (c α : ℝ) (hc0 : 0 ≤ c)
    (hcα : 8*c < α) (hα1 : α < 1) (Δ p E T₀ : ℕ) (hΔ : 0 < Δ) :
    ∃ a b K N₀ : ℕ, 0 < a ∧ a < b ∧
      8*c < (a:ℝ)/(b:ℝ) ∧ (a:ℝ)/(b:ℝ) < α ∧
      ∀ N, N₀ ≤ N → ∀ n,
        1 ≤ n → N ≤ Δ*n → n ≤ N*(Nat.clog 2 (N+2))^p →
        let k := iterations a b N
        let T := V42PublicSchedule.sampleEntries (Nat.clog 2 n) k
        1 ≤ k ∧ T₀ ≤ T ∧ 4 ≤ T ∧
        2*c*(Real.logb 2 T / Real.logb 2 (Real.logb 2 T)) < (k:ℝ) ∧
        (n+2)^(E*(k+1)) ≤ ⌈(2:ℝ)^((K:ℝ)*(N:ℝ)^α)⌉₊ := by
  obtain ⟨a,b,ha,hab,hcβ,hβα⟩ := exists_rational_rate c α hc0 hcα hα1
  have hb : 0 < b := lt_trans ha hab
  have hβ1 : (a:ℝ)/(b:ℝ) ≤ 1 := by linarith
  obtain ⟨Ng,hg⟩ := gap_exceeds_twice_error a b Δ p ha hb hβ1 hΔ c hc0 hcβ
  obtain ⟨K,Nt,ht⟩ := construction_power_time a b E p ha hb α hβα.le hβ1
  obtain ⟨Nk,hk⟩ := iterations_eventually_ge a b (max 4 T₀) ha hb
  refine ⟨a,b,K,max Ng (max Nt Nk),ha,hab,hcβ,hβα,?_⟩
  intro N hN n hn hlow hhigh
  dsimp only
  have hklarge : max 4 T₀ ≤ iterations a b N := hk N
    ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hT : max 4 T₀ ≤ V42PublicSchedule.sampleEntries (Nat.clog 2 n) (iterations a b N) :=
    (hklarge.trans (Nat.le_of_lt Nat.lt_two_pow_self)).trans (V42PublicSchedule.sampleEntries_lower _ _)
  exact ⟨by omega,(le_max_right _ _).trans hT,(le_max_left _ _).trans hT,
    hg N ((le_max_left _ _).trans hN) n hn hlow hhigh,
    ht N ((le_max_left _ _).trans ((le_max_right _ _).trans hN)) n hn hhigh⟩

#print axioms numerator_log_bounds
#print axioms iterations_log_lower
#print axioms rate_core
#print axioms gap_exceeds_twice_error
#print axioms construction_power_time
#print axioms quantitative_rate_arithmetic
#print axioms polynomial_clock_power_time
#print axioms entries_eventually_ge
#print axioms exists_rational_rate
end
end CurrentAdditive.V43RandomizedRate
