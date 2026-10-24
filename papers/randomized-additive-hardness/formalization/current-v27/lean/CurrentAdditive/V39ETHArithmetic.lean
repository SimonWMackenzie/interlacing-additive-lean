import Paper2.A4Asymptotics
import Paper2.A4T24Runtime

/-!
Private arithmetic for v39 Section 6 (mathematics unchanged from v38).
This module does not postulate an asymptotic printed-size or clock endpoint.
The logarithmic-overhead estimate is proved from the literal full schedule.
The source size hypothesis remains visible: it belongs to the external
source reduction, rather than the amplification arithmetic.
-/

namespace CurrentAdditive.V39ETHArithmetic

noncomputable section

open Paper2.Unit4Shell.Asymptotics

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

def ell (L : ℕ) : ℕ := Nat.clog 2 (L + 1)
def overhead (L : ℕ) : ℕ := L + 64 + 28 * ell L
def seedCost (L : ℕ) : ℕ := ell L + 7
def budget (L k : ℕ) : ℕ := seedCost L + k * overhead L

/-- The exact public full-product overhead has no hidden asymptotic premise. -/
theorem overhead_relative (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (L : ℕ) (hL : ((178 : ℝ) / δ + 1)^2 ≤ (L : ℝ) + 2) :
    (overhead L : ℝ) ≤ (1 + δ) * L := by
  have he : (ell L : ℝ) ≤ Real.logb 2 ((L : ℝ) + 2) + 1 := by
    have h := clog_le_logb_add_one (L + 1) (by omega)
    have hm : Real.logb 2 ((L + 1 : ℕ) : ℝ) ≤
        Real.logb 2 ((L : ℝ) + 2) := by
      apply (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2)
        (by positivity) (by positivity)).2
      push_cast
      linarith
    dsimp [ell]
    linarith
  have hs := small_log 28 92 δ L (by norm_num) (by norm_num)
    hδ hδ1 (by positivity) (by norm_num at hL ⊢; exact hL)
  dsimp [overhead]
  push_cast
  linarith

/-- The same literal cutoff makes the lookup seed fit inside `L` bits. -/
theorem seed_le_of_relative (δ : ℝ) (hδ1 : δ ≤ 1)
    (L : ℕ) (hh : (overhead L : ℝ) ≤ (1 + δ) * L) :
    seedCost L ≤ L := by
  have h0 : (0 : ℝ) ≤ L := by positivity
  have he0 : (0 : ℝ) ≤ ell L := by positivity
  have h : (ell L : ℝ) + 7 ≤ L := by
    dsimp [overhead] at hh
    push_cast at hh
    nlinarith
  exact_mod_cast h

/-- The final comparison uses coefficient four for the directly square sample. -/
theorem core (c ε X k ℓ L : ℝ) (hc0 : 0 ≤ c) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 2)
    (hcε : 2 * c * ((4 + ε) * (1 + ε)) < 1 - ε)
    (hX : X ≤ (4 + ε) * k * L) (hL : L ≤ (1 + ε) * ℓ)
    (hXk : k ≤ X) (hk : (1 - ε) * ℓ ≤ Real.logb 2 k)
    (hℓ : 0 < ℓ) (hk1 : 1 ≤ k) :
    2 * c * (X / Real.logb 2 X) < k := by
  have hkpos : 0 < k := by linarith
  have hlk : 0 < Real.logb 2 k := lt_of_lt_of_le (by nlinarith) hk
  have hlX : Real.logb 2 k ≤ Real.logb 2 X :=
    (Real.logb_le_logb (by norm_num) hkpos (by linarith)).2 hXk
  have hlXpos : 0 < Real.logb 2 X := lt_of_lt_of_le hlk hlX
  have hX2 : X ≤ (4 + ε) * (1 + ε) * k * ℓ := by
    have hh := mul_le_mul_of_nonneg_left hL
      (show 0 ≤ (4 + ε) * k by positivity)
    nlinarith
  have hden : (1 - ε) * ℓ ≤ Real.logb 2 X := hk.trans hlX
  rw [mul_div_assoc', div_lt_iff₀ hlXpos]
  have hstep : 2 * c * X ≤ 2 * c * ((4 + ε) * (1 + ε) * k * ℓ) :=
    mul_le_mul_of_nonneg_left hX2 (by positivity)
  have hstep2 : k * ((1 - ε) * ℓ) ≤ k * Real.logb 2 X :=
    mul_le_mul_of_nonneg_left hden hkpos.le
  have hkl : 0 < k * ℓ := mul_pos hkpos hℓ
  nlinarith [mul_lt_mul_of_pos_right hcε hkl]

/-- Each error constant below 1/8 has positive rational slack. -/
theorem exists_accuracy (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 8) :
    ∃ ε : ℚ, 0 < ε ∧ ε ≤ 1 / 100 ∧
      2 * c * ((4 + (ε : ℝ)) * (1 + (ε : ℝ))) < 1 - (ε : ℝ) := by
  have hpos : (0 : ℝ) < (1 - 8 * c) / 100 := by linarith
  obtain ⟨ε, hε0, hε1⟩ := exists_rat_btwn hpos
  refine ⟨ε, by exact_mod_cast hε0, ?_, ?_⟩
  · have : ((ε : ℚ) : ℝ) ≤ ((1 / 100 : ℚ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · have h2c : 2 * c < (1 - 100 * (ε : ℝ)) / 4 := by linarith
    have hq : (0 : ℝ) < (4 + (ε : ℝ)) * (1 + (ε : ℝ)) := by positivity
    have hlt := mul_lt_mul_of_pos_right h2c hq
    have hcube : (0 : ℝ) ≤ (ε : ℝ) ^ 3 := by positivity
    nlinarith

/-- A harmless explicit envelope for the logarithmic sample-size remainder. -/
theorem log_budget_le (L k : ℕ) (hL : 1 ≤ L) (hk : 1 ≤ k)
    (hseed : seedCost L ≤ L) (hh : overhead L ≤ 7 * L) :
    Nat.clog 2 (budget L k + 2) ≤ k + L + 4 := by
  have hLk : L ≤ k * L := Nat.le_mul_of_pos_left L hk
  have hkh : k * overhead L ≤ k * (7 * L) := Nat.mul_le_mul_left k hh
  have hb : budget L k ≤ 8 * k * L := by
    dsimp [budget]
    nlinarith
  have hkL : 1 ≤ k * L := by nlinarith
  have hbase : budget L k + 2 ≤ 16 * k * L := by nlinarith
  have hkp : k ≤ 2 ^ k := Nat.le_of_lt Nat.lt_two_pow_self
  have hLp : L ≤ 2 ^ L := Nat.le_of_lt Nat.lt_two_pow_self
  have hp : 16 * k * L ≤ 2 ^ (k + L + 4) := by
    calc
      16*k*L ≤ 16*(2^k)*(2^L) := by gcongr
      _ = 2^(k+L+4) := by simp only [pow_add]; norm_num; ring
  exact (Nat.clog_le_iff_le_pow (by decide)).2 (hbase.trans hp)

/-- Concrete sufficient cutoffs, rather than an assumed small-o size bound. -/
def lengthCutoff (ε : ℝ) : ℕ :=
  max 22 (max ⌈((178 : ℝ) / (ε / 12) + 1)^2⌉₊ ⌈(12 : ℝ) / ε⌉₊)

def iterationCutoff (ε : ℝ) : ℕ := max 1 ⌈(21 : ℝ) / ε⌉₊

/-- Discharge the logarithmic remainder from the exact elementary sample bound.
The final exact-schedule theorem supplies `hT` from the literal sampler formula.
-/
theorem sharp_from_sample_bound (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (L k T : ℕ) (hL : lengthCutoff ε ≤ L)
    (hk : iterationCutoff ε ≤ k)
    (hT : Nat.clog 2 T ≤ 4 * budget L k + 2 * k +
      2 * Nat.clog 2 (budget L k + 2) + 12) :
    (Nat.clog 2 T : ℝ) ≤ (4 + ε) * k * L := by
  have hL22 : 22 ≤ L := (le_max_left _ _).trans hL
  have hk1 : 1 ≤ k := (le_max_left _ _).trans hk
  have hlarge : ((178 : ℝ)/(ε/12)+1)^2 ≤ (L : ℝ)+2 := by
    have hnat : ⌈((178 : ℝ)/(ε/12)+1)^2⌉₊ ≤ L :=
      (le_max_left _ _).trans ((le_max_right _ _).trans hL)
    have hr : ((178 : ℝ)/(ε/12)+1)^2 ≤ (L : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hnat)
    linarith
  have hrel := overhead_relative (ε/12) (by positivity) (by linarith) L hlarge
  have hs := seed_le_of_relative (ε/12) (by linarith) L hrel
  have h7 : overhead L ≤ 7*L := by
    have hr : (overhead L : ℝ) ≤ 7*(L : ℝ) := by
      have h0 : (0 : ℝ) ≤ L := by positivity
      nlinarith
    exact_mod_cast hr
  have hlog := log_budget_le L k (by omega) hk1 hs h7
  have hb : (budget L k : ℝ) ≤ L + (k : ℝ) * ((1+ε/12)*L) := by
    have hsq : (seedCost L : ℝ) ≤ L := by exact_mod_cast hs
    have hmul := mul_le_mul_of_nonneg_left hrel (show (0 : ℝ) ≤ k by positivity)
    dsimp [budget]
    push_cast
    linarith
  have hK : (21 : ℝ) ≤ ε*(k : ℝ) := by
    have hnat : ⌈(21 : ℝ)/ε⌉₊ ≤ k := (le_max_right _ _).trans hk
    have hr : (21 : ℝ)/ε ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast hnat)
    have := (div_le_iff₀ hε).1 hr
    linarith
  have hLen : (12 : ℝ) ≤ ε*(L : ℝ) := by
    have hnat : ⌈(12 : ℝ)/ε⌉₊ ≤ L :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hL)
    have hr : (12 : ℝ)/ε ≤ L := (Nat.le_ceil _).trans (by exact_mod_cast hnat)
    have := (div_le_iff₀ hε).1 hr
    linarith
  have hTR : (Nat.clog 2 T : ℝ) ≤ 4*(budget L k : ℝ)+2*k+
      2*(Nat.clog 2 (budget L k + 2) : ℝ)+12 := by exact_mod_cast hT
  have hlogR : (Nat.clog 2 (budget L k + 2) : ℝ) ≤ (k : ℝ)+L+4 := by exact_mod_cast hlog
  have hLR : (22 : ℝ) ≤ L := by exact_mod_cast hL22
  have hterm1 := mul_le_mul_of_nonneg_right hK (show (0 : ℝ) ≤ L by positivity)
  have hterm2 := mul_le_mul_of_nonneg_right hLen (show (0 : ℝ) ≤ k by positivity)
  nlinarith

/-- A fixed polynomial of any `n^{E(k+1)}` clock is still subexponential.
The supplied upper bound on `n` is precisely the sparse-source size relation.
No machine is inferred from an arithmetic bound. -/
theorem polynomial_clock_subexponential (E p q C : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ n : ℕ,
      1 ≤ n → n ≤ N * (Nat.clog 2 (N + 2)) ^ p →
      ((C * (n + 2) ^ (E * (kOf N + 1))) ^ q : ℕ) ≤
        C ^ q * ⌈(2 : ℝ) ^ (ε * N)⌉₊ := by
  obtain ⟨N₀, hN₀⟩ := Paper2.Unit4Shell.T24Runtime.subexponential (E*q) p ε hε
  refine ⟨N₀, ?_⟩
  intro N hN n hn hs
  have hr := hN₀ N hN n hn hs
  have hb : (n + 2) ^ ((E*q) * (kOf N + 1)) ≤
      ⌈(2 : ℝ) ^ (ε * N)⌉₊ := by
    exact_mod_cast hr.trans (Nat.le_ceil _)
  calc
    (C * (n + 2) ^ (E * (kOf N + 1))) ^ q =
        C^q * (n+2)^((E*q)*(kOf N+1)) := by
      rw [mul_pow, ← pow_mul]
      congr 2
      ring
    _ ≤ C ^ q * ⌈(2 : ℝ) ^ (ε * N)⌉₊ := Nat.mul_le_mul_left _ hb

#print axioms overhead_relative
#print axioms seed_le_of_relative
#print axioms core
#print axioms exists_accuracy
#print axioms log_budget_le
#print axioms sharp_from_sample_bound
#print axioms polynomial_clock_subexponential

end
end CurrentAdditive.V39ETHArithmetic
