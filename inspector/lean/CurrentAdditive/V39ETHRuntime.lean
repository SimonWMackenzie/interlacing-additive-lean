import CurrentAdditive.V39ETHAsymptotics

/-! Arithmetic resource consequences for the literal v39 square sample.
No physical algorithm or all-tape clock is asserted. The theorem proves that
a clock polynomial in the actual printed size, once independently constructed,
has the sparse-ETH subexponential rate.
-/

namespace CurrentAdditive.V39ETHArithmetic

noncomputable section

open Paper2.Unit4Shell.Asymptotics

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- A coarse absolute-exponent bound for the *actual* sampled table, with no
admissibility or promise needed. The constant is deliberately generous.
-/
theorem sample_entries_polynomial (n k : ℕ) (hn : 1 ≤ n) :
    V39PublicSchedule.sampleEntries (Nat.clog 2 n) k ≤
      (n+2)^(1000*(k+1)) := by
  let L := Nat.clog 2 n
  have he : ell L ≤ L := V39PublicSchedule.ell_le L
  have hke : k*ell L ≤ k*L := Nat.mul_le_mul_left k he
  have hb : budget L k ≤ 71*(k+1)*(L+1) := by
    dsimp [budget, seedCost, overhead]
    nlinarith
  have hclog : Nat.clog 2 (budget L k+2) ≤ budget L k+2 := by
    apply (Nat.clog_le_iff_le_pow (by decide : 1<2)).2
    exact Nat.le_of_lt Nat.lt_two_pow_self
  have hs := V39PublicSchedule.sampleEntries_clog_upper L k
  rw [schedule_budget_eq] at hs
  have hbound : Nat.clog 2 (V39PublicSchedule.sampleEntries L k) ≤
      500*(k+1)*(L+1) := by nlinarith
  have hpow : V39PublicSchedule.sampleEntries L k ≤
      2^(500*(k+1)*(L+1)) :=
    (Nat.le_pow_clog (by decide) _).trans
      (Nat.pow_le_pow_right (by decide) hbound)
  have hside : 2^(L+1) ≤ (n+2)^2 := by
    have hround := V39PublicSchedule.pow2Ceil_lt_twice n (by omega)
    change 2^L < 2*n at hround
    rw [pow_succ]
    nlinarith
  calc
    V39PublicSchedule.sampleEntries (Nat.clog 2 n) k ≤
        2^(500*(k+1)*(L+1)) := hpow
    _ = (2^(L+1))^(500*(k+1)) := by rw [← pow_mul]; congr 1; ring
    _ ≤ ((n+2)^2)^(500*(k+1)) := Nat.pow_le_pow_left hside _
    _ = (n+2)^(1000*(k+1)) := by rw [← pow_mul]; congr 1; ring

/-- Every fixed polynomial of the literal printed table size is
subexponential, uniformly over all source sizes satisfying the upper bound.
-/
theorem sample_polynomial_subexponential (p q C : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ n,
      1 ≤ n → n ≤ N*(Nat.clog 2 (N+2))^p →
      C*(V39PublicSchedule.sampleEntries (Nat.clog 2 n) (kOf N)+1)^q ≤
        C*2^q*⌈(2 : ℝ)^(ε*N)⌉₊ := by
  obtain ⟨N₀, hN₀⟩ := Paper2.Unit4Shell.T24Runtime.subexponential (1000*q) p ε hε
  refine ⟨N₀, ?_⟩
  intro N hN n hn hs
  have hpoly := sample_entries_polynomial n (kOf N) hn
  have hbase : 1 ≤ (n+2)^(1000*(kOf N+1)) := Nat.one_le_pow _ _ (by omega)
  have ht : V39PublicSchedule.sampleEntries (Nat.clog 2 n) (kOf N)+1 ≤
      2*(n+2)^(1000*(kOf N+1)) := by omega
  have hr := hN₀ N hN n hn hs
  have hnat : (n+2)^((1000*q)*(kOf N+1)) ≤ ⌈(2 : ℝ)^(ε*N)⌉₊ := by
    exact_mod_cast hr.trans (Nat.le_ceil _)
  calc
    C*(V39PublicSchedule.sampleEntries (Nat.clog 2 n) (kOf N)+1)^q ≤
        C*(2*(n+2)^(1000*(kOf N+1)))^q :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ht _)
    _ = C*2^q*(n+2)^((1000*q)*(kOf N+1)) := by
      rw [mul_pow, ← pow_mul]
      have he : 1000*(kOf N+1)*q = (1000*q)*(kOf N+1) := by ring
      rw [he]
      ring
    _ ≤ C*2^q*⌈(2 : ℝ)^(ε*N)⌉₊ := Nat.mul_le_mul_left _ hnat

/-- The construction's `n^{E(k+1)}` resource envelope and an arbitrary
fixed polynomial in the actual table size share one subexponential bound.
Instantiating the envelope with a physical all-tape clock is a separate step.
-/
theorem construction_and_estimator_subexponential (p E q C D : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ n,
      1 ≤ n → n ≤ N*(Nat.clog 2 (N+2))^p →
      C*(n+2)^(E*(kOf N+1)) +
        D*(V39PublicSchedule.sampleEntries (Nat.clog 2 n) (kOf N)+1)^q ≤
          K*⌈(2 : ℝ)^(ε*N)⌉₊ := by
  obtain ⟨Nc, hNc⟩ := Paper2.Unit4Shell.T24Runtime.subexponential E p ε hε
  obtain ⟨Ne, hNe⟩ := sample_polynomial_subexponential p q D ε hε
  refine ⟨C+D*2^q, max Nc Ne, ?_⟩
  intro N hN n hn hs
  have hc := hNc N ((le_max_left _ _).trans hN) n hn hs
  have hcn : (n+2)^(E*(kOf N+1)) ≤ ⌈(2 : ℝ)^(ε*N)⌉₊ := by
    exact_mod_cast hc.trans (Nat.le_ceil _)
  have he := hNe N ((le_max_right _ _).trans hN) n hn hs
  have hm := Nat.mul_le_mul_left C hcn
  nlinarith

#print axioms sample_entries_polynomial
#print axioms sample_polynomial_subexponential
#print axioms construction_and_estimator_subexponential

end
end CurrentAdditive.V39ETHArithmetic
