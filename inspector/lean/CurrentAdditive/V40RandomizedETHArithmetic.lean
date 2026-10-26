import CurrentAdditive.V39ETHRuntime

/-! Arithmetic and class interfaces for the current unrestricted randomized
endpoint. These are intermediate composition lemmas. They do not assert a
physical constructor, output law, comparator, or complete machine clock. -/
namespace CurrentAdditive.V40RandomizedETHEndpoint
noncomputable section
open Paper2.Unit4Shell.Asymptotics
set_option maxHeartbeats 100000
set_option maxRecDepth 8192

/-- A polynomial in actual input bytes and an established source-resource
bound is subexponential in the original number of formula variables. -/
theorem polynomial_source_envelope_subexponential (E p C d : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ n m,
      1 ≤ n → n ≤ N*(Nat.clog 2 (N+2))^p →
      C*(m+(n+2)^(E*(kOf N+1))+1)^d ≤
        K*⌈(2 : ℝ)^(ε*N)⌉₊*(m+1)^d := by
  obtain ⟨N₀,hN₀⟩ := Paper2.Unit4Shell.T24Runtime.subexponential (E*d) p ε hε
  refine ⟨C*2^d,N₀,?_⟩
  intro N hN n m hn hs
  have hx : 1 ≤ (n+2)^(E*(kOf N+1)) := Nat.one_le_pow _ _ (by omega)
  have hbase : m+(n+2)^(E*(kOf N+1))+1 ≤
      (m+1)*(2*(n+2)^(E*(kOf N+1))) := by
    have hm := Nat.mul_le_mul_left m hx
    calc
      _ ≤ m*(n+2)^(E*(kOf N+1))+(n+2)^(E*(kOf N+1))+1 := by omega
      _ ≤ 2*(m*(n+2)^(E*(kOf N+1))+(n+2)^(E*(kOf N+1))) := by omega
      _ = _ := by ring
  have hr := hN₀ N hN n hn hs
  have hnat : (n+2)^((E*d)*(kOf N+1)) ≤ ⌈(2 : ℝ)^(ε*N)⌉₊ := by
    exact_mod_cast hr.trans (Nat.le_ceil _)
  calc
    _ ≤ C*((m+1)*(2*(n+2)^(E*(kOf N+1))))^d :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbase _)
    _ = C*2^d*(n+2)^((E*d)*(kOf N+1))*(m+1)^d := by
      rw [mul_pow,mul_pow,←pow_mul]
      have he : E*(kOf N+1)*d=(E*d)*(kOf N+1) := by ring
      rw [he]
      ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hnat)

/-- Both the literal binary raw clock and the actual printed entry count
fit one source-resource power. No physical clock is inferred here. -/
theorem binary_clock_and_entries (E n k : ℕ) (hn : 1 ≤ n) :
    2^(E*((k+1)*Nat.clog 2 n)) +
        V39PublicSchedule.sampleEntries (Nat.clog 2 n) k ≤
      2*(n+2)^((2*E+1000)*(k+1)) := by
  have hc : 2^(Nat.clog 2 n) ≤ (n+2)^2 := by
    have h := V39PublicSchedule.pow2Ceil_lt_twice n (by omega)
    change 2^(Nat.clog 2 n) < 2*n at h
    nlinarith
  have hb : 2^(E*((k+1)*Nat.clog 2 n)) ≤ (n+2)^((2*E)*(k+1)) := by
    calc
      _ = (2^(Nat.clog 2 n))^(E*(k+1)) := by
        rw [←pow_mul]
        congr 1
        ring
      _ ≤ ((n+2)^2)^(E*(k+1)) := Nat.pow_le_pow_left hc _
      _ = _ := by rw [←pow_mul]; congr 1; ring
  have ht := V39ETHArithmetic.sample_entries_polynomial n k hn
  have hb' : (n+2)^((2*E)*(k+1)) ≤
      (n+2)^((2*E+1000)*(k+1)) :=
    Nat.pow_le_pow_right (by omega) (by nlinarith)
  have ht' : (n+2)^(1000*(k+1)) ≤
      (n+2)^((2*E+1000)*(k+1)) :=
    Nat.pow_le_pow_right (by omega) (by nlinarith)
  omega

/-- This is an honest intermediate arithmetic join: the complete physical
machine must separately be bounded by the displayed left hand expression. -/
theorem raw_clock_and_estimator_subexponential (E p C d : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ n m,
      1 ≤ n → n ≤ N*(Nat.clog 2 (N+2))^p →
      C*(m+2^(E*((kOf N+1)*Nat.clog 2 n))+
        V39PublicSchedule.sampleEntries (Nat.clog 2 n) (kOf N)+1)^d ≤
        K*⌈(2 : ℝ)^(ε*N)⌉₊*(m+1)^d := by
  obtain ⟨K,N₀,h⟩ := polynomial_source_envelope_subexponential
    (2*E+1000) p (C*2^d) d ε hε
  refine ⟨K,N₀,?_⟩
  intro N hN n m hn hs
  have hb := binary_clock_and_entries E n (kOf N) hn
  have hbase : m+2^(E*((kOf N+1)*Nat.clog 2 n))+
      V39PublicSchedule.sampleEntries (Nat.clog 2 n) (kOf N)+1 ≤
      2*(m+(n+2)^((2*E+1000)*(kOf N+1))+1) := by omega
  calc
    _ ≤ C*(2*(m+(n+2)^((2*E+1000)*(kOf N+1))+1))^d :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbase _)
    _ = (C*2^d)*(m+(n+2)^((2*E+1000)*(kOf N+1))+1)^d := by
      simp only [mul_pow,Nat.mul_assoc]
    _ ≤ _ := h N hN n m hn hs

#print axioms polynomial_source_envelope_subexponential
#print axioms binary_clock_and_entries
#print axioms raw_clock_and_estimator_subexponential
end
end CurrentAdditive.V40RandomizedETHEndpoint
