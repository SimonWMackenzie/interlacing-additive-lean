import Paper2.SubexpLen
import Paper2.A4T24RuntimeComposed

/-!
# Paper A (lock v12), lane `owner:a-eth-1`, segment 3 (partial): the reduction's random bits fit
the effective tape `expLen |encode Φ|`

Lock v12 `sections/06-reduction.tex:137-141` (proof of `thm:quantitative`): "Both the
construction and any fixed polynomial-time estimator take $n^{O(k+1)}=2^{O(N/\log N)}=2^{o(N)}$".

The admitted random-bit bound `RandomBits.inputBits_le_resource` gives
`inputBits ≤ (n+2)^(160(k+1))` for the selected T24 experiment; with `k = kOf N`,
`n ≤ N·⌈log₂(N+2)⌉^p` (admitted `T10Size.t45_shell_form`) and `N ≤ |encode Φ| ≤ (N+2)³`
(admitted `T24RuntimeComposed.encode_length_cube`) this is at most the segment-1 effective tape
length `expLen |encode Φ| = 2^(|encode Φ| / ⌈log₂⌈log₂ |encode Φ|⌉⌉)` for all large `N`
(`reduction_bits_fit`). This checks that the segment-1 carrier is large enough for the
reduction's `2^{O(N/log N)}` random bits (the `2^{εN}` bound of `T24_runtime` alone would NOT
suffice, since `expLen m ≤ 2^{εm}` eventually for every `ε`). It is a numeric step of segment 3,
not the decider.

No ledger row is closed.
-/

noncomputable section

namespace Paper2.AEth

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics

theorem sq_le_two_pow_pred' (k : ℕ) : (k + 7) * (k + 7) ≤ 2 ^ (k + 6) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have e : k + 1 + 6 = (k + 6) + 1 := by omega
    rw [e, pow_succ]
    nlinarith

/-- For `c ≥ 7`, `c² ≤ 2^(c-1)`. -/
theorem sq_le_two_pow_pred (c : ℕ) (h : 7 ≤ c) : c * c ≤ 2 ^ (c - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, c = k + 7 := ⟨c - 7, by omega⟩
  have e : k + 7 - 1 = k + 6 := by omega
  rw [e]
  exact sq_le_two_pow_pred' k

theorem clog_ge_of_ge {C N : ℕ} (h : 2 ^ C ≤ N) : C ≤ Nat.clog 2 N := by
  have := Nat.clog_mono_right 2 h
  rwa [Nat.clog_pow 2 _ (by norm_num)] at this

/-- `⌈log₂(3c+3)⌉ ≤ ⌈log₂ c⌉ + 2` for `c ≥ 3`. -/
theorem clog_three_le (c : ℕ) (hc : 3 ≤ c) : Nat.clog 2 (3 * c + 3) ≤ Nat.clog 2 c + 2 := by
  apply Nat.clog_le_of_le_pow
  have h1 : c ≤ 2 ^ Nat.clog 2 c := Nat.le_pow_clog (by norm_num) c
  rw [pow_add]
  norm_num
  omega

/-- **Numeric core.** For constants `K p` there is `N₀` such that for `N ≥ N₀`, every
`n ≤ N·⌈log₂(N+2)⌉^p` and every `m` with `N ≤ m ≤ (N+2)³`:
`(n+2)^(K·(kOf N + 1)) ≤ expLen m`. -/
theorem budget_numeric (K p : ℕ) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ n m, n ≤ N * Nat.clog 2 (N + 2) ^ p → N ≤ m →
      m ≤ (N + 2) ^ 3 → (n + 2) ^ (K * (kOf N + 1)) ≤ expLen m := by
  set A := 2 * K * (p + 2) with hA
  set C₀ := 8 + 2 ^ (2 * A + 1) * (2 * A + 1) + 4 * A with hC₀
  refine ⟨2 ^ C₀, fun N hN n m hn hNm hm => ?_⟩
  set c := Nat.clog 2 N with hc
  have hcC : C₀ ≤ c := clog_ge_of_ge hN
  have hc8 : 8 ≤ c := by omega
  have h256 : 2 ^ 8 ≤ 2 ^ C₀ := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hN2 : 256 ≤ N := by norm_num at h256; omega
  -- (F1) N ≤ 2^c, 2^(c-1) < N
  have hF1 : N ≤ 2 ^ c := Nat.le_pow_clog (by norm_num) N
  have hpred : 2 ^ (c - 1) < N := Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
  -- c² ≤ N
  have hcc : c * c ≤ N := le_trans (sq_le_two_pow_pred c (by omega)) hpred.le
  -- (F2) clog (N+2) ≤ c + 1
  have hF2 : Nat.clog 2 (N + 2) ≤ c + 1 := by
    apply Nat.clog_le_of_le_pow
    rw [pow_succ]; omega
  -- (F3) n + 2 ≤ 2 ^ (c*(p+1)+1)
  have hc1 : c + 1 ≤ 2 ^ c := Nat.lt_two_pow_self
  have hF3 : n + 2 ≤ 2 ^ (c * (p + 1) + 1) := by
    have h1 : Nat.clog 2 (N + 2) ^ p ≤ (2 ^ c) ^ p :=
      Nat.pow_le_pow_left (le_trans hF2 hc1) p
    have h2 : n ≤ 2 ^ c * (2 ^ c) ^ p := le_trans hn (Nat.mul_le_mul hF1 h1)
    have h3 : 2 ^ c * (2 ^ c) ^ p = 2 ^ (c * (p + 1)) := by
      rw [← pow_mul, ← pow_add]; congr 1; ring
    have h4 : 2 ≤ 2 ^ (c * (p + 1)) := by
      have : 1 ≤ c * (p + 1) := by nlinarith
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (c * (p + 1)) := Nat.pow_le_pow_right (by norm_num) this
    rw [pow_succ]; omega
  -- exponent bound: (c(p+1)+1) * K * (kOf N + 1) ≤ A * (N / c)
  have hk : kOf N = N / (c * c) := by unfold kOf; rw [← hc, sq]
  have hck : c * (N / (c * c)) ≤ N / c := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    calc c * (N / (c * c)) * c = N / (c * c) * (c * c) := by ring
      _ ≤ N := Nat.div_mul_le_self N (c * c)
  have hcN : c ≤ N / c := by
    rw [Nat.le_div_iff_mul_le (by omega)]; exact hcc
  have hexp : (c * (p + 1) + 1) * (K * (kOf N + 1)) ≤ A * (N / c) := by
    rw [hk]
    have h1 : c * (p + 1) + 1 ≤ (p + 2) * c := by nlinarith
    calc (c * (p + 1) + 1) * (K * (N / (c * c) + 1))
        ≤ ((p + 2) * c) * (K * (N / (c * c) + 1)) := Nat.mul_le_mul_right _ h1
      _ = K * (p + 2) * (c * (N / (c * c)) + c) := by ring
      _ ≤ K * (p + 2) * (N / c + N / c) := Nat.mul_le_mul_left _ (by omega)
      _ = A * (N / c) := by rw [hA]; ring
  -- (F5) A * (N / c) ≤ m / llog m
  have hmpos : 3 ≤ m := by omega
  have hclogm : Nat.clog 2 m ≤ 3 * c + 3 := by
    apply Nat.clog_le_of_le_pow
    calc m ≤ (N + 2) ^ 3 := hm
      _ ≤ (2 ^ (c + 1)) ^ 3 := Nat.pow_le_pow_left (by rw [pow_succ]; omega) 3
      _ = 2 ^ (3 * c + 3) := by rw [← pow_mul]; congr 1; ring
  set L := Nat.clog 2 (3 * c + 3) with hL
  have hllog : llog m ≤ L := Nat.clog_mono_right 2 hclogm
  have hllog1 : 1 ≤ llog m := by
    unfold llog
    have h2 : 2 ≤ Nat.clog 2 m := by
      have := clog_ge_of_ge (C := 2) (N := m) (by
        have : 2 ^ 2 ≤ 2 ^ C₀ := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega)
      exact this
    exact Nat.succ_le_of_lt (Nat.clog_pos (by norm_num) (by omega))
  -- A * L ≤ c
  have hAL : A * L ≤ c := by
    have h1 : L ≤ Nat.clog 2 c + 2 := clog_three_le c (by omega)
    have h2 : 2 * A * Nat.clog 2 c ≤ c := by
      have := mul_clog_le (2 * A) c (by omega)
      simpa [Nat.mul_assoc] using this
    have h3 : 2 ≤ Nat.clog 2 c := clog_ge_of_ge (C := 2) (by omega)
    have h4 : 4 * A ≤ c := by omega
    calc A * L ≤ A * (Nat.clog 2 c + 2) := Nat.mul_le_mul_left _ h1
      _ ≤ 2 * A * Nat.clog 2 c := by nlinarith
      _ ≤ c := h2
  have hF5 : A * (N / c) ≤ m / llog m := by
    rcases Nat.eq_zero_or_pos A with hA0 | hApos
    · rw [hA0]; simp
    have hL1 : 1 ≤ L := le_trans hllog1 hllog
    have h1 : N / c ≤ N / (A * L) := Nat.div_le_div_left hAL (by positivity)
    have h2 : A * (N / (A * L)) ≤ N / L := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      calc A * (N / (A * L)) * L = N / (A * L) * (A * L) := by ring
        _ ≤ N := Nat.div_mul_le_self N (A * L)
    have h3 : N / L ≤ m / L := Nat.div_le_div_right hNm
    have h4 : m / L ≤ m / llog m := Nat.div_le_div_left hllog (by omega)
    calc A * (N / c) ≤ A * (N / (A * L)) := Nat.mul_le_mul_left _ h1
      _ ≤ N / L := h2
      _ ≤ m / L := h3
      _ ≤ m / llog m := h4
  -- assemble
  calc (n + 2) ^ (K * (kOf N + 1)) ≤ (2 ^ (c * (p + 1) + 1)) ^ (K * (kOf N + 1)) :=
        Nat.pow_le_pow_left hF3 _
    _ = 2 ^ ((c * (p + 1) + 1) * (K * (kOf N + 1))) := by rw [← pow_mul]
    _ ≤ 2 ^ (m / llog m) :=
        Nat.pow_le_pow_right (by norm_num) (le_trans hexp hF5)
    _ = expLen m := rfl

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

theorem encode_length_ge (f : EncodedCNF.Formula) : f.variables ≤ (EncodedCNF.encode f).length := by
  simp only [EncodedCNF.encode, EncodedGraph.unary, List.length_append, List.length_replicate]
  omega

/-- **The reduction's random bits fit the effective tape.** For every density `cs` there is
`N₀` such that for every sparse valid `Φ` with `N ≥ N₀`, the selected T24 experiment at
`k = kOf N` uses at most `expLen |encode Φ|` random bits. -/
theorem reduction_bits_fit (cs : ℕ) :
    ∃ N₀ : ℕ, ∀ Φ : ValidFormula, Φ.val.clauses.length ≤ cs * Φ.val.variables →
      N₀ ≤ Φ.val.variables →
      (TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
        (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
        B.degreeBound (sourceGap D B) (kOf Φ.val.variables)).inputBits ≤
      expLen (EncodedCNF.encode Φ.val).length := by
  obtain ⟨N₁, hN₁⟩ := budget_numeric 160 (D.sizeExponent + 2)
  refine ⟨max N₁ (max 36 (max (28 * cs + 9)
    (2 ^ (2 ^ (D.sizeExponent + 1) * Paper2.Unit4Shell.T10Size.t45C D B cs)))), ?_⟩
  intro Φ hsp hN
  have h1 : N₁ ≤ Φ.val.variables := le_trans (le_max_left _ _) hN
  have h2 : 36 ≤ Φ.val.variables := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have h3 : 28 * cs + 9 ≤ Φ.val.variables :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have h4 : 2 ^ (2 ^ (D.sizeExponent + 1) * Paper2.Unit4Shell.T10Size.t45C D B cs) ≤
      Φ.val.variables :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hk1 : 1 ≤ kOf Φ.val.variables := Paper2.Unit4Shell.AsymptoticsExplicit.kOf_pos _ h2
  have hbits := Paper2.Unit4Shell.RandomBits.inputBits_le_resource D B Φ (kOf Φ.val.variables) hk1
  have hsize := Paper2.Unit4Shell.T10Size.t45_shell_form D B cs Φ hsp h4
  have hlen := Paper2.Unit4Shell.T24RuntimeComposed.encode_length_cube cs Φ hsp h3
  have hge := encode_length_ge Φ.val
  have hfit := hN₁ Φ.val.variables h1 ((t10Graph D B Φ).vertices)
    (EncodedCNF.encode Φ.val).length hsize hge (by omega)
  exact le_trans hbits hfit

end Paper2.AEth

end

#print axioms Paper2.AEth.budget_numeric
#print axioms Paper2.AEth.encode_length_ge
#print axioms Paper2.AEth.reduction_bits_fit
