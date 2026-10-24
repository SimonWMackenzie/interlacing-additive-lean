import Paper2.A4Kof
import EthInapproximability.CurrentPaper.MatrixUnaryPower

/-!
# Paper A (lock v12), lane `owner:a-eth-1`, segment 1a: an effective subexponential tape length

Lock v12 `sections/06-reduction.tex:95-102` (`def:reth`): "Randomized sparse ETH asserts that, for
some fixed constant $c_s$, there is no bounded-error randomized algorithm deciding $3$-SAT on $N$
variables and at most $c_sN$ clauses in worst-case time $2^{o(N)}$." ROOT DECISION R19
(`MODEL_REPAIR_2026-09-27.md`): "The ETH model also needs an explicitly effective, potentially
subexponential tape budget". Author decisions D-A1 (a fixed length before the input, no
advice) and D-A6 (the ETH shape with an explicit polynomial factor).

This module supplies the effective length used by the ETH carrier `SubexpTape.Algorithm`:
* `Subexp g`: for every `ε > 0` eventually `g m ≤ C·⌈2^{εm}⌉·(m+1)^d`;
* ONE fixed bit machine `lenMachine` that, from the unary word `1^m`, prints the unary word
  `1^(expLen m)`, `expLen m = 2^(m / ⌈log₂⌈log₂ m⌉⌉)`, within the explicit clock `lenTime m`
  (`lenMachine_outputs`), assembled only from admitted physical unary machines:
  `KofLoops.WrapDup`, `PairMap` of `ExactParameterMachineLog ∘ ExactParameterMachineLog`,
  `KofLoops.Swap`, `KofFront.DivFloor`, `MatrixUnaryPower`; every handoff is charged by the
  admitted `composition_outputsWithin`;
* `expLen_subexp`, `lenTime_subexp`: both are subexponential;
* `expLen_ge`: for every constant `K`, eventually `2^(K·⌊m / ⌈log₂ m⌉⌋) ≤ expLen m` (the tape is
  large enough for any `2^{O(m / log m)}` random-bit demand).

No ledger row is closed.
-/

noncomputable section

namespace Paper2.AEth

open EthInapproximability.CurrentPaper
open Paper2.Unit4Shell
open Paper2.Unit4Shell.KofLoops
open Paper2.Unit4Shell.KofFront

/-- Subexponential growth in the argument `m` (with an explicit polynomial factor):
for every `ε > 0` there are `C d m₀` with `g m ≤ C·⌈2^{εm}⌉·(m+1)^d` for `m ≥ m₀`. -/
def Subexp (g : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C d m₀ : ℕ, ∀ m, m₀ ≤ m →
    g m ≤ C * ⌈(2 : ℝ) ^ (ε * m)⌉₊ * (m + 1) ^ d

/-- The iterated ceiling logarithm `⌈log₂⌈log₂ m⌉⌉`. -/
def llog (m : ℕ) : ℕ := Nat.clog 2 (Nat.clog 2 m)

/-- The exponent of the effective tape length. -/
def expExp (m : ℕ) : ℕ := m / llog m

/-- **The effective subexponential tape length** `2^(m / ⌈log₂⌈log₂ m⌉⌉)`. -/
def expLen (m : ℕ) : ℕ := 2 ^ expExp m

/-- `1^m ↦ 1^(⌈log₂⌈log₂ m⌉⌉)`. -/
def loglogMachine : BitMachine.Machine :=
  BitMachineComposition.composition ExactParameterMachineLog.machine
    ExactParameterMachineLog.machine

/-- **THE fixed length machine** `1^m ↦ 1^(expLen m)`. -/
def lenMachine : BitMachine.Machine :=
  BitMachineComposition.composition WrapDup.machine
    (BitMachineComposition.composition (Paper2.Unit4Shell.PairMap.machine loglogMachine)
      (BitMachineComposition.composition Swap.machine
        (BitMachineComposition.composition DivFloor.machine MatrixUnaryPower.machine)))

/-- The explicit constant of the polynomial part of the length machine's clock. -/
def BL : ℕ := 2 * UnaryBinaryEncoding.coefficient + 2000

/-- The explicit clock of the length machine. -/
def lenTime (m : ℕ) : ℕ := BL * (m + 1) ^ 2 + 20 * expLen m

theorem llog_le (m : ℕ) : llog m ≤ m :=
  le_trans (clog_le_self _) (clog_le_self m)

theorem expExp_le (m : ℕ) : expExp m ≤ m := Nat.div_le_self m (llog m)

theorem loglog_outputs (m : ℕ) :
    loglogMachine.OutputsWithin (List.replicate m true) (List.replicate (llog m) true)
      ((UnaryBinaryEncoding.coefficient + 6) * (m + 1) ^ 2 + 2 * Nat.clog 2 m + 2 +
        (UnaryBinaryEncoding.coefficient + 6) * (Nat.clog 2 m + 1) ^ 2) := by
  have h := BitMachineComposition.composition_outputsWithin ExactParameterMachineLog.machine
    ExactParameterMachineLog.machine (ExactParameterMachineLog.outputs m)
    (ExactParameterMachineLog.outputs (Nat.clog 2 m))
  simpa only [loglogMachine, llog, List.length_replicate] using h

/-- **The length machine is correct and charged.** From the unary word `1^m`, the fixed machine
`lenMachine` prints exactly `1^(expLen m)` within `lenTime m` steps. -/
theorem lenMachine_outputs (m : ℕ) :
    lenMachine.OutputsWithin (List.replicate m true) (List.replicate (expLen m) true)
      (lenTime m) := by
  set C1 := Nat.clog 2 m with hC1
  set Q := llog m with hQdef
  set F4 : List Bool := [false, false, false, false] with hF4
  have h2 := WrapDup.machine_outputs m
  have hout : WrapDup.out m = EncodedComplexity.pair (List.replicate m true)
      (EncodedComplexity.pair (List.replicate m true) F4) := by
    simp [WrapDup.out, EncodedComplexity.pair, hF4]
  rw [hout] at h2
  have h3 := Paper2.Unit4Shell.PairMap.machine_outputs (M := loglogMachine)
    (List.replicate m true) (List.replicate Q true)
    (EncodedComplexity.pair (List.replicate m true) F4) _ (loglog_outputs m)
  have h4 := Swap.machine_outputs (List.replicate Q true) (List.replicate m true) F4
  rw [← DivFloor.packedInput_eq m Q] at h4
  have h5 := DivFloor.outputs m Q
  have h6 := MatrixUnaryPower.outputs (List.replicate (m / Q) true)
  rw [List.length_replicate] at h6
  have hC := BitMachineComposition.composition_outputsWithin _ _ h2
    (BitMachineComposition.composition_outputsWithin _ _ h3
      (BitMachineComposition.composition_outputsWithin _ _ h4
        (BitMachineComposition.composition_outputsWithin _ _ h5 h6)))
  have hE : 2 ^ (m / Q) = expLen m := rfl
  rw [hE] at hC
  apply BitMachine.outputsWithin_mono _ hC
  have hin := DivFloor.packedInput_length m Q
  rw [hin]
  simp only [List.length_replicate, EncodedComplexity.pair_length, hF4, List.length_cons,
    List.length_nil]
  have hC1m : C1 ≤ m := clog_le_self m
  have hQm : Q ≤ m := llog_le m
  have hqm : m / Q ≤ m := Nat.div_le_self m Q
  have hq2 : m / Q < 2 ^ (m / Q) := Nat.lt_two_pow_self
  have hE2 : 2 ^ (m / Q) = expLen m := rfl
  rw [hE2] at hq2
  have hsq : (C1 + 1) ^ 2 ≤ (m + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hm1 : m + 1 ≤ (m + 1) ^ 2 := by nlinarith
  have hU := Nat.mul_le_mul_left (UnaryBinaryEncoding.coefficient + 6) hsq
  unfold lenTime BL
  nlinarith

/-- For `m ≥ 2^(2^K)`, `K ≤ ⌈log₂⌈log₂ m⌉⌉`. -/
theorem le_llog {K m : ℕ} (hm : 2 ^ (2 ^ K) ≤ m) : K ≤ llog m := by
  have h1 : 2 ^ K ≤ Nat.clog 2 m := by
    have := Nat.clog_mono_right 2 hm
    rwa [Nat.clog_pow 2 _ (by norm_num)] at this
  have h2 := Nat.clog_mono_right 2 h1
  rwa [Nat.clog_pow 2 _ (by norm_num)] at h2

/-- For every `ε > 0`, eventually `expLen m ≤ 2^{εm}`. -/
theorem expLen_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → (expLen m : ℝ) ≤ (2 : ℝ) ^ (ε * m) := by
  obtain ⟨K, hK⟩ := exists_nat_gt (1 / ε)
  refine ⟨2 ^ (2 ^ K), fun m hm => ?_⟩
  have hKl : K ≤ llog m := le_llog hm
  have hKpos : 0 < K := by
    have : (0 : ℝ) < 1 / ε := by positivity
    exact_mod_cast (lt_trans this hK)
  have hq : expExp m ≤ m / K := Nat.div_le_div_left hKl hKpos
  have hqR : (expExp m : ℝ) ≤ ε * m := by
    have h1 : ((m / K : ℕ) : ℝ) ≤ (m : ℝ) / K := Nat.cast_div_le
    have h2 : (m : ℝ) / K ≤ ε * m := by
      have hKR : (0 : ℝ) < K := by exact_mod_cast hKpos
      rw [div_le_iff₀ hKR]
      have h3 : 1 < ε * K := by
        have := hK
        rw [div_lt_iff₀ hε] at this
        linarith
      have hm0 : (0 : ℝ) ≤ m := by positivity
      nlinarith
    calc (expExp m : ℝ) ≤ ((m / K : ℕ) : ℝ) := by exact_mod_cast hq
      _ ≤ (m : ℝ) / K := h1
      _ ≤ ε * m := h2
  unfold expLen
  push_cast
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hqR

/-- **The effective tape length is subexponential.** -/
theorem expLen_subexp : Subexp expLen := by
  intro ε hε
  obtain ⟨m₀, hm₀⟩ := expLen_le_rpow ε hε
  refine ⟨1, 0, m₀, fun m hm => ?_⟩
  have h := hm₀ m hm
  have h2 : expLen m ≤ ⌈(2 : ℝ) ^ (ε * m)⌉₊ := by
    have := le_trans h (Nat.le_ceil _)
    exact_mod_cast this
  simpa using h2

/-- **The length machine's clock is subexponential.** -/
theorem lenTime_subexp : Subexp lenTime := by
  intro ε hε
  obtain ⟨m₀, hm₀⟩ := expLen_le_rpow ε hε
  refine ⟨BL + 20, 2, m₀, fun m hm => ?_⟩
  have h := hm₀ m hm
  have h2 : expLen m ≤ ⌈(2 : ℝ) ^ (ε * m)⌉₊ := by
    have := le_trans h (Nat.le_ceil _)
    exact_mod_cast this
  have hc1 : 1 ≤ ⌈(2 : ℝ) ^ (ε * m)⌉₊ := by
    have : (0 : ℝ) < (2 : ℝ) ^ (ε * m) := by positivity
    exact Nat.one_le_iff_ne_zero.mpr (by
      intro h0
      rw [Nat.ceil_eq_zero] at h0
      linarith)
  have hp : 1 ≤ (m + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  unfold lenTime
  generalize BL = b
  generalize ⌈(2 : ℝ) ^ (ε * m)⌉₊ = c at h2 hc1 ⊢
  generalize (m + 1) ^ 2 = P at hp ⊢
  have h3 : expLen m * 1 ≤ c * P := Nat.mul_le_mul h2 hp
  have h4 : b * P * 1 ≤ b * P * c := Nat.mul_le_mul_left _ hc1
  have e : (b + 20) * c * P = b * P * c + 20 * (c * P) := by ring
  rw [e]
  omega

theorem sq_le_two_pow' (k : ℕ) : (k + 4) * (k + 4) ≤ 2 ^ (k + 4) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have e : k + 1 + 4 = (k + 4) + 1 := by omega
    rw [e, pow_succ]
    nlinarith

theorem sq_le_two_pow (n : ℕ) (h : 4 ≤ n) : n * n ≤ 2 ^ n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  exact sq_le_two_pow' k

theorem two_le_bound (K : ℕ) : 2 ≤ 2 ^ (K + 1) * (K + 1) := by
  have h1 : 2 ≤ 2 ^ (K + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (K + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  nlinarith

/-- `K · ⌈log₂ c⌉ ≤ c` once `c ≥ 2^(K+1)·(K+1)`. -/
theorem mul_clog_le (K c : ℕ) (hc0 : 2 ^ (K + 1) * (K + 1) ≤ c) : K * Nat.clog 2 c ≤ c := by
  obtain ⟨l, hl⟩ : ∃ l, l = Nat.clog 2 c := ⟨_, rfl⟩
  rw [← hl]
  rcases Nat.eq_zero_or_pos K with hK | hK
  · simp [hK]
  have hc1 : 1 < c := by have := two_le_bound K; omega
  have hpred : 2 ^ (l - 1) < c := by rw [hl]; exact Nat.pow_pred_clog_lt_self (by norm_num) hc1
  by_cases hsmall : l ≤ 2 * K + 2
  · have h1 : K * l ≤ K * (2 * K + 2) := Nat.mul_le_mul_left _ hsmall
    have h2 : 2 * K ≤ 2 ^ (K + 1) := by
      have : K < 2 ^ K := Nat.lt_two_pow_self
      rw [pow_succ]; omega
    have h3 : K * (2 * K + 2) ≤ 2 ^ (K + 1) * (K + 1) := by nlinarith
    omega
  · have hl4 : 4 ≤ l := by omega
    have hsq := sq_le_two_pow l hl4
    have h2K : 2 * (K * l) ≤ l * l := by nlinarith
    have hpow : 2 ^ l = 2 * 2 ^ (l - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega

/-- **The tape is large enough for every `2^{O(m / log m)}` demand**: for every constant `K`,
eventually `2^(K·⌊m / ⌈log₂ m⌉⌋) ≤ expLen m`. -/
theorem expLen_ge (K : ℕ) :
    ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → 2 ^ (K * (m / Nat.clog 2 m)) ≤ expLen m := by
  refine ⟨2 ^ (2 ^ (K + 1) * (K + 1)), fun m hm => ?_⟩
  unfold expLen expExp
  apply Nat.pow_le_pow_right (by norm_num)
  set c := Nat.clog 2 m with hc
  have hlc : llog m = Nat.clog 2 c := rfl
  have hc0 : 2 ^ (K + 1) * (K + 1) ≤ c := by
    have := Nat.clog_mono_right 2 hm
    rwa [Nat.clog_pow 2 _ (by norm_num)] at this
  have hKl : K * llog m ≤ c := by rw [hlc]; exact mul_clog_le K c hc0
  have hc1 : 1 < c := by have := two_le_bound K; omega
  have hlpos : 0 < llog m := by rw [hlc]; exact Nat.clog_pos (by norm_num) hc1
  rw [Nat.le_div_iff_mul_le hlpos]
  calc K * (m / c) * llog m = (m / c) * (K * llog m) := by ring
    _ ≤ (m / c) * c := Nat.mul_le_mul_left _ hKl
    _ ≤ m := Nat.div_mul_le_self m c

end Paper2.AEth

end

#print axioms Paper2.AEth.lenMachine_outputs
#print axioms Paper2.AEth.expLen_subexp
#print axioms Paper2.AEth.lenTime_subexp
#print axioms Paper2.AEth.expLen_ge
