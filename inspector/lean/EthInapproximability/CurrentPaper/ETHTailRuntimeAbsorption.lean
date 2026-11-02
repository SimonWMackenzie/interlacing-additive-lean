import EthInapproximability.CurrentPaper.ETHTailGrowth

/-!
# Fixed-coefficient absorption in the ETH exponent slack

The existing growth theorem absorbs any fixed polynomial in the common table
length. This lemma also absorbs a fixed real coefficient, using a strictly
intermediate exponent. It is numerical only: it does not assert an actual
source, materialization, list-map, or SAT-machine runtime.
-/

namespace EthInapproximability.CurrentPaper.ETHTailRuntimeAbsorption

open Filter

theorem coefficient_source_times_table_eventually (c A d B C : ℕ)
    (ε δ : ℝ) (hεδ : ε < δ) :
    ∀ᶠ n : ℕ in atTop,
      (C : ℝ) * (2 : ℝ) ^ (ε * n) *
        ((FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n : ℕ) : ℝ) ^ B ≤
          (2 : ℝ) ^ (δ * n) := by
  let θ := (ε + δ) / 2
  have hεθ : ε < θ := by dsimp [θ]; linarith
  have hθδ : θ < δ := by dsimp [θ]; linarith
  have htable := ETHTailGrowth.source_times_table_eventually c A d B ε θ hεθ
  have hbase : 1 < (2 : ℝ) ^ (δ - θ) :=
    Real.one_lt_rpow (by norm_num) (by linarith)
  have hcoef : ∀ᶠ n : ℕ in atTop,
      (C : ℝ) ≤ (2 : ℝ) ^ ((δ - θ) * n) := by
    have ht := (tendsto_pow_atTop_atTop_of_one_lt hbase).eventually_ge_atTop (C : ℝ)
    filter_upwards [ht] with n hn
    simpa only [Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2), Nat.cast_ofNat]
      using hn
  filter_upwards [htable, hcoef] with n ht hc
  have hnonneg : 0 ≤ (2 : ℝ) ^ (θ * n) := Real.rpow_nonneg (by norm_num) _
  calc
    (C : ℝ) * (2 : ℝ) ^ (ε * n) *
        ((FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n : ℕ) : ℝ) ^ B
        = (C : ℝ) * ((2 : ℝ) ^ (ε * n) *
          ((FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n : ℕ) : ℝ) ^ B) := by
            ring
    _ ≤ (C : ℝ) * (2 : ℝ) ^ (θ * n) :=
      mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg _)
    _ ≤ (2 : ℝ) ^ ((δ - θ) * n) * (2 : ℝ) ^ (θ * n) :=
      mul_le_mul_of_nonneg_right hc hnonneg
    _ = (2 : ℝ) ^ (δ * n) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

/-- A fixed multiplier and the source-list ceiling fit into the same
spare exponent. The output is a natural transition budget of exactly the
form used by `EncodedETHTail.TimeBound`, before its input-length factor. -/
theorem ceiling_source_times_table_eventually (c A d B C : ℕ)
    (ε δ : ℝ) (hε : 0 ≤ ε) (hεδ : ε < δ) :
    ∀ᶠ n : ℕ in atTop,
      C * ⌈(2 : ℝ) ^ (ε * n)⌉₊ *
        FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n ^ B ≤
          ⌈(2 : ℝ) ^ (δ * n)⌉₊ := by
  filter_upwards [coefficient_source_times_table_eventually c A d B (2 * C) ε δ hεδ]
    with n hn
  have hpow : 1 ≤ (2 : ℝ) ^ (ε * n) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hceil : (⌈(2 : ℝ) ^ (ε * n)⌉₊ : ℝ) ≤
      2 * (2 : ℝ) ^ (ε * n) :=
    Nat.ceil_le_two_mul (by linarith)
  have hnat : (C * ⌈(2 : ℝ) ^ (ε * n)⌉₊ *
      FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n ^ B : ℝ) ≤
      (⌈(2 : ℝ) ^ (δ * n)⌉₊ : ℝ) := by
    calc
      _ = (C : ℝ) * (⌈(2 : ℝ) ^ (ε * n)⌉₊ : ℝ) *
          ((FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n : ℕ) : ℝ) ^ B := by
            ring
      _ ≤ (C : ℝ) * (2 * (2 : ℝ) ^ (ε * n)) *
          ((FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n : ℕ) : ℝ) ^ B := by
            gcongr
      _ = ((2 * C : ℕ) : ℝ) * (2 : ℝ) ^ (ε * n) *
          ((FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n : ℕ) : ℝ) ^ B := by
            push_cast; ring
      _ ≤ (2 : ℝ) ^ (δ * n) := hn
      _ ≤ (⌈(2 : ℝ) ^ (δ * n)⌉₊ : ℝ) := Nat.le_ceil _
  exact_mod_cast hnat

theorem solver_budget_eventually (c A d B C D : ℕ)
    (ε δ : ℝ) (hε : 0 ≤ ε) (hεδ : ε < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ input : List Bool,
      EncodedETHTail.variableCount input = n →
      C * ⌈(2 : ℝ) ^ (ε * n)⌉₊ *
          FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n ^ B *
            (input.length + 1) ^ D ≤
        EncodedETHTail.TimeBound δ 1 D input := by
  filter_upwards [ceiling_source_times_table_eventually c A d B C ε δ hε hεδ]
    with n hn input hvar
  have h := Nat.mul_le_mul_right ((input.length + 1) ^ D) hn
  simpa only [EncodedETHTail.TimeBound, hvar, one_mul] using h

/-- The finitely many exceptional parameter values can be charged to one
fixed multiplier. This is purely a bound on a stated numerical expression;
it is not a construction of the small-input SAT solver. -/
theorem ceiling_source_times_table_global (c A d B C : ℕ)
    (ε δ : ℝ) (hε : 0 ≤ ε) (hεδ : ε < δ) :
    ∃ K : ℕ, ∀ n : ℕ,
      C * ⌈(2 : ℝ) ^ (ε * n)⌉₊ *
          FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n ^ B ≤
        K * ⌈(2 : ℝ) ^ (δ * n)⌉₊ := by
  obtain ⟨N, hN⟩ := (eventually_atTop.1
    (ceiling_source_times_table_eventually c A d B C ε δ hε hεδ))
  let f (n : ℕ) := C * ⌈(2 : ℝ) ^ (ε * n)⌉₊ *
    FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n ^ B
  let K := 1 + ∑ n ∈ Finset.range N, f n
  refine ⟨K, ?_⟩
  intro n
  have hδ : 1 ≤ ⌈(2 : ℝ) ^ (δ * n)⌉₊ := by
    have hp : (1 : ℝ) ≤ (2 : ℝ) ^ (δ * n) :=
      Real.one_le_rpow (by norm_num) (mul_nonneg (by linarith) (Nat.cast_nonneg _))
    have hc : (1 : ℝ) ≤ (⌈(2 : ℝ) ^ (δ * n)⌉₊ : ℝ) :=
      hp.trans (Nat.le_ceil _)
    exact_mod_cast hc
  by_cases hn : n < N
  · have hs : f n ≤ ∑ i ∈ Finset.range N, f i :=
      Finset.single_le_sum (fun i hi => Nat.zero_le _) (Finset.mem_range.mpr hn)
    change f n ≤ K * ⌈(2 : ℝ) ^ (δ * n)⌉₊
    have hfK : f n ≤ K := by dsimp [K]; omega
    exact hfK.trans (by simpa only [mul_one] using Nat.mul_le_mul_left K hδ)
  · have hl : f n ≤ ⌈(2 : ℝ) ^ (δ * n)⌉₊ := hN n (by omega)
    change f n ≤ K * ⌈(2 : ℝ) ^ (δ * n)⌉₊
    have hK : 1 ≤ K := by dsimp [K]; omega
    exact hl.trans (by simpa only [one_mul] using
      Nat.mul_le_mul_right ⌈(2 : ℝ) ^ (δ * n)⌉₊ hK)

theorem solver_budget_global (c A d B C D : ℕ)
    (ε δ : ℝ) (hε : 0 ≤ ε) (hεδ : ε < δ) :
    ∃ K : ℕ, ∀ input : List Bool,
      C * ⌈(2 : ℝ) ^ (ε * EncodedETHTail.variableCount input)⌉₊ *
          FinalPadding.tableSize
            (ETHTailGrowth.repetitions c A d)
            (EncodedETHTail.variableCount input) ^ B *
            (input.length + 1) ^ D ≤
        EncodedETHTail.TimeBound δ K D input := by
  obtain ⟨K, hK⟩ := ceiling_source_times_table_global c A d B C ε δ hε hεδ
  refine ⟨K, ?_⟩
  intro input
  have h := Nat.mul_le_mul_right ((input.length + 1) ^ D)
    (hK (EncodedETHTail.variableCount input))
  simpa only [EncodedETHTail.TimeBound] using h

end EthInapproximability.CurrentPaper.ETHTailRuntimeAbsorption
