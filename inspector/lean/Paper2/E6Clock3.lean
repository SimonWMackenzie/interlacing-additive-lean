import Paper2.E3Inner
-- a-eth-owner-6 copy of frozen a-eth-owner-3/E3Clock.lean (SHA-256 2a1312fa77f54f90b53fb49b6c30bb6a582fc452fee1c8553cac0cdb3ffcefdd); import lines renamed only; `import ETape` dropped, `Paper2.AEth2.ceil_pow_le` -> `Paper2.AEth6.ceil_pow_le`.

/-! a-eth-owner-6 (G1): `ceil_pow_le` re-proved here (statement and proof text verbatim from frozen a-eth-owner-2
`ETape.lean:46-68`, SHA-256 of that file recorded in RECEIPT.md) under the NEW name `Paper2.AEth6.ceil_pow_le`,
so this module does not import `ETape`. -/
theorem Paper2.AEth6.ceil_pow_le {a b x : ℝ} (E : ℕ) (ha : 0 ≤ a) (hx : 0 ≤ x) (hab : a * E ≤ b) :
    ⌈(2 : ℝ) ^ (a * x)⌉₊ ^ E ≤ 2 ^ E * ⌈(2 : ℝ) ^ (b * x)⌉₊ := by
  have hy1 : (1 : ℝ) ≤ (2 : ℝ) ^ (a * x) := Real.one_le_rpow (by norm_num) (mul_nonneg ha hx)
  have hc : (⌈(2 : ℝ) ^ (a * x)⌉₊ : ℝ) ≤ 2 * (2 : ℝ) ^ (a * x) :=
    le_of_lt (Nat.ceil_lt_two_mul (by linarith))
  have hpow : ((⌈(2 : ℝ) ^ (a * x)⌉₊ : ℝ)) ^ E ≤ (2 * (2 : ℝ) ^ (a * x)) ^ E :=
    pow_le_pow_left₀ (by positivity) hc E
  have he : ((2 : ℝ) ^ (a * x)) ^ E = (2 : ℝ) ^ (a * x * E) :=
    (Real.rpow_mul_natCast (by norm_num) _ _).symm
  have hle : (2 : ℝ) ^ (a * x * E) ≤ (2 : ℝ) ^ (b * x) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have : a * x * E = (a * E) * x := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hab hx
  have hceil : (2 : ℝ) ^ (b * x) ≤ (⌈(2 : ℝ) ^ (b * x)⌉₊ : ℝ) := Nat.le_ceil _
  have key : ((⌈(2 : ℝ) ^ (a * x)⌉₊ ^ E : ℕ) : ℝ) ≤ ((2 ^ E * ⌈(2 : ℝ) ^ (b * x)⌉₊ : ℕ) : ℝ) := by
    push_cast
    calc ((⌈(2 : ℝ) ^ (a * x)⌉₊ : ℝ)) ^ E ≤ (2 * (2 : ℝ) ^ (a * x)) ^ E := hpow
      _ = 2 ^ E * ((2 : ℝ) ^ (a * x)) ^ E := by rw [mul_pow]
      _ = 2 ^ E * (2 : ℝ) ^ (a * x * E) := by rw [he]
      _ ≤ 2 ^ E * (⌈(2 : ℝ) ^ (b * x)⌉₊ : ℝ) :=
          mul_le_mul_of_nonneg_left (le_trans hle hceil) (by positivity)
  exact_mod_cast key


/-!
# Paper A (lock v12), lane `owner:a-eth-3`, segment 1 (obstacle B2): the D-A6 clock of the front cut

Author decision D-A6 (the ETH clock `2^(εN)·(|input|+1)^O(1)` for every `ε > 0` eventually) and ROOT
DECISION R20. The front cut `frontCut` of `E3Inner` runs, on `pair (encode F) t` for EVERY tape `t`,
within `frontTime F`, a function of `X = |encode F|` and `N = F.variables` only. Here:

* `frontTime_le_G`: `frontTime F ≤ G (X + expLen N)` for ONE fixed polynomial expression `G`
  (monotonicity only; `lenTime N = BL(N+1)² + 20·expLen N`, `N ≤ X`);
* `frontTime_budget`: for every `ε > 0` there are `C d N₀` with
  `frontTime F ≤ C·⌈2^(εN)⌉·(X+1)^d` for EVERY CNF `F` with `N ≥ N₀` (valid, sparse or not):
  the inner machine and the cut are inside the D-A6 budget.

No ledger row is closed.
-/

noncomputable section

namespace Paper2.AEth3

open EthInapproximability.CurrentPaper

/-- The front-cut clock as a function of `X`, `N`, `U` (with `U = expLen N`). -/
def innerOf (pb X N U : ℕ) : ℕ :=
  5 * X + 8 + 2 * (4 * X + 2) + 2 +
    ((2 * X + (2 * N + 3 + 2 * N + 2 + (Paper2.AEth.BL * (N + 1) ^ 2 + 20 * U)) + 2 * U + 6) +
      2 * (2 * U + 2 * X + 2) + 2 + 3 * (2 * U + 2 * X + 2 + 1)) + 0 * pb

def frontOf (pb X N U : ℕ) : ℕ :=
  ((2 * X + 1) + (X + 1) + innerOf pb X N U + (X + innerOf pb X N U * pb + 1) + 1 +
    (1 + 1) * (3 + 1 * (X + innerOf pb X N U * pb + 1) ^ 1 *
      (3 * (X + innerOf pb X N U * pb) + 6)) +
    (1 * (X + innerOf pb X N U * pb + 1) ^ 1 + 1) +
    (1 * (X + innerOf pb X N U * pb + 1) ^ 1 + 1) + 1 +
    (X + innerOf pb X N U * pb + 1) + 1) +
  2 * (2 * (2 * X + 2 * U + 2) + 1 + (2 * X + 2 * U + 3)) + 2 +
  (2 * (2 * X + 2 * U + 2) + (2 * X + 3) + 2 * X + 6)

theorem innerTime_eq (F : EncodedCNF.Formula) :
    innerTime F = innerOf innerMachine.pushBound (EncodedCNF.encode F).length F.variables
      (Paper2.AEth.expLen F.variables) := by
  simp only [innerTime, innerOf, muTime, Paper2.AEth.lenTime]
  ring

theorem frontTime_eq (F : EncodedCNF.Formula) :
    frontTime F = frontOf innerMachine.pushBound (EncodedCNF.encode F).length F.variables
      (Paper2.AEth.expLen F.variables) := by
  simp only [frontTime, frontOf, Paper2.AEth2.Cut.cutTimeG, fOut_length, cutLen_eq, innerTime_eq]

theorem innerOf_mono {pb X N U X' N' U' : ℕ} (hX : X ≤ X') (hN : N ≤ N') (hU : U ≤ U') :
    innerOf pb X N U ≤ innerOf pb X' N' U' := by
  unfold innerOf
  gcongr

theorem frontOf_mono {pb X N U X' N' U' : ℕ} (hX : X ≤ X') (hN : N ≤ N') (hU : U ≤ U') :
    frontOf pb X N U ≤ frontOf pb X' N' U' := by
  have hI := innerOf_mono (pb := pb) hX hN hU
  unfold frontOf
  gcongr

/-- ONE fixed polynomial bound of the front-cut clock. -/
def G (S : ℕ) : ℕ := frontOf innerMachine.pushBound S S S

theorem frontTime_le_G (F : EncodedCNF.Formula) :
    frontTime F ≤ G ((EncodedCNF.encode F).length + Paper2.AEth.expLen F.variables) := by
  rw [frontTime_eq, G]
  have hN := SourceOriginalVariableCapture.original_n_le_input F
  exact frontOf_mono (by omega) (by omega) (by omega)

set_option maxRecDepth 20000 in
theorem G_poly : Paper2.Unit4Shell.Poly.PolyIn id G := by
  unfold G frontOf innerOf
  repeat (first
    | exact Paper2.Unit4Shell.Poly.self
    | exact Paper2.Unit4Shell.Poly.const _
    | apply Paper2.Unit4Shell.Poly.add
    | apply Paper2.Unit4Shell.Poly.mul
    | apply Paper2.Unit4Shell.Poly.pow)

theorem one_le_expLen (N : ℕ) : 1 ≤ Paper2.AEth.expLen N := Nat.one_le_two_pow

/-- **The front cut is inside the D-A6 budget.** For every `ε > 0` there are `C d N₀` such that
for EVERY CNF `F` with `F.variables ≥ N₀`:
`frontTime F ≤ C·⌈2^(ε·N)⌉·(|encode F|+1)^d`. -/
theorem frontTime_budget (ε : ℝ) (hε : 0 < ε) :
    ∃ C d N₀ : ℕ, ∀ F : EncodedCNF.Formula, N₀ ≤ F.variables →
      frontTime F ≤ C * ⌈(2 : ℝ) ^ (ε * F.variables)⌉₊ * ((EncodedCNF.encode F).length + 1) ^ d := by
  obtain ⟨C, E, hG⟩ := G_poly
  set a : ℝ := ε / (E + 1) with ha
  have ha0 : 0 < a := by positivity
  have haE : a * E ≤ ε := by
    rw [ha, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨m₀, hm₀⟩ := Paper2.AEth.expLen_le_rpow a ha0
  refine ⟨C * 2 ^ E * 2 ^ E, E, m₀, fun F hF => ?_⟩
  set X := (EncodedCNF.encode F).length with hX
  set N := F.variables with hN
  set U := Paper2.AEth.expLen N with hU
  have hU1 : 1 ≤ U := one_le_expLen N
  have h1 : frontTime F ≤ C * (X + U + 1) ^ E := (frontTime_le_G F).trans (hG _)
  have h2 : X + U + 1 ≤ (X + 1) * (2 * U) := by nlinarith
  have h3 : (X + U + 1) ^ E ≤ (X + 1) ^ E * (2 ^ E * U ^ E) := by
    calc (X + U + 1) ^ E ≤ ((X + 1) * (2 * U)) ^ E := Nat.pow_le_pow_left h2 E
      _ = (X + 1) ^ E * (2 ^ E * U ^ E) := by rw [mul_pow, mul_pow]
  have hUc : U ≤ ⌈(2 : ℝ) ^ (a * N)⌉₊ := by
    have hr : (U : ℝ) ≤ (2 : ℝ) ^ (a * N) := hm₀ N hF
    exact_mod_cast hr.trans (Nat.le_ceil _)
  have h4 : U ^ E ≤ 2 ^ E * ⌈(2 : ℝ) ^ (ε * N)⌉₊ :=
    (Nat.pow_le_pow_left hUc E).trans
      (Paper2.AEth6.ceil_pow_le E ha0.le (Nat.cast_nonneg N) haE)
  calc frontTime F ≤ C * (X + U + 1) ^ E := h1
    _ ≤ C * ((X + 1) ^ E * (2 ^ E * U ^ E)) := Nat.mul_le_mul_left _ h3
    _ ≤ C * ((X + 1) ^ E * (2 ^ E * (2 ^ E * ⌈(2 : ℝ) ^ (ε * N)⌉₊))) := by gcongr
    _ = C * 2 ^ E * 2 ^ E * ⌈(2 : ℝ) ^ (ε * N)⌉₊ * (X + 1) ^ E := by ring

end Paper2.AEth3

#print axioms Paper2.AEth3.frontTime_eq
#print axioms Paper2.AEth3.frontTime_le_G
#print axioms Paper2.AEth3.G_poly
#print axioms Paper2.AEth3.frontTime_budget
