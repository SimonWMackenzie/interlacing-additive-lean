import Mathlib
import EthBridge.Defs

/-! # EthBridge pure-arithmetic layer (Tranche E0)

Lemma SIGNATURES ONLY (all `sorry`) for the note's finite/analytic inequalities,
drafted for faithfulness sign-off BEFORE any proof effort:

* `rowThreshold_ceil_halving`  — note (1)
* `margin`                     — note (2)/(3)
* `Bdef_ge_log2`               — note (5)
* `Bdef_antitone`              — note (6)
* `Bdef_ceil_halving`          — note (7)
* `Bdef_three`                 — note (8)
* `cExcess_ceil_halving`       — note (17)
* `state_defect_iff_density`   — the density↔defect conversion (plan step 2)

Fidelity is checked to the note's LITERAL text: ceilings (`⌈·⌉₊`), strict vs
non-strict, real-valued powers, and the `q = ⌈p/2⌉` nat = `(p+1)/2` identity.
-/

namespace EthBridge

/-! ## Note (1): row-threshold ceiling halving -/

/-- **Note (1).** `A_(a-1) ≤ ⌈A_a / 2⌉` for `a ≥ 1`.

Derivation (note §2): `A_a ≥ m·2^a·x`, so `⌈A_a/2⌉ ≥ ⌈m·2^(a-1)·x⌉ = A_(a-1)`.
`⌈A_a/2⌉` is the Nat-ceiling of the real `A_a/2` (equivalently the Nat quantity
`(A_a+1)/2`). JUDGE FLAG: the note fixes `0 < x ≤ 1/4` globally, but this
inequality needs no hypothesis on `x` (pure ceiling monotonicity); only `1 ≤ a`
is required. -/
theorem rowThreshold_ceil_halving (m : ℕ) (x : ℝ) (a : ℕ) (ha : 1 ≤ a) :
    rowThreshold m x (a - 1) ≤ ⌈(rowThreshold m x a : ℝ) / 2⌉₊ := by
  cases a with
  | zero => omega
  | succ b =>
      simp only [Nat.succ_sub_one, rowThreshold]
      apply Nat.ceil_le_ceil
      by_cases hx : 0 ≤ x
      · have hceil :
            (m : ℝ) * (2 : ℝ) ^ (b + 1) * x ≤
              (⌈(m : ℝ) * (2 : ℝ) ^ (b + 1) * x⌉₊ : ℝ) :=
          Nat.le_ceil _
        calc
          (m : ℝ) * (2 : ℝ) ^ b * x =
              ((m : ℝ) * (2 : ℝ) ^ (b + 1) * x) / 2 := by
                rw [pow_succ]
                ring
          _ ≤ (⌈(m : ℝ) * (2 : ℝ) ^ (b + 1) * x⌉₊ : ℝ) / 2 := by
                exact (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2 hceil
      · have hleft : (m : ℝ) * (2 : ℝ) ^ b * x ≤ 0 := by
          exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_not_ge hx)
        exact hleft.trans (by positivity)

/-! ## Note (2)/(3): the numerical margin -/

/-- **Note (2)/(3).** At the paper's convenient value `y = 3/5`, the margin
`3λ + (7/5)·ln 2 ≤ -2·ln y` holds for every `0 < λ ≤ 17/1000`.

JUDGE FLAG: the note's exact tolerance is `λ ≤ 0.0170817…` (note (3)); we prove
the *safe* rational bound `17/1000 = 0.017 < 0.0170817…`. This is TIGHT — at
`λ = 17/1000` the two sides differ by `< 3·10^{-4}` — so `norm_num` will need the
real logs bounded carefully. The general-`y` note (2) is
`3λ + (7/5)·ln 2 ≤ -2·ln y` with `y = 1/2 + δ`; the concrete `y = 3/5` version
below is the one consumed downstream (E1 base, `a = 1` Bob step). -/
theorem margin (lam : ℝ) (hlam0 : 0 < lam) (hlam : lam ≤ 17 / 1000) :
    3 * lam + (7 / 5) * Real.log 2 ≤ -2 * Real.log (3 / 5) := by
  rw [Real.log_div (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (5 : ℝ) ≠ 0)]
  have hlog2 := Real.log_two_lt_d9
  have hlog3 := Real.log_three_lt_d9
  have hlog5 := Real.log_five_gt_d9
  norm_num at hlam hlog2 hlog3 hlog5 ⊢
  linarith

/-! ## Notes (5)–(8): properties of the Bob-defect envelope `B(p)` -/

/-- **Note (5).** `B(p) ≥ ln 2` for `p ≥ 2`.
(Holds for all `p ≥ 1` since `6/(5p) > 0`; stated at `p ≥ 2` per the note.) -/
theorem Bdef_ge_log2 (p : ℕ) (hp : 2 ≤ p) : Real.log 2 ≤ Bdef p := by
  unfold Bdef
  have hpR : (0 : ℝ) < p := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hp)
  have hlog : 0 ≤ Real.log (2 : ℝ) :=
    (Real.log_pos (by norm_num)).le
  have hfrac : 0 ≤ (6 : ℝ) / (5 * (p : ℝ)) := by positivity
  rw [show (1 + 6 / (5 * (p : ℝ))) * Real.log 2 =
      Real.log 2 + (6 / (5 * (p : ℝ))) * Real.log 2 by ring]
  exact le_add_of_nonneg_right (mul_nonneg hfrac hlog)

/-- **Note (6).** `B` is antitone on `[2, ∞)`: `B(p') ≥ B(p)` whenever
`2 ≤ p' ≤ p`. -/
theorem Bdef_antitone (p p' : ℕ) (hp' : 2 ≤ p') (hpp : p' ≤ p) :
    Bdef p ≤ Bdef p' := by
  unfold Bdef
  have hp'R : (0 : ℝ) < p' := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num) hp')
  have hpR : (0 : ℝ) < p := lt_of_lt_of_le hp'R (by exact_mod_cast hpp)
  have hppR : (p' : ℝ) ≤ p := by exact_mod_cast hpp
  have hfrac : (6 : ℝ) / (5 * (p : ℝ)) ≤ 6 / (5 * (p' : ℝ)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith
  exact mul_le_mul_of_nonneg_right (by linarith) (Real.log_pos (by norm_num)).le

/-- **Note (7).** `B(⌈p/2⌉) ≥ (⌈p/2⌉ / p)·(B(p) + ln 2)` for `p ≥ 3`.

`⌈p/2⌉` is the Nat `(p+1)/2`. The note reduces the odd case `p = 2q-1` to
`8q² - 19q + 6 ≥ 0` (all `q ≥ 2`), the even case `p = 2q` being immediate. -/
theorem Bdef_ceil_halving (p : ℕ) (hp : 3 ≤ p) :
    ((((p + 1) / 2 : ℕ) : ℝ) / (p : ℝ)) * (Bdef p + Real.log 2)
      ≤ Bdef ((p + 1) / 2) := by
  have hlog : 0 ≤ Real.log (2 : ℝ) := (Real.log_pos (by norm_num)).le
  rcases Nat.even_or_odd p with heven | hodd
  · rw [even_iff_exists_two_mul] at heven
    rcases heven with ⟨q, rfl⟩
    have hq : 2 ≤ q := by omega
    have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
    have hqpos : (0 : ℝ) < q := by positivity
    have hhalf : (2 * q + 1) / 2 = q := by omega
    simp only [hhalf, Bdef, Nat.cast_mul, Nat.cast_ofNat]
    rw [show
      (q : ℝ) / (2 * (q : ℝ)) *
          ((1 + 6 / (5 * (2 * (q : ℝ)))) * Real.log 2 + Real.log 2) =
        (((q : ℝ) / (2 * (q : ℝ))) *
          (2 + 6 / (5 * (2 * (q : ℝ))))) * Real.log 2 by ring]
    apply mul_le_mul_of_nonneg_right _ hlog
    have hleft :
        ((q : ℝ) / (2 * (q : ℝ))) *
            (2 + 6 / (5 * (2 * (q : ℝ)))) =
          ((q : ℝ) * (10 * (2 * (q : ℝ)) + 6)) /
            (5 * (2 * (q : ℝ)) ^ 2) := by
      field_simp [ne_of_gt hqpos]
      ring
    have hright :
        1 + 6 / (5 * (q : ℝ)) =
          (5 * (q : ℝ) + 6) / (5 * (q : ℝ)) := by
      field_simp [ne_of_gt hqpos]
    rw [hleft, hright]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith
  · rw [odd_iff_exists_bit1] at hodd
    rcases hodd with ⟨k, rfl⟩
    have hk : 1 ≤ k := by omega
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hkpos : (0 : ℝ) < k := by positivity
    have hhalf : (2 * k + 1 + 1) / 2 = k + 1 := by omega
    simp only [hhalf, Bdef, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
    rw [show
      ((k : ℝ) + 1) / (2 * (k : ℝ) + 1) *
          ((1 + 6 / (5 * (2 * (k : ℝ) + 1))) * Real.log 2 + Real.log 2) =
        ((((k : ℝ) + 1) / (2 * (k : ℝ) + 1)) *
          (2 + 6 / (5 * (2 * (k : ℝ) + 1)))) * Real.log 2 by ring]
    apply mul_le_mul_of_nonneg_right _ hlog
    have hleft :
        (((k : ℝ) + 1) / (2 * (k : ℝ) + 1)) *
            (2 + 6 / (5 * (2 * (k : ℝ) + 1))) =
          (((k : ℝ) + 1) * (10 * (2 * (k : ℝ) + 1) + 6)) /
            (5 * (2 * (k : ℝ) + 1) ^ 2) := by
      field_simp [ne_of_gt hkpos]
      ring
    have hright :
        1 + 6 / (5 * ((k : ℝ) + 1)) =
          (5 * ((k : ℝ) + 1) + 6) / (5 * ((k : ℝ) + 1)) := by
      field_simp [ne_of_gt hkpos]
    rw [hleft, hright]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have hfactor : 0 ≤ ((k : ℝ) - 1) * (8 * (k : ℝ) + 5) :=
      mul_nonneg (by linarith) (by positivity)
    nlinarith

/-- **Note (8).** `(3/p)·B(p) ≤ (7/5)·ln 2` for `p ≥ 3`, with equality at `p = 3`.
(The left side is decreasing in `p`.) -/
theorem Bdef_three (p : ℕ) (hp : 3 ≤ p) :
    (3 / (p : ℝ)) * Bdef p ≤ (7 / 5) * Real.log 2 := by
  unfold Bdef
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by positivity
  have hcoef :
      (3 / (p : ℝ)) * (1 + 6 / (5 * (p : ℝ))) ≤ (7 / 5 : ℝ) := by
    rw [show (3 / (p : ℝ)) * (1 + 6 / (5 * (p : ℝ))) =
        (15 * (p : ℝ) + 18) / (5 * (p : ℝ) ^ 2) by
      field_simp [ne_of_gt hp0]
      ring]
    apply (div_le_iff₀ (by positivity)).2
    have hfactor : 0 ≤ ((p : ℝ) - 3) * (7 * (p : ℝ) + 6) :=
      mul_nonneg (by linarith) (by positivity)
    nlinarith
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right hcoef (Real.log_pos (by norm_num)).le

/-! ## Note (17): excess-copy ceiling halving -/

/-- **Note (17).** `(q/p)·c_a(p) ≤ c_(a-1)(q)` for `q = ⌈p/2⌉ = (p+1)/2`,
`a ≥ 1`, `p > 2^(a-1)`.

Algebra: `c_a(p) = p - 2^(a-1)`, `c_(a-1)(q) = q - 2^(a-2)`; the claim is
`q - (q/p)·2^(a-1) ≤ q - 2^(a-2)`, i.e. `(q/p)·2 ≥ 1`, which follows from
`q ≥ p/2`. JUDGE FLAG: the hypothesis `p > 2^(a-1)` (equivalently `c_a(p) > 0`)
is carried from the note's context but is NOT needed for THIS inequality — the
only input is `q ≥ p/2`. Retained here for statement-level fidelity; the judge
may drop it. -/
theorem cExcess_ceil_halving (a p : ℕ) (ha : 1 ≤ a)
    (hp : (2 : ℝ) ^ ((a : ℤ) - 1) < (p : ℝ)) :
    ((((p + 1) / 2 : ℕ) : ℝ) / (p : ℝ)) * cExcess a p
      ≤ cExcess (a - 1) ((p + 1) / 2) := by
  unfold cExcess
  have hp0 : (0 : ℝ) < (p : ℝ) :=
    lt_trans (zpow_pos (by norm_num) _) hp
  have hq_nat : p ≤ 2 * ((p + 1) / 2) := by omega
  have hq : (p : ℝ) ≤ 2 * (((p + 1) / 2 : ℕ) : ℝ) := by
    exact_mod_cast hq_nat
  have ha_sub : (((a - 1 : ℕ) : ℤ) - 1) = (a : ℤ) - 2 := by
    omega
  have hpow : (2 : ℝ) ^ ((a : ℤ) - 1) =
      2 * (2 : ℝ) ^ ((a : ℤ) - 2) := by
    rw [show (a : ℤ) - 1 = 1 + ((a : ℤ) - 2) by ring,
      zpow_one_add₀ (by norm_num)]
  have ht : 0 ≤ (2 : ℝ) ^ ((a : ℤ) - 2) :=
    (zpow_pos (by norm_num) _).le
  rw [ha_sub, hpow]
  field_simp [hp0.ne']
  nlinarith [mul_nonneg ht (sub_nonneg.mpr hq)]

/-! ## Density ↔ defect conversion (plan step 2) -/

/-- The state-family conversion `Def(C) ≤ B  ⟺  |C| ≥ n^p·e^{-B}` underlying the
two `stateDefect` / `stateDensity` variants. Requires `0 < |C|` (so the defect
is a genuine log) and `0 < n = Fintype.card Y`. This lemma is why the two state
predicates coincide on positive-target (nonempty-column) states; it is the
formal content of the judge's "density vs defect" decision.

STATEMENT CHECK (E1): the signature is CORRECT as written — no correction needed.
`colDefect = log(n^p/|C|)`; with `n^p/|C| > 0` under `hC`, `hn`, monotonicity of
`log`/`exp` gives `log(n^p/|C|) ≤ B ⟺ n^p/|C| ≤ e^B ⟺ n^p·e^{-B} ≤ |C|`.

PROOF SKETCH.
* `hn` gives `0 < (n : ℝ)^p` (as `(0:ℝ) < n` and `p` any; `n^0 = 1 > 0`), and
  `hC` gives `0 < (|C| : ℝ)`, so `0 < n^p / |C|`.
* `Real.log_le_iff_le_exp (by positivity : 0 < n^p/|C|)` :
    `log (n^p/|C|) ≤ B ↔ n^p/|C| ≤ Real.exp B`.
* `div_le_iff (by exact_mod_cast hC : 0 < (|C| : ℝ))` :
    `n^p/|C| ≤ exp B ↔ n^p ≤ exp B * |C|`.
* Finish by multiplying through by `Real.exp (-B) > 0` and
  `Real.exp_neg`/`Real.exp_add` (`exp B * exp (-B) = 1`) to turn
  `n^p ≤ exp B * |C|` into `n^p · exp(-B) ≤ |C|` (a `mul_le_mul` /
  `le_div_iff` rearrangement). Unfold `colDefect` at the start. -/
theorem state_defect_iff_density (Y : Type*) [Fintype Y] (p : ℕ)
    (C : Finset (Fin p → Y)) (B : ℝ)
    (hC : 0 < C.card) (hn : 0 < Fintype.card Y) :
    colDefect Y p C ≤ B ↔
      ((Fintype.card Y : ℝ) ^ p) * Real.exp (-B) ≤ (C.card : ℝ) := by
  unfold colDefect
  have hnR : (0 : ℝ) < (Fintype.card Y : ℝ) := by
    exact_mod_cast hn
  have hcard : (0 : ℝ) < (C.card : ℝ) := by
    exact_mod_cast hC
  have hquot :
      0 < ((Fintype.card Y : ℝ) ^ p) / (C.card : ℝ) :=
    div_pos (pow_pos hnR p) hcard
  rw [Real.log_le_iff_le_exp hquot, div_le_iff₀ hcard,
    Real.exp_neg, ← div_eq_mul_inv,
    div_le_iff₀ (Real.exp_pos B), mul_comm]

end EthBridge
