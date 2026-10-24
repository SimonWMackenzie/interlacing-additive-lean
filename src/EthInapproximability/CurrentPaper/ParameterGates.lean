import EthInapproximability.CurrentPaper.Parameters
import EthInapproximability.CurrentPaper.HardSeed
import EthInapproximability.CurrentPaper.PrimeSampler

/-!
# Numerical acceptance gates for the current explicit parameter formulas

Source: v8 `F-parameter-choices.tex`. This module extends, rather than changes,
the frozen literal definitions in `Parameters`. Mathematical dependencies on
the actual graph source and indexed family are kept distinct from the two
integer acceptance tests. No protocol lower bound is encoded in acceptance.
-/

namespace EthInapproximability.CurrentPaper.ParameterGates

open Parameters

def lossBudget (i : Input) : ℕ :=
  max (secondDepth i) (tailDepth i) + outerWidth i + 4

def stoppingBudget (i : Input) : ℕ :=
  lossBudget i + 8 * firstWidth i + outerExponent i + secondExponent i +
    i.cost + firstExponent i + 10

theorem scale_add_four_le_firstExponent (i : Input) : scale i + 4 ≤ firstExponent i := by
  have h := scale_floor i
  norm_num at h
  unfold firstExponent
  nlinarith

theorem outerExponent_le_scalePower (i : Input) : outerExponent i ≤ 2 ^ scale i := by
  have h := scale_floor i
  norm_num at h
  have hp := outer_polynomial_le_power (show 32 ≤ scale i by omega)
  change 1000 * scale i ^ 2 ≤ _
  omega

theorem stoppingBudget_le_two_outer (i : Input) : stoppingBudget i ≤ 2 * outerWidth i := by
  let A := 2 ^ firstExponent i
  have hsmall : 2 ^ scale i ≤ A :=
    Nat.pow_le_pow_right (by decide) (by have := scale_add_four_le_firstExponent i; omega)
  have hsecond : secondDepth i ≤ A := (secondDepth_bound i).trans
    (Nat.pow_le_pow_right (by decide) (by have := scale_add_four_le_firstExponent i; omega))
  have htail : tailDepth i ≤ A :=
    (tailDepth_le_quarter_bins i).trans ((Nat.div_le_self _ _).trans
      ((bins_le_scale_power i).trans hsmall))
  have hfirst : firstWidth i ≤ A := Nat.sub_le _ _
  have houter : outerExponent i ≤ A := (outerExponent_le_scalePower i).trans hsmall
  have hq2 : secondExponent i ≤ A := (secondExponent_le i).trans
    (Nat.pow_le_pow_right (by decide) (by have := scale_add_four_le_firstExponent i; omega))
  have hcost : i.cost ≤ A := (public_bounds i).2.2.1.trans hsmall
  have ha : firstExponent i ≤ A := by
    have h := scale_polynomial_bound i
    exact (by omega : firstExponent i ≤ 2 ^ scale i).trans hsmall
  have hA : 16 ≤ A := by
    have he : 4 ≤ firstExponent i := by have := scale_add_four_le_firstExponent i; omega
    exact (by norm_num : (16 : ℕ) = 2 ^ 4) ▸ Nat.pow_le_pow_right (by decide) he
  have hexp : firstExponent i + 4 ≤ outerExponent i := by
    have hl := scale_floor i
    norm_num at hl
    unfold firstExponent outerExponent
    nlinarith
  have hpower : 16 * A ≤ outerWidth i := by
    have h := Nat.pow_le_pow_right (n := 2) (by decide) hexp
    simpa only [pow_add, show (2 : ℕ) ^ 4 = 16 by norm_num,
      Nat.mul_comm, outerWidth] using h
  unfold stoppingBudget lossBudget
  omega

theorem balanceExponent_add_four_le_outer (i : Input) :
    balanceExponent i + 4 ≤ outerWidth i := by
  have hl := scale_floor i
  norm_num at hl
  have hp := quartic_le_power (show 32 ≤ scale i by omega)
  have hsmall : 6 * scale i ≤ outerExponent i := by unfold outerExponent; nlinarith
  have hexp := Nat.pow_le_pow_right (n := 2) (by decide) hsmall
  change 100000000 * scale i ^ 4 + 4 ≤ 2 ^ outerExponent i
  omega

theorem balanceOrder_ge_four_outer (i : Input) :
    4 * outerWidth i ≤ balanceOrder i := by
  have hl := scale_floor i
  norm_num at hl
  have hs : 1 ≤ scale i ^ 2 := one_le_pow₀ (by omega)
  have hp : scale i ^ 2 ≤ scale i ^ 4 := Nat.pow_le_pow_right (by omega) (by decide)
  have he : outerExponent i + 2 ≤ balanceExponent i := by
    change 1000 * scale i ^ 2 + 2 ≤ 100000000 * scale i ^ 4
    omega
  have h := Nat.pow_le_pow_right (n := 2) (by decide) he
  simpa only [pow_add, show (2 : ℕ) ^ 2 = 4 by norm_num,
    Nat.mul_comm, outerWidth, balanceOrder] using h

theorem balanceOrder_ge_two_stoppingBudget (i : Input) :
    2 * stoppingBudget i ≤ balanceOrder i := by
  have h := stoppingBudget_le_two_outer i
  have ht := balanceOrder_ge_four_outer i
  omega

theorem sqrt_balanceExponent (i : Input) :
    Real.sqrt (balanceExponent i : ℝ) = 10000 * (scale i : ℝ) ^ 2 := by
  have he : (balanceExponent i : ℝ) = (10000 * (scale i : ℝ) ^ 2) ^ 2 := by
    unfold balanceExponent
    push_cast
    ring
  rw [he, Real.sqrt_sq (by positivity)]

theorem stopping_exponential_margin (i : Input) :
    (stoppingBudget i + balanceExponent i + 4 : ℕ) ≤
      (2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt (balanceExponent i : ℝ)) := by
  have hh := stoppingBudget_le_two_outer i
  have hm := balanceExponent_add_four_le_outer i
  have hsum : stoppingBudget i + balanceExponent i + 4 ≤ 4 * outerWidth i := by omega
  have hl := scale_floor i
  norm_num at hl
  have hexp : outerExponent i + 2 ≤ 4900 * scale i ^ 2 := by
    unfold outerExponent
    nlinarith
  have hp : 4 * outerWidth i ≤ 2 ^ (4900 * scale i ^ 2) := by
    have h := Nat.pow_le_pow_right (n := 2) (by decide) hexp
    simpa only [pow_add, show (2 : ℕ) ^ 2 = 4 by norm_num,
      Nat.mul_comm, outerWidth] using h
  have hcast : ((stoppingBudget i + balanceExponent i + 4 : ℕ) : ℝ) ≤
      (2 : ℝ) ^ (4900 * scale i ^ 2 : ℕ) := by exact_mod_cast hsum.trans hp
  rw [sqrt_balanceExponent]
  have he : (49 / 100 : ℝ) * (10000 * (scale i : ℝ) ^ 2) =
      ((4900 * scale i ^ 2 : ℕ) : ℝ) := by push_cast; ring
  rw [he, Real.rpow_natCast]
  exact hcast

/-- A square comparison discharges the exact double-exponential chi gate. -/
theorem chi_le_dyadic_of_square (m k : ℕ)
    (h : 10000 * k ^ 2 ≤ 2401 * m) :
    HardSeed.columnDensity ((2 : ℝ) ^ m) ≤ (2 : ℝ) ^ (-((2 ^ k : ℕ) : ℝ)) := by
  have hc : (10000 : ℝ) * (k : ℝ) ^ 2 ≤ 2401 * (m : ℝ) := by exact_mod_cast h
  have hr : (100 / 49 : ℝ) * k ≤ Real.sqrt (m : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have he : (k : ℝ) ≤ (49 / 100 : ℝ) * Real.sqrt (m : ℝ) := by linarith
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he
  rw [HardSeed.columnDensity_pow]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  rw [Real.rpow_natCast] at hp
  have hcast : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by norm_cast
  rw [hcast]
  linarith

theorem first_chi_gate (i : Input) (j : ℕ) (hj : j ≤ 1) :
    HardSeed.columnDensity ((2 : ℝ) ^ (firstExponent i - j)) ≤
      (2 : ℝ) ^ (-(firstDepth i : ℝ)) := by
  apply chi_le_dyadic_of_square
  have hl := scale_floor i
  norm_num at hl
  have ha : j ≤ firstExponent i := by unfold firstExponent; nlinarith
  have hsub := Nat.sub_add_cancel ha
  change 10000 * (7 * scale i) ^ 2 ≤ 2401 * (firstExponent i - j)
  change (firstExponent i - j) + j = 256 * scale i ^ 2 at hsub
  nlinarith

theorem tail_chi_gate (i : Input) :
    HardSeed.columnDensity ((2 : ℝ) ^ (binExponent i - 2)) ≤
      (2 : ℝ) ^ (-(tailDepth i : ℝ)) := by
  apply chi_le_dyadic_of_square
  have hu := auxiliaryLog_floor i
  have hb : 2 ≤ binExponent i := by unfold binExponent; nlinarith
  have hsub := Nat.sub_add_cancel hb
  change 10000 * (40 * auxiliaryLog i) ^ 2 ≤ 2401 * (binExponent i - 2)
  change (binExponent i - 2) + 2 = 10000 * auxiliaryLog i ^ 2 at hsub
  nlinarith

theorem balanceOrder_ge_two_secondExponent (i : Input) :
    2 * secondExponent i + 2 ≤ balanceOrder i := by
  have hl := scale_floor i
  norm_num at hl
  have he := secondExponent_le i
  have hbe : scale i + 3 ≤ balanceExponent i := by
    have hs : scale i ≤ scale i ^ 4 := by
      simpa using (Nat.pow_le_pow_right (show 0 < scale i by omega) (by decide : 1 ≤ 4))
    unfold balanceExponent
    omega
  have hp : 2 ^ (scale i + 3) ≤ balanceOrder i :=
    Nat.pow_le_pow_right (by decide) hbe
  have hpow : 0 < 2 ^ scale i := by positivity
  rw [pow_add] at he hp
  norm_num at he hp
  omega

theorem samplerAlphabet_ge_two (i : Input) (hx : 2 ≤ i.rows) :
    2 ≤ firstWidth i * i.rows := by
  have hq := firstWidth_pos i
  calc
    2 = 1 * 2 := by norm_num
    _ ≤ firstWidth i * i.rows := Nat.mul_le_mul hq hx

theorem actualFamily_balanced (i : Input) (hc : 0 < i.sourceConstant)
    (ha : Accepted i) :
    NPCC.IsBalancedFamily (balanceOrder i)
      (PrimeSampler.family (secondWidth i) (balanceOrder i) (firstWidth i * i.rows)
        (lt_of_lt_of_le (by decide : 0 < 2) (samplerAlphabet_ge_two i ha.1)))
      (1 / (100 * (balanceOrder i : ℝ))) := by
  exact PrimeSampler.family_balanced _ _ _ _ (balanceOrder_pos i)
    (by have h := accepted_balance_four_le_second i hc ha; omega)

theorem actualSecondFamily_balanced (i : Input) (hc : 0 < i.sourceConstant)
    (ha : Accepted i) :
    NPCC.IsBalancedFamily (balanceOrder i)
      (PrimeSampler.secondFamily (firstExponent i) (secondWidth i) (balanceOrder i)
        (firstWidth i * i.rows)
        (lt_of_lt_of_le (by decide : 0 < 2) (samplerAlphabet_ge_two i ha.1))
        (PrimeSampler.canonicalFirstRowsEquiv (firstExponent i) i.rows))
      (1 / (100 * (balanceOrder i : ℝ))) := by
  exact PrimeSampler.canonicalSecondFamily_balanced _ _ _ _ _ (balanceOrder_pos i)
    (by have h := accepted_balance_four_le_second i hc ha; omega)

theorem actualFamily_size_lower (i : Input) (hc : 0 < i.sourceConstant)
    (ha : Accepted i) :
    (firstWidth i * i.rows) ^ balanceOrder i ≤
      PrimeSampler.size (secondWidth i) (balanceOrder i) (firstWidth i * i.rows) := by
  exact PrimeSampler.size_lower _ _ _
    (lt_of_lt_of_le (by decide : 0 < 2) (samplerAlphabet_ge_two i ha.1))
    (balanceOrder_pos i)
    (by have h := accepted_balance_four_le_second i hc ha; omega)

theorem actualFamily_size_bounds (i : Input) (hc : 0 < i.sourceConstant)
    (ha : Accepted i) :
    secondWidth i ^ 2 ≤ 2 ^ balanceOrder i ∧
      2 ^ balanceOrder i ≤ (firstWidth i * i.rows) ^ balanceOrder i ∧
      (firstWidth i * i.rows) ^ balanceOrder i ≤
        PrimeSampler.size (secondWidth i) (balanceOrder i) (firstWidth i * i.rows) := by
  refine ⟨?_, Nat.pow_le_pow_left (samplerAlphabet_ge_two i ha.1) _,
    actualFamily_size_lower i hc ha⟩
  unfold secondWidth
  rw [← pow_mul]
  exact Nat.pow_le_pow_right (by decide)
    (by have h := balanceOrder_ge_two_secondExponent i; omega)

theorem actualFamily_size_ge_alphabet (i : Input) (hc : 0 < i.sourceConstant)
    (ha : Accepted i) :
    firstWidth i * i.rows ≤
      PrimeSampler.size (secondWidth i) (balanceOrder i) (firstWidth i * i.rows) := by
  calc
    firstWidth i * i.rows = (firstWidth i * i.rows) ^ 1 := (pow_one _).symm
    _ ≤ (firstWidth i * i.rows) ^ balanceOrder i := Nat.pow_le_pow_right
      (by have h := samplerAlphabet_ge_two i ha.1; omega) (balanceOrder_pos i)
    _ ≤ _ := actualFamily_size_lower i hc ha

theorem actualFamily_size_ge_alphabet_mul_square (i : Input)
    (hc : 0 < i.sourceConstant) (ha : Accepted i) :
    (firstWidth i * i.rows) * secondWidth i ^ 2 ≤
      PrimeSampler.size (secondWidth i) (balanceOrder i) (firstWidth i * i.rows) := by
  have hm := samplerAlphabet_ge_two i ha.1
  calc
    (firstWidth i * i.rows) * secondWidth i ^ 2 =
        (firstWidth i * i.rows) * 2 ^ (2 * secondExponent i) := by
      unfold secondWidth
      rw [← pow_mul, Nat.mul_comm (secondExponent i) 2]
    _ ≤ (firstWidth i * i.rows) * (firstWidth i * i.rows) ^
        (2 * secondExponent i) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm _)
    _ = (firstWidth i * i.rows) ^ (2 * secondExponent i + 1) := by rw [pow_succ]; ring
    _ ≤ (firstWidth i * i.rows) ^ balanceOrder i := Nat.pow_le_pow_right
      (by omega) (by have h := balanceOrder_ge_two_secondExponent i; omega)
    _ ≤ _ := actualFamily_size_lower i hc ha

theorem accepted_secondWidth_ge_9216_bins (i : Input)
    (hc : 0 < i.sourceConstant) (ha : Accepted i) :
    9216 * bins i ≤ secondWidth i := by
  have hq := outerWidth_pos i
  have ht := balanceOrder_pos i
  calc
    9216 * bins i ≤ 2 ^ 40 * 1 * bins i * 1 ^ 2 * 1 ^ 4 := by norm_num; omega
    _ ≤ 2 ^ 40 * i.sourceConstant * bins i * outerWidth i ^ 2 * balanceOrder i ^ 4 := by
      gcongr <;> omega
    _ ≤ _ := ha.2.2.2

theorem actualFamily_size_ge_9216_bins (i : Input)
    (hc : 0 < i.sourceConstant) (ha : Accepted i) :
    9216 * bins i ≤
      PrimeSampler.size (secondWidth i) (balanceOrder i) (firstWidth i * i.rows) := by
  have hs := actualFamily_size_bounds i hc ha
  calc
    9216 * bins i ≤ secondWidth i := accepted_secondWidth_ge_9216_bins i hc ha
    _ ≤ secondWidth i ^ 2 := by
      simpa using (Nat.pow_le_pow_right (secondWidth_pos i) (by decide : 1 ≤ 2))
    _ ≤ _ := hs.1.trans (hs.2.1.trans hs.2.2)

theorem outer_firstWidth_two_bins (i : Input) : 2 * bins i ≤ firstWidth i := by
  have hl := scale_floor i
  norm_num at hl
  have hb := binExponent_le_scale i
  have he : binExponent i + 2 ≤ firstExponent i := by
    unfold firstExponent
    nlinarith
  have hp := Nat.pow_le_pow_right (n := 2) (by decide) he
  rw [pow_add] at hp
  have hs := bins_pos i
  change 2 ^ binExponent i * 2 ^ 2 ≤ 2 ^ firstExponent i at hp
  change 2 * 2 ^ binExponent i ≤ 2 ^ firstExponent i - 2
  norm_num at hp
  change 0 < 2 ^ binExponent i at hs
  omega

theorem outer_secondDepth_power (i : Input) :
    2048 * bins i * firstWidth i * i.rows ≤ 2 ^ secondDepth i := by
  have hp := Nat.le_pow_clog (by decide : 1 < 2)
    (32 * bins i * firstWidth i * i.rows)
  unfold secondDepth
  rw [pow_add]
  norm_num
  nlinarith

theorem outer_separation_div (i : Input) (hx : 2 ≤ i.rows) (N : ℕ)
    (hN : firstWidth i * i.rows ≤ N) :
    (bins i : ℝ) * (⌈2 * (N : ℝ) / 2 ^ secondDepth i⌉₊ : ℝ) < N := by
  have hs := bins_pos i
  have hq := firstWidth_pos i
  have htwo := outer_firstWidth_two_bins i
  have hNpos : 0 < N := by nlinarith
  have hNlow : 4 * bins i ≤ N := by nlinarith
  have hpow := outer_secondDepth_power i
  have hp : 2048 * bins i ≤ 2 ^ secondDepth i := by
    have hmul : 1 ≤ firstWidth i * i.rows := by nlinarith
    nlinarith
  have hsr : (0 : ℝ) < bins i := by exact_mod_cast hs
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hlow : 4 * (bins i : ℝ) ≤ N := by exact_mod_cast hNlow
  have hpr : 2048 * (bins i : ℝ) ≤ (2 : ℝ) ^ secondDepth i := by
    exact_mod_cast hp
  have hpp : (0 : ℝ) < 2 ^ secondDepth i := by positivity
  have hfrac : (bins i : ℝ) * (2 * (N : ℝ) / 2 ^ secondDepth i) ≤ N / 1024 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hpp).2
    nlinarith
  have hc := Nat.ceil_lt_add_one (R := ℝ)
    (show 0 ≤ 2 * (N : ℝ) / 2 ^ secondDepth i by positivity)
  have hm := mul_lt_mul_of_pos_left hc hsr
  nlinarith

theorem outer_separation_zpow (i : Input) (hx : 2 ≤ i.rows) (N : ℕ)
    (hN : firstWidth i * i.rows ≤ N) :
    (bins i : ℝ) * (⌈(2 : ℝ) ^ (1 - (secondDepth i : ℤ)) * N⌉₊ : ℝ) < N := by
  have he : (2 : ℝ) ^ (1 - (secondDepth i : ℤ)) = 2 / 2 ^ secondDepth i := by
    rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
    simp
  rw [he]
  have hr : 2 / (2 : ℝ) ^ secondDepth i * N = 2 * N / (2 : ℝ) ^ secondDepth i := by ring
  rw [hr]
  exact outer_separation_div i hx N hN

theorem actualFamily_outer_separation (i : Input)
    (hc : 0 < i.sourceConstant) (ha : Accepted i) :
    bins i ≤ 2 ^ secondDepth i ∧
      (bins i : ℝ) *
        (⌈(2 : ℝ) ^ (1 - (secondDepth i : ℤ)) *
          PrimeSampler.size (secondWidth i) (balanceOrder i) (firstWidth i * i.rows)⌉₊ : ℝ) <
        PrimeSampler.size (secondWidth i) (balanceOrder i) (firstWidth i * i.rows) := by
  refine ⟨bins_le_secondDepth_power i (by have h := ha.1; omega), ?_⟩
  exact outer_separation_zpow i ha.1 _ (actualFamily_size_ge_alphabet i hc ha)

/-- Absorb a balance error at most one by one additional binary digit. -/
theorem dyadic_ratio_lower {h ε : ℝ} {L K : ℕ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hh : (2 : ℝ) ^ (-(L : ℝ)) ≤ h) :
    (2 : ℝ) ^ (-((L + K + 1 : ℕ) : ℝ)) ≤
      h * (2 : ℝ) ^ (-(K : ℝ)) / (1 + ε) := by
  have hh0 : 0 ≤ h := (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).le.trans hh
  calc
    (2 : ℝ) ^ (-((L + K + 1 : ℕ) : ℝ)) =
        (2 : ℝ) ^ (-(L : ℝ)) * (2 : ℝ) ^ (-(K : ℝ)) / 2 := by
      push_cast
      rw [show -((L : ℝ) + K + 1) = -(L : ℝ) + -(K : ℝ) + -1 by ring,
        Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      norm_num [Real.rpow_neg_one, div_eq_mul_inv]
    _ ≤ h * (2 : ℝ) ^ (-(K : ℝ)) / 2 := by gcongr
    _ ≤ h * (2 : ℝ) ^ (-(K : ℝ)) / (1 + ε) := by
      apply div_le_div_of_nonneg_left (by positivity) (by linarith)
      linarith

theorem three_fifths_le_negative_half_power :
    (3 / 5 : ℝ) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hnonneg : 0 ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have hsq : ((2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ (2 : ℕ) = 1 / 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num [Real.rpow_neg_one]
  nlinarith

/-- A half-bit exponent budget implies the first localized stopping gate. -/
theorem row_stopping_gate {t L H A : ℕ} {h ε : ℝ}
    (ht : 0 < t) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hh : (2 : ℝ) ^ (-(L : ℝ)) ≤ h)
    (hbudget : 2 * (L + H + A + 1) ≤ t) :
    (3 / 5 : ℝ) ≤
      (h * (2 : ℝ) ^ (-((H + A : ℕ) : ℝ)) / (1 + ε)) ^ (1 / (t : ℝ)) := by
  have htr : (0 : ℝ) < t := by exact_mod_cast ht
  have hratio := dyadic_ratio_lower hε0 hε1 (K := H + A) hh
  have hbudgetR : 2 * ((L : ℝ) + H + A + 1) ≤ t := by exact_mod_cast hbudget
  have hexp : -(1 / 2 : ℝ) ≤ -((L + (H + A) + 1 : ℕ) : ℝ) * (1 / (t : ℝ)) := by
    push_cast
    rw [mul_one_div, le_div_iff₀ htr]
    linarith
  calc
    (3 / 5 : ℝ) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := three_fifths_le_negative_half_power
    _ ≤ (2 : ℝ) ^ (-((L + (H + A) + 1 : ℕ) : ℝ) * (1 / (t : ℝ))) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = ((2 : ℝ) ^ (-((L + (H + A) + 1 : ℕ) : ℝ))) ^ (1 / (t : ℝ)) :=
      Real.rpow_mul (by norm_num) _ _
    _ ≤ _ := Real.rpow_le_rpow (by positivity) hratio (by positivity)

/-- The second localized stopping gate, using the exact hard-seed density. -/
theorem column_stopping_gate {m L H : ℕ} {h ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hh : (2 : ℝ) ^ (-(L : ℝ)) ≤ h)
    (hbudget : ((L + H + m + 1 : ℕ) : ℝ) ≤
      (2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt (m : ℝ))) :
    HardSeed.columnDensity ((2 : ℝ) ^ m) ≤
      h * (2 : ℝ) ^ (-((H + m : ℕ) : ℝ)) / (1 + ε) := by
  rw [HardSeed.columnDensity_pow]
  apply (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (neg_le_neg hbudget)).trans
  simpa [Nat.add_assoc] using dyadic_ratio_lower hε0 hε1 (K := H + m) hh

/-- Both stopping gates for a power-of-two sampling order. -/
theorem localized_stopping_gates {t m L H A : ℕ} {h ε : ℝ}
    (ht : t = 2 ^ m) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hh : (2 : ℝ) ^ (-(L : ℝ)) ≤ h)
    (hrow : 2 * (L + H + A + 1) ≤ t)
    (hcol : ((L + H + m + 1 : ℕ) : ℝ) ≤
      (2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt (m : ℝ))) :
    (3 / 5 : ℝ) ≤
        (h * (2 : ℝ) ^ (-((H + A : ℕ) : ℝ)) / (1 + ε)) ^ (1 / (t : ℝ)) ∧
      HardSeed.columnDensity (t : ℝ) ≤
        h * (2 : ℝ) ^ (-((H + m : ℕ) : ℝ)) / (1 + ε) := by
  constructor
  · exact row_stopping_gate (ht ▸ pow_pos (by norm_num) _) hε0 hε1 hh hrow
  · rw [ht, Nat.cast_pow, Nat.cast_ofNat]
    exact column_stopping_gate hε0 hε1 hh hcol

/-- The accumulated error of at most `t` balanced-family factors is below
`51/50`, with no approximation of exponential values. -/
theorem product_balance_error {t k : ℕ} (ht : 0 < t) (hk : k ≤ t) :
    (1 + 1 / (100 * (t : ℝ))) ^ k < (51 / 50 : ℝ) := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hkR : (k : ℝ) ≤ t := by exact_mod_cast hk
  have hbase : 1 + 1 / (100 * (t : ℝ)) ≤ Real.exp (1 / (100 * (t : ℝ))) := by
    simpa [add_comm] using Real.add_one_le_exp (1 / (100 * (t : ℝ)))
  have hexponent : (k : ℝ) * (1 / (100 * (t : ℝ))) ≤ 1 / 100 := by
    rw [mul_one_div, div_le_iff₀ (by positivity : (0 : ℝ) < 100 * t)]
    nlinarith
  calc
    (1 + 1 / (100 * (t : ℝ))) ^ k ≤ (Real.exp (1 / (100 * (t : ℝ)))) ^ k := by
      gcongr
    _ = Real.exp ((k : ℝ) * (1 / (100 * (t : ℝ)))) := by rw [Real.exp_nat_mul]
    _ ≤ Real.exp (1 / 100 : ℝ) := Real.exp_le_exp.mpr hexponent
    _ < 1 / (1 - (1 / 100 : ℝ)) :=
      Real.exp_bound_div_one_sub_of_interval' (by norm_num) (by norm_num)
    _ < (51 / 50 : ℝ) := by norm_num

theorem sourceConstant_bounds {c Δ γ : ℚ}
    (hΔ : 1 ≤ Δ) (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hsource : 2 ^ 44 * Δ / γ ≤ c) :
    2 ^ 44 ≤ c ∧ 2 ^ 44 ≤ c * γ := by
  have hmul : 2 ^ 44 * Δ ≤ c * γ := (div_le_iff₀ hγ).1 hsource
  have hlarge : (2 : ℚ) ^ 44 ≤ c * γ := by nlinarith
  have hc : 0 < c := by
    by_contra h
    have hnonpos : c * γ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) hγ.le
    norm_num at hlarge
    linarith
  have hmul_le : c * γ ≤ c := mul_le_of_le_one_right hc.le hγone
  exact ⟨hlarge.trans hmul_le, hlarge⟩

theorem sourceVertex_bound {c Δ γ δ : ℚ}
    (hΔ : 1 ≤ Δ) (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hsource : 2 ^ 44 * Δ / γ ≤ c)
    (hvertex : γ / (4 * Δ) ≤ δ) :
    2 ^ 42 ≤ c * δ := by
  have hb := sourceConstant_bounds hΔ hγ hγone hsource
  have hc : 0 ≤ c := le_trans (by norm_num) hb.1
  have hden : 0 < 4 * Δ := by linarith
  have hmul : 2 ^ 44 * Δ ≤ c * γ := (div_le_iff₀ hγ).1 hsource
  calc
    (2 : ℚ) ^ 42 ≤ (c * γ) / (4 * Δ) := by
      apply (le_div_iff₀ hden).2
      norm_num at hmul ⊢
      linarith
    _ = c * (γ / (4 * Δ)) := by ring
    _ ≤ c * δ := mul_le_mul_of_nonneg_left hvertex hc

/-- Appendix A's equivalent minimum form, before substituting the computable
parameter record. All three column tolerances and all three row tolerances
are derived from the actual source-constant bound. -/
theorem source_tolerances_rational {c s Δ γ δ : ℚ}
    (hΔ : 1 ≤ Δ) (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hsource : 2 ^ 44 * Δ / γ ≤ c)
    (hs : 64 ≤ s) (hvertex : γ / (4 * Δ) ≤ δ) :
    c⁻¹ ≤ γ / 24 ∧
    2 / (c * s) ≤ min ((2 : ℚ) ^ (-21 : ℤ) / (2000 * s))
      (min ((2 : ℚ) ^ (-22 : ℤ) * δ / 32)
        ((2 : ℚ) ^ (-22 : ℤ) / (32 * (s - 3)))) ∧
    1 / (c * s) ≤ min ((1 / 184 : ℚ) / 200)
      (min (((1 / 184 : ℚ) * (γ / 24)) / (64 * s))
        ((2 / (c * s)) / 2)) := by
  have hb := sourceConstant_bounds hΔ hγ hγone hsource
  have hv := sourceVertex_bound hΔ hγ hγone hsource hvertex
  have hc : 0 < c := by have h := hb.1; norm_num at h; linarith
  have hspos : 0 < s := by linarith
  have hsm : 0 < s - 3 := by linarith
  have hcs : 0 < c * s := mul_pos hc hspos
  have hcLarge : 17592186044416 ≤ c := by norm_num at hb; exact hb.1
  have hcgLarge : 17592186044416 ≤ c * γ := by norm_num at hb; exact hb.2
  have hcvLarge : 4398046511104 ≤ c * δ := by norm_num at hv; exact hv
  have hzeta : c⁻¹ ≤ γ / 24 := by
    rw [← one_div]
    apply (div_le_iff₀ hc).2
    nlinarith
  have hcolT : 2 / (c * s) ≤ (2 : ℚ) ^ (-21 : ℤ) / (2000 * s) := by
    norm_num
    apply (div_le_div_iff₀ hcs (by positivity : (0 : ℚ) < 2000 * s)).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hcLarge) hspos.le]
  have hcolV : 2 / (c * s) ≤ (2 : ℚ) ^ (-22 : ℤ) * δ / 32 := by
    apply (div_le_iff₀ hcs).2
    norm_num
    have hmul := mul_le_mul_of_nonneg_right hcvLarge hspos.le
    nlinarith
  have hcolB : 2 / (c * s) ≤ (2 : ℚ) ^ (-22 : ℤ) / (32 * (s - 3)) := by
    norm_num
    apply (div_le_div_iff₀ hcs (by positivity : (0 : ℚ) < 32 * (s - 3))).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hcLarge) hspos.le]
  have hrow0 : 1 / (c * s) ≤ (1 / 184 : ℚ) / 200 := by
    apply (div_le_iff₀ hcs).2
    norm_num
    nlinarith [mul_nonneg (sub_nonneg.mpr hcLarge) hspos.le]
  have hrow1 : 1 / (c * s) ≤ ((1 / 184 : ℚ) * (γ / 24)) / (64 * s) := by
    apply (div_le_div_iff₀ hcs (by positivity : (0 : ℚ) < 64 * s)).2
    norm_num
    nlinarith [mul_nonneg (sub_nonneg.mpr hcgLarge) hspos.le]
  have hrow2 : 1 / (c * s) ≤ (2 / (c * s)) / 2 := by
    ring_nf
    exact le_refl _
  exact ⟨hzeta, le_min hcolT (le_min hcolV hcolB), le_min hrow0 (le_min hrow1 hrow2)⟩

/-- The full Appendix A tolerance chain for the actual computable parameters.
The deletion estimate is a visible graph-source input; all six tolerance
bounds, including the one involving `zeta=gamma/24`, are conclusions. -/
theorem source_tolerances (i : Input) (Δ : ℕ) (γ δ : ℚ)
    (hΔ : 1 ≤ Δ) (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hsource : 2 ^ 44 * (Δ : ℚ) / γ ≤ i.sourceConstant)
    (hvertex : γ / (4 * (Δ : ℚ)) ≤ δ) :
    (i.sourceConstant : ℚ)⁻¹ ≤ γ / 24 ∧
    columnTolerance i ≤ min ((2 : ℚ) ^ (-21 : ℤ) / (2000 * bins i))
      (min ((2 : ℚ) ^ (-22 : ℤ) * δ / 32)
        ((2 : ℚ) ^ (-22 : ℤ) / (32 * ((bins i : ℚ) - 3)))) ∧
    rowTolerance i ≤ min ((1 / 184 : ℚ) / 200)
      (min (((1 / 184 : ℚ) * (γ / 24)) / (64 * bins i))
        (columnTolerance i / 2)) := by
  have hs : (64 : ℚ) ≤ bins i := by
    exact_mod_cast (Nat.le_of_dvd (bins_pos i) (sixtyfour_dvd_bins i))
  have h := source_tolerances_rational (c := (i.sourceConstant : ℚ))
    (s := (bins i : ℚ)) (Δ := (Δ : ℚ)) (γ := γ) (δ := δ)
    (by exact_mod_cast hΔ) hγ hγone hsource hs hvertex
  simpa only [rowTolerance, columnTolerance, Nat.cast_mul] using h

/-- Exactly the half-minimum form displayed in
`eq:paper-parameter-source-constant`. -/
theorem source_tolerances_display (i : Input) (Δ : ℕ) (γ δ : ℚ)
    (hΔ : 1 ≤ Δ) (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hsource : 2 ^ 44 * (Δ : ℚ) / γ ≤ i.sourceConstant)
    (hvertex : γ / (4 * (Δ : ℚ)) ≤ δ) :
    (i.sourceConstant : ℚ)⁻¹ ≤ γ / 24 ∧
    columnTolerance i ≤ (1 / 2 : ℚ) *
      min ((2 : ℚ) ^ (-21 : ℤ) / (1000 * bins i))
        (min ((2 : ℚ) ^ (-22 : ℤ) * δ / 16)
          ((2 : ℚ) ^ (-22 : ℤ) / (16 * ((bins i : ℚ) - 3)))) ∧
    rowTolerance i ≤ (1 / 2 : ℚ) * min ((1 / 184 : ℚ) / 100)
      (min (((1 / 184 : ℚ) * (γ / 24)) / (32 * bins i))
        (columnTolerance i)) := by
  have h := source_tolerances i Δ γ δ hΔ hγ hγone hsource hvertex
  refine ⟨h.1, ?_, ?_⟩
  · rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℚ) ≤ 1 / 2),
      mul_min_of_nonneg _ _ (by norm_num : (0 : ℚ) ≤ 1 / 2)]
    rcases le_min_iff.mp h.2.1 with ⟨hT, hVB⟩
    rcases le_min_iff.mp hVB with ⟨hV, hB⟩
    refine le_min ?_ (le_min ?_ ?_)
    · convert hT using 1
      ring
    · convert hV using 1
      ring
    · convert hB using 1
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
  · rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℚ) ≤ 1 / 2),
      mul_min_of_nonneg _ _ (by norm_num : (0 : ℚ) ≤ 1 / 2)]
    rcases le_min_iff.mp h.2.2 with ⟨h0, h12⟩
    rcases le_min_iff.mp h12 with ⟨h1, h2⟩
    refine le_min ?_ (le_min ?_ ?_)
    · convert h0 using 1
      ring
    · convert h1 using 1
      ring
    · convert h2 using 1
      ring

theorem bins_sub_three_cast (i : Input) :
    ((bins i - 3 : ℕ) : ℚ) = (bins i : ℚ) - 3 := by
  have hs := Nat.le_of_dvd (bins_pos i) (sixtyfour_dvd_bins i)
  exact_mod_cast (Nat.cast_sub (show 3 ≤ bins i by omega) :
    ((bins i - 3 : ℕ) : ℚ) = (bins i : ℚ) - (3 : ℚ))

/-- The common budget in Appendix F simultaneously covers every call with
ambient width at most `q*q₂` and certified base cost at most `D+a`. -/
theorem all_stopping_gates (i : Input) {H A : ℕ} {h ε : ℝ}
    (hH : H ≤ i.cost + firstExponent i)
    (hA : A ≤ outerExponent i + secondExponent i)
    (hh : (2 : ℝ) ^ (-(lossBudget i : ℝ)) ≤ h)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (3 / 5 : ℝ) ≤
        (h * (2 : ℝ) ^ (-((H + A : ℕ) : ℝ)) / (1 + ε)) ^
          (1 / (balanceOrder i : ℝ)) ∧
      HardSeed.columnDensity (balanceOrder i : ℝ) ≤
        h * (2 : ℝ) ^ (-((H + balanceExponent i : ℕ) : ℝ)) / (1 + ε) := by
  apply localized_stopping_gates rfl hε0 hε1 hh
  · change 2 * (lossBudget i + H + A + 1) ≤ balanceOrder i
    have hbudget := balanceOrder_ge_two_stoppingBudget i
    unfold stoppingBudget at hbudget
    omega
  · have hbudget := stopping_exponential_margin i
    have hle : lossBudget i + H + balanceExponent i + 1 ≤
        stoppingBudget i + balanceExponent i + 4 := by
      unfold stoppingBudget
      omega
    have hcast : ((lossBudget i + H + balanceExponent i + 1 : ℕ) : ℝ) ≤
        ((stoppingBudget i + balanceExponent i + 4 : ℕ) : ℝ) := by exact_mod_cast hle
    exact hcast.trans hbudget

/-- In particular, exactly the same indexed family works at both depths.
The depth may be any number up to their maximum, not just the two endpoints. -/
theorem second_interlace_stopping_gates (i : Input) (b : ℕ)
    (hb : b ≤ max (secondDepth i) (tailDepth i)) :
    (3 / 5 : ℝ) ≤
        ((2 : ℝ) ^ (-(b : ℝ)) *
          (2 : ℝ) ^ (-((i.cost + firstExponent i + secondExponent i : ℕ) : ℝ)) /
          (1 + 1 / (100 * (balanceOrder i : ℝ)))) ^
            (1 / (balanceOrder i : ℝ)) ∧
      HardSeed.columnDensity (balanceOrder i : ℝ) ≤
        (2 : ℝ) ^ (-(b : ℝ)) *
          (2 : ℝ) ^ (-((i.cost + firstExponent i + balanceExponent i : ℕ) : ℝ)) /
          (1 + 1 / (100 * (balanceOrder i : ℝ))) := by
  apply all_stopping_gates i (le_refl _) (Nat.le_add_left _ _)
  · apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    have h : b ≤ lossBudget i := by unfold lossBudget; omega
    exact neg_le_neg (by exact_mod_cast h)
  · positivity
  · have ht : (1 : ℝ) ≤ balanceOrder i := by exact_mod_cast balanceOrder_pos i
    apply (div_le_one (by positivity)).2
    linarith

theorem referenceExponent_le_scalePower (i : Input) :
    referenceExponent i ≤ 2 ^ scale i := by
  have h := outerExponent_le_scalePower i
  unfold referenceExponent outerExponent at *
  omega

theorem reference_exponent_margin (i : Input) :
    certificateCost i - 1 + retainedExponent i +
      max (outerExponent i) (referenceExponent i) + 1 ≤ 2 ^ (scale i + 4) := by
  have hC := certificateCost_bound i
  have hL := retainedExponent_power_bound i
  have hq := outerExponent_le_scalePower i
  have ht := referenceExponent_le_scalePower i
  have hp : 0 < 2 ^ scale i := by positivity
  rw [pow_add] at hC ⊢
  norm_num at hC ⊢
  omega

theorem reference_row_margin (i : Input) :
    2 * (certificateCost i - 1 + retainedExponent i + outerExponent i + 1) ≤
      referenceWidth i := by
  have hl := scale_floor i
  norm_num at hl
  have he : scale i + 5 ≤ referenceExponent i := by
    unfold referenceExponent
    nlinarith
  have hp := Nat.pow_le_pow_right (n := 2) (by decide) he
  have hm := reference_exponent_margin i
  rw [show scale i + 5 = (scale i + 4) + 1 by omega, pow_succ] at hp
  change _ ≤ 2 ^ referenceExponent i
  omega

theorem reference_column_margin (i : Input) :
    ((certificateCost i - 1 + retainedExponent i + referenceExponent i + 1 : ℕ) : ℝ) ≤
      (2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt (referenceExponent i : ℝ)) := by
  have hl := scale_floor i
  norm_num at hl
  have hsqrt : Real.sqrt (referenceExponent i : ℝ) = 10 * (scale i : ℝ) := by
    have h : (referenceExponent i : ℝ) = (10 * (scale i : ℝ)) ^ 2 := by
      unfold referenceExponent
      push_cast
      ring
    rw [h, Real.sqrt_sq (by positivity)]
  have hm := reference_exponent_margin i
  have hle : certificateCost i - 1 + retainedExponent i + referenceExponent i + 1 ≤
      2 ^ (scale i + 4) := by omega
  have hcast : ((certificateCost i - 1 + retainedExponent i + referenceExponent i + 1 : ℕ) : ℝ) ≤
      (2 : ℝ) ^ (scale i + 4) := by exact_mod_cast hle
  apply hcast.trans
  rw [← Real.rpow_natCast, hsqrt]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  have hlr : (32 : ℝ) ≤ scale i := by exact_mod_cast (show 32 ≤ scale i by omega)
  push_cast
  linarith

theorem retainedFraction_dyadic_lower (i : Input) :
    (2 : ℝ) ^ (-(retainedExponent i : ℝ)) ≤
      (retainedFraction i : ℚ) := by
  have h := Nat.le_pow_clog (by decide : 1 < 2) (160 * restorationWidth i)
  have hcast : (160 : ℝ) * restorationWidth i ≤ (2 : ℝ) ^ retainedExponent i := by
    exact_mod_cast h
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  change _ ≤ ((1 / (160 * (restorationWidth i : ℚ)) : ℚ) : ℝ)
  push_cast
  simpa only [one_div] using
    one_div_le_one_div_of_le (by have := restorationWidth_pos i; positivity) hcast

set_option maxHeartbeats 600000 in
-- Explicit conversion between rational tolerances and real powers is expensive.
/-- Reference-only calls use their own prescribed width, with zero balance
error and the actual retained fraction, without enlarging that width. -/
theorem reference_stopping_gates (i : Input) :
    (3 / 5 : ℝ) ≤
        (((retainedFraction i : ℚ) : ℝ) *
          (2 : ℝ) ^ (-((certificateCost i - 1 + outerExponent i : ℕ) : ℝ))) ^
            (1 / (referenceWidth i : ℝ)) ∧
      HardSeed.columnDensity (referenceWidth i : ℝ) ≤
        ((retainedFraction i : ℚ) : ℝ) *
          (2 : ℝ) ^ (-((certificateCost i - 1 + referenceExponent i : ℕ) : ℝ)) := by
  have h := localized_stopping_gates (t := referenceWidth i) (m := referenceExponent i)
    (L := retainedExponent i) (H := certificateCost i - 1) (A := outerExponent i)
    (ε := 0) rfl (by norm_num) (by norm_num) (retainedFraction_dyadic_lower i)
    (by simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using reference_row_margin i)
    (by simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using reference_column_margin i)
  simpa only [add_zero, div_one] using h

/-- An exact integer comparison, before taking reciprocals. It keeps the
very small loss estimates free of floating-point approximations. -/
theorem outer_tail_integer_margin (i : Input) :
    i.sourceConstant * bins i * outerWidth i ^ 2 * 2 ^ 40 ≤ 2 ^ tailDepth i := by
  have hc := (public_bounds i).1
  have hs := bins_le_scale_power i
  have ht := tailDepth_polynomial_lower i
  have he : 2 * scale i + 2 * outerExponent i + 40 ≤ tailDepth i := by
    unfold outerExponent
    omega
  calc
    i.sourceConstant * bins i * outerWidth i ^ 2 * 2 ^ 40 ≤
        2 ^ scale i * 2 ^ scale i * (2 ^ outerExponent i) ^ 2 * 2 ^ 40 := by
      change _ ≤ 2 ^ scale i * 2 ^ scale i * outerWidth i ^ 2 * 2 ^ 40
      gcongr
    _ = 2 ^ (2 * scale i + 2 * outerExponent i + 40) := by
      rw [← pow_mul, ← pow_add, ← pow_add, ← pow_add]
      congr 1
      omega
    _ ≤ _ := Nat.pow_le_pow_right (by decide) he

theorem inner_integer_margin (i : Input) :
    2 ^ 100 * i.sourceConstant * bins i * secondWidth i *
      outerWidth i ^ 5 * balanceOrder i ^ 20 ≤ 2 ^ firstDepth i := by
  have hc := (public_bounds i).1
  have hs := bins_le_scale_power i
  have hb := firstDepth_polynomial_lower i
  have he : 100 + 2 * scale i + secondExponent i +
      5 * outerExponent i + 20 * balanceExponent i ≤ firstDepth i := by
    unfold outerExponent
    omega
  calc
    2 ^ 100 * i.sourceConstant * bins i * secondWidth i *
        outerWidth i ^ 5 * balanceOrder i ^ 20 ≤
      2 ^ 100 * 2 ^ scale i * 2 ^ scale i * 2 ^ secondExponent i *
        (2 ^ outerExponent i) ^ 5 * (2 ^ balanceExponent i) ^ 20 := by
      change _ ≤ 2 ^ 100 * 2 ^ scale i * 2 ^ scale i * secondWidth i *
        outerWidth i ^ 5 * balanceOrder i ^ 20
      gcongr
    _ = 2 ^ (100 + 2 * scale i + secondExponent i +
        5 * outerExponent i + 20 * balanceExponent i) := by
      rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
      congr 1
      omega
    _ ≤ _ := Nat.pow_le_pow_right (by decide) he

theorem dyadic_product_bound (n m k : ℕ) (h : m + k ≤ n) :
    (2 : ℝ) ^ m * (2 : ℝ) ^ (-(n : ℝ)) ≤ 1 / (2 : ℝ) ^ k := by
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast, ← div_eq_mul_inv]
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  apply (div_le_div_iff₀ hpos (by positivity : (0 : ℝ) < 2 ^ k)).2
  have hp : (2 : ℝ) ^ (m + k) ≤ 2 ^ n :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h
  simpa only [pow_add, one_mul] using hp

theorem outer_tail_small (i : Input) :
    (outerWidth i : ℝ) * (2 : ℝ) ^ (-(tailDepth i : ℝ)) ≤ 1 / 32768 := by
  have ht := tailDepth_polynomial_lower i
  have he : outerExponent i + 15 ≤ tailDepth i := by
    unfold outerExponent
    omega
  have h := dyadic_product_bound (tailDepth i) (outerExponent i) 15 he
  norm_num only [show (2 : ℝ) ^ (15 : ℕ) = 32768 by norm_num] at h
  simpa only [outerWidth, Nat.cast_pow, Nat.cast_ofNat] using h

theorem bins_le_outerWidth (i : Input) : bins i ≤ outerWidth i := by
  have hl := scale_floor i
  norm_num at hl
  have hb := binExponent_le_scale i
  apply Nat.pow_le_pow_right (by decide)
  change binExponent i ≤ 1000 * scale i ^ 2
  nlinarith

theorem dense_tail_loss (i : Input) :
    (outerWidth i : ℝ) * (2 : ℝ) ^ (-(tailDepth i : ℝ)) ≤ 4 / 25025 ∧
      (bins i : ℝ) * (2 : ℝ) ^ (-(tailDepth i : ℝ)) ≤ 4 / 25025 := by
  have ho := (outer_tail_small i).trans (by norm_num : (1 / 32768 : ℝ) ≤ 4 / 25025)
  refine ⟨ho, ?_⟩
  apply le_trans ?_ ho
  gcongr
  exact_mod_cast bins_le_outerWidth i

theorem accepted_edges_ge_bins (i : Input)
    (hc : 0 < i.sourceConstant) (he : 0 < i.edges) (ha : Accepted i) :
    bins i ≤ i.edges := by
  have hq := bins_le_outerWidth i
  have hs := bins_pos i
  have ht := balanceOrder_pos i
  have hsmall : 24 * bins i * bins i ≤
      2 ^ 40 * i.sourceConstant * bins i * outerWidth i ^ 2 * balanceOrder i ^ 4 := by
    have hp : bins i ≤ outerWidth i ^ 2 := hq.trans
      (by simpa using Nat.pow_le_pow_right (outerWidth_pos i) (by decide : 1 ≤ 2))
    have hc' : (24 : ℕ) ≤ 2 ^ 40 * i.sourceConstant := by norm_num; omega
    calc
      24 * bins i * bins i ≤ (2 ^ 40 * i.sourceConstant) * bins i * outerWidth i ^ 2 := by gcongr
      _ ≤ _ := Nat.le_mul_of_pos_right _ (pow_pos ht _)
  have hlow := hsmall.trans ha.2.2.2
  have hu := (secondWidth_bounds i he).2
  nlinarith

theorem inner_pair_loss (i : Input) :
    2 * (secondWidth i : ℝ) * (2 : ℝ) ^ (-(firstDepth i : ℝ)) ≤ 1 / 8 := by
  have hb := firstDepth_polynomial_lower i
  have he : secondExponent i + 4 ≤ firstDepth i := by omega
  have h := dyadic_product_bound (firstDepth i) (secondExponent i) 4 he
  have hh : (secondWidth i : ℝ) * (2 : ℝ) ^ (-(firstDepth i : ℝ)) ≤ 1 / 16 := by
    simpa only [secondWidth, Nat.cast_pow, Nat.cast_ofNat,
      show (2 : ℝ) ^ (4 : ℕ) = 16 by norm_num] using h
  nlinarith

theorem inner_many_loss (i : Input) :
    2 * (outerWidth i : ℝ) * secondWidth i *
      (2 : ℝ) ^ (-(firstDepth i : ℝ)) ≤ 1 := by
  have hb := firstDepth_polynomial_lower i
  have he : outerExponent i + secondExponent i + 1 ≤ firstDepth i := by
    unfold outerExponent
    omega
  have h := dyadic_product_bound (firstDepth i) (outerExponent i + secondExponent i) 1 he
  have hh : (outerWidth i : ℝ) * secondWidth i *
      (2 : ℝ) ^ (-(firstDepth i : ℝ)) ≤ 1 / 2 := by
    simpa only [outerWidth, secondWidth, Nat.cast_pow, Nat.cast_ofNat, pow_add, pow_one] using h
  nlinarith

theorem sampling_row_request (i : Input) :
    (balanceOrder i : ℝ) * (2 : ℝ) ^ (-(firstDepth i : ℝ)) ≤ 1 := by
  have hb := firstDepth_polynomial_lower i
  have he : balanceExponent i + 0 ≤ firstDepth i := by omega
  have h := dyadic_product_bound (firstDepth i) (balanceExponent i) 0 he
  simpa only [balanceOrder, Nat.cast_pow, Nat.cast_ofNat, pow_zero, div_one] using h

theorem reference_row_request (i : Input) :
    (referenceWidth i : ℝ) * (2 : ℝ) ^ (-(tailDepth i : ℝ)) ≤ 1 := by
  have hb := tailDepth_polynomial_lower i
  have he : referenceExponent i + 0 ≤ tailDepth i := by
    unfold referenceExponent
    omega
  have h := dyadic_product_bound (tailDepth i) (referenceExponent i) 0 he
  simpa only [referenceWidth, Nat.cast_pow, Nat.cast_ofNat, pow_zero, div_one] using h

theorem hard_seed_exponent_domains (i : Input) :
    2 ^ 20 ≤ balanceExponent i ∧ 2 ^ 20 ≤ referenceExponent i ∧
      2 ^ 20 ≤ firstExponent i - 1 ∧ 2 ^ 20 ≤ binExponent i - 2 := by
  have hl := scale_floor i
  have hu := auxiliaryLog_floor i
  norm_num at hl
  have hscale4 : 1 ≤ scale i ^ 4 := one_le_pow₀ (by omega)
  have hscaleSq : scale i ≤ scale i ^ 2 := by nlinarith
  have hbs : 2 ^ 20 + 2 ≤ binExponent i := by unfold binExponent; nlinarith
  have hfirst : 2 ^ 20 + 1 ≤ firstExponent i := by unfold firstExponent; nlinarith
  refine ⟨?_, ?_, by omega, by omega⟩
  · unfold balanceExponent
    norm_num
    omega
  · unfold referenceExponent
    norm_num
    nlinarith

theorem two_copy_balance_error (i : Input) :
    0 ≤ 2 * (1 / (100 * (balanceOrder i : ℝ))) +
      (1 / (100 * (balanceOrder i : ℝ))) ^ 2 ∧
      2 * (1 / (100 * (balanceOrder i : ℝ))) +
        (1 / (100 * (balanceOrder i : ℝ))) ^ 2 ≤ 1 := by
  have ht : (1 : ℝ) ≤ balanceOrder i := by exact_mod_cast balanceOrder_pos i
  have hε0 : 0 ≤ 1 / (100 * (balanceOrder i : ℝ)) := by positivity
  have hε : 1 / (100 * (balanceOrder i : ℝ)) ≤ 1 / 100 := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  constructor
  · positivity
  · nlinarith [sq_nonneg (1 / 100 - 1 / (100 * (balanceOrder i : ℝ)))]

/-- The two-copy joint-family call, with the error of two independent
balanced factors written literally. -/
theorem two_copy_stopping_gates (i : Input) :
    let ε := 2 * (1 / (100 * (balanceOrder i : ℝ))) +
      (1 / (100 * (balanceOrder i : ℝ))) ^ 2
    (3 / 5 : ℝ) ≤
        ((49 / 64 : ℝ) *
          (2 : ℝ) ^ (-((i.cost + firstExponent i + (secondExponent i + 1) : ℕ) : ℝ)) /
          (1 + ε)) ^ (1 / (balanceOrder i : ℝ)) ∧
      HardSeed.columnDensity (balanceOrder i : ℝ) ≤
        (49 / 64 : ℝ) *
          (2 : ℝ) ^ (-((i.cost + firstExponent i + balanceExponent i : ℕ) : ℝ)) /
          (1 + ε) := by
  dsimp only
  apply all_stopping_gates i (le_refl _) ?_ ?_
    (two_copy_balance_error i).1 (two_copy_balance_error i).2
  · have hl := scale_floor i
    norm_num at hl
    unfold outerExponent
    nlinarith
  · have hL : 1 ≤ lossBudget i := by unfold lossBudget; omega
    have hcast : (1 : ℝ) ≤ lossBudget i := by exact_mod_cast hL
    calc
      (2 : ℝ) ^ (-(lossBudget i : ℝ)) ≤ (2 : ℝ) ^ (-(1 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ ≤ 49 / 64 := by norm_num [Real.rpow_neg_one]

theorem firstWidth_le_outerWidth (i : Input) : firstWidth i ≤ outerWidth i := by
  apply (Nat.sub_le _ _).trans
  apply Nat.pow_le_pow_right (by decide)
  change 256 * scale i ^ 2 ≤ 1000 * scale i ^ 2
  omega

theorem accepted_graph_item_room (i : Input)
    (ha : Accepted i) :
    64 * i.sourceConstant * bins i * firstWidth i ≤ secondWidth i := by
  have hq := firstWidth_le_outerWidth i
  have hq2 : firstWidth i ≤ outerWidth i ^ 2 := hq.trans
    (by simpa using Nat.pow_le_pow_right (outerWidth_pos i) (by decide : 1 ≤ 2))
  have ht : 1 ≤ balanceOrder i ^ 4 := pow_pos (balanceOrder_pos i) _
  calc
    64 * i.sourceConstant * bins i * firstWidth i ≤
        2 ^ 40 * i.sourceConstant * bins i * outerWidth i ^ 2 := by
      gcongr
      norm_num
    _ ≤ 2 ^ 40 * i.sourceConstant * bins i * outerWidth i ^ 2 * balanceOrder i ^ 4 :=
      Nat.le_mul_of_pos_right _ ht
    _ ≤ secondWidth i := ha.2.2.2

theorem block_ratio_strict {T q v α : ℝ}
    (hT : 64 ≤ T) (hq : T - 2 ≤ q) (hv : 0 < v) (hv1 : v ≤ 1)
    (hα0 : 0 < α) (hα : α ≤ v / 256) :
    α < (3 / 5 : ℝ) * v ∧
      9 * T * v / 16 < q * (((3 / 5 : ℝ) * v - α) / (1 - α)) := by
  have hα1 : α < 1 := by linarith
  have hnum : 0 < (3 / 5 : ℝ) * v - α := by linarith
  have hratio : (3 / 5 : ℝ) * v - α ≤
      ((3 / 5 : ℝ) * v - α) / (1 - α) := by
    apply (le_div_iff₀ (by linarith : 0 < 1 - α)).2
    nlinarith
  have hq0 : 0 ≤ q := by linarith
  have hfirst : (T - 2) * ((3 / 5 : ℝ) * v - v / 256) ≤
      q * (((3 / 5 : ℝ) * v - α) / (1 - α)) := by
    apply le_trans (mul_le_mul_of_nonneg_left (by linarith :
      (3 / 5 : ℝ) * v - v / 256 ≤ (3 / 5 : ℝ) * v - α) (by linarith))
    exact (mul_le_mul_of_nonneg_right hq hnum.le).trans
      (mul_le_mul_of_nonneg_left hratio hq0)
  constructor
  · linarith
  · have hmargin : 0 < ((43 * T - 1526) / 1280) * v := by
      apply mul_pos _ hv
      linarith
    nlinarith

theorem pow_sub_mul_negative {a j : ℕ} (hj : j ≤ a) :
    (2 : ℝ) ^ (a - j) = (2 : ℝ) ^ a * (2 : ℝ) ^ (-(j : ℝ)) := by
  rw [← Real.rpow_natCast, Nat.cast_sub hj, sub_eq_add_neg,
    Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast]

theorem depth_fraction {a b : ℕ} (h : a + 8 ≤ b) :
    (2 : ℝ) ^ a * (2 : ℝ) ^ (-(b : ℝ)) ≤ 1 / 256 := by
  rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  have hh : (a : ℝ) + -(b : ℝ) ≤ -8 := by
    have hc : (a : ℝ) + 8 ≤ b := by exact_mod_cast h
    linarith
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hh
  norm_num [Real.rpow_neg] at hp
  exact hp

theorem extraction_alpha {a b j : ℕ} (hj : j ≤ a) (hdepth : a + 8 ≤ b) :
    0 < (2 : ℝ) ^ (a - j) * (2 : ℝ) ^ (-(b : ℝ)) ∧
      (2 : ℝ) ^ (a - j) * (2 : ℝ) ^ (-(b : ℝ)) ≤
        (2 : ℝ) ^ (-(j : ℝ)) / 256 := by
  constructor
  · positivity
  · rw [pow_sub_mul_negative hj]
    calc
      (2 : ℝ) ^ a * (2 : ℝ) ^ (-(j : ℝ)) * (2 : ℝ) ^ (-(b : ℝ)) =
          ((2 : ℝ) ^ a * (2 : ℝ) ^ (-(b : ℝ))) * (2 : ℝ) ^ (-(j : ℝ)) := by ring
      _ ≤ (1 / 256 : ℝ) * (2 : ℝ) ^ (-(j : ℝ)) :=
        mul_le_mul_of_nonneg_right (depth_fraction hdepth) (by positivity)
      _ = _ := by ring

theorem extraction_block_gate {a b j q : ℕ} (ha : 6 ≤ a) (hj : j ≤ 1)
    (hdepth : a + 8 ≤ b) (hq : 2 ^ a - 2 ≤ q) :
    0 < (2 : ℝ) ^ (a - j) * (2 : ℝ) ^ (-(b : ℝ)) ∧
    (2 : ℝ) ^ (a - j) * (2 : ℝ) ^ (-(b : ℝ)) <
      (3 / 5 : ℝ) * (2 : ℝ) ^ (-(j : ℝ)) ∧
    9 * 2 ^ (a - j) / 16 ≤
      ⌈(q : ℝ) * (((3 / 5 : ℝ) * (2 : ℝ) ^ (-(j : ℝ)) -
        (2 : ℝ) ^ (a - j) * (2 : ℝ) ^ (-(b : ℝ))) /
        (1 - (2 : ℝ) ^ (a - j) * (2 : ℝ) ^ (-(b : ℝ))))⌉₊ := by
  have hja : j ≤ a := by omega
  have hα := extraction_alpha hja hdepth
  have hT : (64 : ℝ) ≤ (2 : ℝ) ^ a := by
    exact_mod_cast (show 64 ≤ 2 ^ a from (by norm_num : 64 = 2 ^ 6) ▸
      Nat.pow_le_pow_right (by decide) ha)
  have hp2 : 2 ≤ 2 ^ a := by have := Nat.pow_le_pow_right (n := 2) (by decide) ha; norm_num at this; omega
  have hqr : (2 : ℝ) ^ a - 2 ≤ q := by
    have hc : (2 : ℝ) ^ a ≤ (q : ℝ) + 2 := by
      exact_mod_cast (by omega : (2 ^ a : ℕ) ≤ q + 2)
    linarith
  have hv1 : (2 : ℝ) ^ (-(j : ℝ)) ≤ 1 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show -(j : ℝ) ≤ 0 by simp)
    simpa using h
  have hb := block_ratio_strict hT hqr (by positivity) hv1 hα.1 hα.2
  refine ⟨hα.1, hb.1, ?_⟩
  have hreal : (9 * 2 ^ (a - j) / 16 : ℕ) ≤
      9 * (2 : ℝ) ^ a * (2 : ℝ) ^ (-(j : ℝ)) / 16 := by
    calc
      ((9 * 2 ^ (a - j) / 16 : ℕ) : ℝ) ≤ (9 * (2 : ℝ) ^ (a - j)) / 16 := by
        apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).2
        exact_mod_cast (Nat.div_mul_le_self (9 * 2 ^ (a - j)) 16)
      _ = _ := by rw [pow_sub_mul_negative hja]; ring
  exact_mod_cast hreal.trans (hb.2.le.trans (Nat.le_ceil _))

theorem first_extraction_gate (i : Input) (ha : Accepted i) (j : ℕ) (hj : j ≤ 1) :
    0 < (2 : ℝ) ^ (firstExponent i - j) * (2 : ℝ) ^ (-(i.incomingDepth : ℝ)) ∧
    (2 : ℝ) ^ (firstExponent i - j) * (2 : ℝ) ^ (-(i.incomingDepth : ℝ)) <
      (3 / 5 : ℝ) * (2 : ℝ) ^ (-(j : ℝ)) ∧
    9 * 2 ^ (firstExponent i - j) / 16 ≤
      ⌈(firstWidth i : ℝ) * (((3 / 5 : ℝ) * (2 : ℝ) ^ (-(j : ℝ)) -
        (2 : ℝ) ^ (firstExponent i - j) * (2 : ℝ) ^ (-(i.incomingDepth : ℝ))) /
        (1 - (2 : ℝ) ^ (firstExponent i - j) * (2 : ℝ) ^ (-(i.incomingDepth : ℝ))))⌉₊ := by
  have hb : 6 ≤ binExponent i := by
    have h := auxiliaryLog_floor i
    unfold binExponent
    nlinarith
  have he : 6 ≤ firstExponent i := by
    have h := scale_floor i
    norm_num at h
    unfold firstExponent
    nlinarith
  exact extraction_block_gate he hj (by have := ha.2.2.1; omega) (le_refl _)

theorem first_alpha_bounds (i : Input) (ha : Accepted i) (j : ℕ) (hj : j ≤ 1) :
    0 < (2 : ℝ) ^ (firstExponent i - j) * (2 : ℝ) ^ (-(i.incomingDepth : ℝ)) ∧
      (2 : ℝ) ^ (firstExponent i - j) * (2 : ℝ) ^ (-(i.incomingDepth : ℝ)) ≤
        (2 : ℝ) ^ (-(j : ℝ)) / 256 := by
  have hb : 6 ≤ binExponent i := by
    have h := auxiliaryLog_floor i
    unfold binExponent
    nlinarith
  have he : 6 ≤ firstExponent i := by
    have h := scale_floor i
    norm_num at h
    unfold firstExponent
    nlinarith
  exact extraction_alpha (by omega) (by have := ha.2.2.1; omega)

theorem strict_product_projection {L p y : ℕ} {χ z : ℝ}
    (hy : 0 < y) (hp : p ≤ L) (hχ : 0 < χ) (hχz : χ ≤ z) :
    ((⌈(y : ℝ) ^ p * χ⌉₊ : ℝ) - 1) * (y : ℝ) ^ (L - p) <
      ⌈(y : ℝ) ^ L * z⌉₊ := by
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ (y : ℝ) ^ p * χ by positivity)
  calc
    ((⌈(y : ℝ) ^ p * χ⌉₊ : ℝ) - 1) * (y : ℝ) ^ (L - p) <
        ((y : ℝ) ^ p * χ) * (y : ℝ) ^ (L - p) :=
      mul_lt_mul_of_pos_right (by linarith) (by positivity)
    _ = (y : ℝ) ^ L * χ := by
      rw [mul_right_comm, ← pow_add, Nat.add_sub_of_le hp]
    _ ≤ (y : ℝ) ^ L * z := mul_le_mul_of_nonneg_left hχz (by positivity)
    _ ≤ ⌈(y : ℝ) ^ L * z⌉₊ := Nat.le_ceil _

theorem second_exponent_floor (i : Input) (hc : 0 < i.sourceConstant)
    (ha : Accepted i) : 6 ≤ secondExponent i := by
  have h := accepted_secondWidth_ge_9216_bins i hc ha
  have hs := bins_pos i
  by_contra he
  have he5 : secondExponent i ≤ 5 := by omega
  have hp := Nat.pow_le_pow_right (n := 2) (by decide) he5
  change secondWidth i ≤ 2 ^ 5 at hp
  norm_num at hp
  omega

theorem second_extraction_gate (i : Input) (hc : 0 < i.sourceConstant)
    (ha : Accepted i) (j : ℕ) (hj : j ≤ 1) :
    0 < (2 : ℝ) ^ (secondExponent i - j) * (2 : ℝ) ^ (-(firstDepth i : ℝ)) ∧
    (2 : ℝ) ^ (secondExponent i - j) * (2 : ℝ) ^ (-(firstDepth i : ℝ)) <
      (3 / 5 : ℝ) * (2 : ℝ) ^ (-(j : ℝ)) ∧
    9 * 2 ^ (secondExponent i - j) / 16 ≤
      ⌈(secondWidth i : ℝ) * (((3 / 5 : ℝ) * (2 : ℝ) ^ (-(j : ℝ)) -
        (2 : ℝ) ^ (secondExponent i - j) * (2 : ℝ) ^ (-(firstDepth i : ℝ))) /
        (1 - (2 : ℝ) ^ (secondExponent i - j) * (2 : ℝ) ^ (-(firstDepth i : ℝ))))⌉₊ := by
  apply extraction_block_gate (second_exponent_floor i hc ha) hj
  · have h := firstDepth_polynomial_lower i
    omega
  · exact Nat.sub_le _ _

theorem second_alpha_bounds (i : Input) (hc : 0 < i.sourceConstant)
    (ha : Accepted i) (j : ℕ) (hj : j ≤ 1) :
    0 < (2 : ℝ) ^ (secondExponent i - j) * (2 : ℝ) ^ (-(firstDepth i : ℝ)) ∧
      (2 : ℝ) ^ (secondExponent i - j) * (2 : ℝ) ^ (-(firstDepth i : ℝ)) ≤
        (2 : ℝ) ^ (-(j : ℝ)) / 256 := by
  have hr := second_exponent_floor i hc ha
  have hb := firstDepth_polynomial_lower i
  exact extraction_alpha (by omega) (by omega)

theorem first_column_projection_gate (i : Input) (ha : Accepted i)
    (j : ℕ) (hj : j ≤ 1) :
    ((⌈(i.columns : ℝ) ^ (9 * 2 ^ (firstExponent i - j) / 16) *
        HardSeed.columnDensity ((2 : ℝ) ^ (firstExponent i - j))⌉₊ : ℝ) - 1) *
        (i.columns : ℝ) ^ (firstLength i - 9 * 2 ^ (firstExponent i - j) / 16) <
      ⌈(i.columns : ℝ) ^ firstLength i * (2 : ℝ) ^ (-(firstDepth i : ℝ))⌉₊ := by
  have hs : 2 ≤ bins i := by
    have h := Nat.le_of_dvd (bins_pos i) (sixtyfour_dvd_bins i)
    omega
  have he := firstWidth_pos i
  have hpow : 2 ^ (firstExponent i - j) ≤ 2 ^ firstExponent i :=
    Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  have hp : 9 * 2 ^ (firstExponent i - j) / 16 ≤ 2 ^ (firstExponent i - j) := by
    apply (Nat.div_le_iff_le_mul_add_pred (by decide : 0 < 16)).2
    omega
  apply strict_product_projection (by have := ha.2.1; omega) _
    (HardSeed.columnDensity_pos _) (first_chi_gate i j hj)
  unfold firstLength firstWidth
  omega

noncomputable def denseFraction (s N : ℕ) (x : ℝ) : ℝ :=
  ((⌈(999 / 1000 : ℝ) * N⌉₊ : ℝ) -
    ((s - 1 : ℕ) : ℝ) * ⌈2 * x * N⌉₊) / N

/-- Rounding an actual bin size loses less than one thousandth of a bin. -/
theorem dense_ceiling_loss {s N : ℕ} {x : ℝ}
    (hs : 0 < s) (hN : 9216 * s ≤ N) (hx : 0 ≤ x)
    (hloss : (s : ℝ) * x ≤ 4 / 25025) :
    (s : ℝ) * (⌈2 * x * N⌉₊ : ℝ) < (N : ℝ) / 1000 := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hNR : (9216 : ℝ) * s ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by nlinarith
  have hc := Nat.ceil_lt_add_one (R := ℝ) (show 0 ≤ 2 * x * N by positivity)
  have hc' := mul_lt_mul_of_pos_left hc hsR
  have hprod := mul_le_mul_of_nonneg_right hloss hNpos.le
  nlinarith

theorem dense_fraction_lower {s N : ℕ} {x : ℝ}
    (hs : 0 < s) (hN : 9216 * s ≤ N) (hx : 0 ≤ x)
    (hloss : (s : ℝ) * x ≤ 4 / 25025) :
    (998 / 1000 : ℝ) ≤ denseFraction s N x := by
  have hNpos : (0 : ℝ) < N := by
    have hNR : (9216 : ℝ) * s ≤ N := by exact_mod_cast hN
    have hsR : (0 : ℝ) < s := by exact_mod_cast hs
    nlinarith
  have hceil := Nat.le_ceil ((999 / 1000 : ℝ) * N)
  have hsmall := dense_ceiling_loss hs hN hx hloss
  have hsub : ((s - 1 : ℕ) : ℝ) ≤ (s : ℝ) := by exact_mod_cast Nat.sub_le s 1
  have hmul := mul_le_mul_of_nonneg_right hsub
    (show (0 : ℝ) ≤ (⌈2 * x * N⌉₊ : ℝ) by positivity)
  unfold denseFraction
  apply (le_div_iff₀ hNpos).2
  linarith

theorem dense_strict_separation {s N : ℕ} {x : ℝ}
    (hs : 0 < s) (hN : 9216 * s ≤ N) (hx : 0 ≤ x)
    (hloss : (s : ℝ) * x ≤ 4 / 25025) :
    s * ⌈2 * x * N⌉₊ < ⌈(999 / 1000 : ℝ) * N⌉₊ := by
  have hl := dense_ceiling_loss hs hN hx hloss
  have hn : (0 : ℝ) < N := by
    have hNR : (9216 : ℝ) * s ≤ N := by exact_mod_cast hN
    have hsR : (0 : ℝ) < s := by exact_mod_cast hs
    nlinarith
  have hc := Nat.le_ceil ((999 / 1000 : ℝ) * N)
  have hr : (s : ℝ) * (⌈2 * x * N⌉₊ : ℝ) <
      (⌈(999 / 1000 : ℝ) * N⌉₊ : ℝ) := by linarith
  exact_mod_cast hr

theorem dense_fraction_balance {d ε : ℝ}
    (hd : (998 / 1000 : ℝ) ≤ d) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 100) :
    (499 / 1010 : ℝ) ≤ (d / 2) / (1 + ε) ∧
      (49 / 100 : ℝ) < (d / 2) / (1 + ε) := by
  have h : (499 / 1010 : ℝ) ≤ (d / 2) / (1 + ε) := by
    apply (le_div_iff₀ (by linarith : (0 : ℝ) < 1 + ε)).2
    nlinarith
  exact ⟨h, lt_of_lt_of_le (by norm_num) h⟩

/-- Two requested rounded pieces fit in the same physical bin. -/
theorem two_copy_ceiling {N : ℕ} {τ : ℝ}
    (hN : 100 ≤ N) (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1 / 100) :
    2 * ⌈τ * N⌉₊ ≤ N := by
  have hNR : (100 : ℝ) ≤ N := by exact_mod_cast hN
  have hc := Nat.ceil_lt_add_one (R := ℝ) (show 0 ≤ τ * N by positivity)
  have hprod := mul_le_mul_of_nonneg_right hτ (show (0 : ℝ) ≤ N by positivity)
  have hr : 2 * (⌈τ * N⌉₊ : ℝ) ≤ N := by nlinarith
  exact_mod_cast hr

/-- The regular-quotient completion estimate at the physical template density. -/
theorem pair_completion_fraction {ρ lam : ℝ}
    (hρ : (99 / 100 : ℝ) ≤ ρ) (hlam : (99 / 100 : ℝ) ≤ lam) :
    (9701 / 9801 : ℝ) ≤ (ρ + lam ^ 2 - 1) / lam ^ 2 := by
  have hsq : (9801 / 10000 : ℝ) ≤ lam ^ 2 := by nlinarith
  apply (le_div_iff₀ (by nlinarith : (0 : ℝ) < lam ^ 2)).2
  nlinarith

theorem two_copy_retained_quotient {a τ ε : ℝ}
    (ha : (9701 / 9801 : ℝ) ≤ a) (hτ : τ ≤ 1 / 100)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 100) :
    (96029900 / 99980001 : ℝ) ≤ (a - τ) / (1 + ε) ^ 2 ∧
      (49 / 64 : ℝ) < (a - τ) / (1 + ε) ^ 2 := by
  have he : (1 + ε) ^ 2 ≤ (10201 / 10000 : ℝ) := by nlinarith
  have hpos : (0 : ℝ) < (1 + ε) ^ 2 := by positivity
  have h : (96029900 / 99980001 : ℝ) ≤ (a - τ) / (1 + ε) ^ 2 := by
    apply (le_div_iff₀ hpos).2
    nlinarith
  exact ⟨h, lt_of_lt_of_le (by norm_num) h⟩

/-- The real fractional-loss test charges the extra unit from a physical ceiling. -/
theorem owner_ceiling_budget {q R x η : ℝ}
    (hR : 0 < R) (hx : 0 ≤ x)
    (hb : 2 * q ^ 2 * x + q ^ 2 / R ≤ η / 128) :
    q ^ 2 * (⌈2 * x * R⌉₊ : ℝ) / R ≤ η / 128 := by
  have hc := Nat.ceil_lt_add_one (R := ℝ) (show 0 ≤ 2 * x * R by positivity)
  have hm := mul_le_mul_of_nonneg_left hc.le (sq_nonneg q)
  have hd := div_le_div_of_nonneg_right hm hR.le
  have he : q ^ 2 * (2 * x * R + 1) / R = 2 * q ^ 2 * x + q ^ 2 / R := by
    field_simp
  exact hd.trans (he ▸ hb)

/-- All three owner-survival tests, preserving the actual reference proportion. -/
theorem owner_initial_survival {q m R A g η δ : ℝ}
    (hq : 1 ≤ q) (hm : 0 < m) (hg : 0 < g) (hg1 : g ≤ 1)
    (hR : R = g * m) (hA : 0 ≤ A) (hη : 0 ≤ η)
    (hbudget : q ^ 2 * A / R ≤ η / 128)
    (hδ : δ * q = η / 16) (hmargin : η / 8 ≤ g) :
    q * A / m ≤ η / 16 ∧
      q * A + δ * q * m ≤ R ∧
      q * (q - 1) * A / R ≤ η / (16 * g) := by
  have hRpos : 0 < R := by rw [hR]; positivity
  have hq0 : 0 ≤ q := by linarith
  have hqsmall : q * A ≤ q ^ 2 * A :=
    mul_le_mul_of_nonneg_right (by nlinarith : q ≤ q ^ 2) hA
  have hb := (div_le_iff₀ hRpos).1 hbudget
  have hbase : q * A / m ≤ η / 128 := by
    apply (div_le_iff₀ hm).2
    have hηg : η * g ≤ η := mul_le_of_le_one_right hη hg1
    rw [hR] at hb
    have hp := mul_le_mul_of_nonneg_right hηg hm.le
    nlinarith
  refine ⟨by linarith, ?_, ?_⟩
  · have hh := (div_le_iff₀ hm).1 hbase
    have hgm := mul_le_mul_of_nonneg_right hmargin hm.le
    rw [hR, hδ]
    nlinarith
  · have hprod : q * (q - 1) * A ≤ q ^ 2 * A := by nlinarith
    have hleft := (div_le_div_of_nonneg_right hprod hRpos.le).trans hbudget
    have hright : η / 128 ≤ η / (16 * g) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 16 * g)).2
      have hp := mul_le_of_le_one_right hη hg1
      nlinarith
    exact hleft.trans hright

open Parameters

/-- Integer margins control both the fractional loss and the rounding term. -/
theorem owner_budget_from_integer_margins {c s q P R : ℝ}
    (hcs : 0 < c * s) (hP : 0 < P) (hR : 0 < R)
    (hmP : 1024 * c * s * q ^ 2 ≤ P)
    (hmR : 1024 * c * s * q ^ 2 ≤ R) :
    2 * q ^ 2 / P + q ^ 2 / R ≤ (1 / (c * s)) / 128 := by
  have hden : 0 < 1024 * c * s := by nlinarith
  have hleft : q ^ 2 / P ≤ 1 / (1024 * c * s) := by
    apply (div_le_div_iff₀ hP hden).2
    nlinarith
  have hright : q ^ 2 / R ≤ 1 / (1024 * c * s) := by
    apply (div_le_div_iff₀ hR hden).2
    nlinarith
  have he : 1 / (1024 * c * s) = (1 / (c * s)) / 1024 := by ring
  rw [he] at hleft hright
  have hn : (0 : ℝ) ≤ 1 / (c * s) := by positivity
  have hdist : 2 * q ^ 2 / P = 2 * (q ^ 2 / P) := by ring
  rw [hdist]
  linarith

theorem actualFamily_dense_fraction (i : Input) (hc : 0 < i.sourceConstant)
    (ha : Accepted i) :
    (998 / 1000 : ℝ) ≤ denseFraction (bins i)
      (PrimeSampler.size (secondWidth i) (balanceOrder i) (firstWidth i * i.rows))
      ((2 : ℝ) ^ (-(tailDepth i : ℝ))) := by
  exact dense_fraction_lower (bins_pos i)
    (ParameterGates.actualFamily_size_ge_9216_bins i hc ha)
    (Real.rpow_nonneg (by norm_num) _) (dense_tail_loss i).2

theorem actualFamily_dense_strict_separation (i : Input)
    (hc : 0 < i.sourceConstant) (ha : Accepted i) :
    bins i *
      ⌈2 * (2 : ℝ) ^ (-(tailDepth i : ℝ)) *
        PrimeSampler.size (secondWidth i) (balanceOrder i) (firstWidth i * i.rows)⌉₊ <
      ⌈(999 / 1000 : ℝ) *
        PrimeSampler.size (secondWidth i) (balanceOrder i) (firstWidth i * i.rows)⌉₊ := by
  exact dense_strict_separation (bins_pos i)
    (ParameterGates.actualFamily_size_ge_9216_bins i hc ha)
    (Real.rpow_nonneg (by norm_num) _) (dense_tail_loss i).2

/-- The actual accepted formulas discharge the ceiling-adjusted owner budget
for every physical reference row count at least `q2^2`. -/
theorem actual_owner_loss_budget (i : Input) (hc : 0 < i.sourceConstant)
    (ha : Accepted i) (N : ℕ) (hN : secondWidth i ^ 2 ≤ N) :
    2 * (outerWidth i : ℝ) ^ 2 * (2 : ℝ) ^ (-(tailDepth i : ℝ)) +
      (outerWidth i : ℝ) ^ 2 / N ≤ ((rowTolerance i : ℚ) : ℝ) / 128 := by
  have hs := bins_pos i
  have hq := outerWidth_pos i
  have ht := balanceOrder_pos i
  have hq2 := secondWidth_pos i
  have htNat : 1024 * i.sourceConstant * bins i * outerWidth i ^ 2 ≤
      2 ^ tailDepth i := by
    apply le_trans ?_ (ParameterGates.outer_tail_integer_margin i)
    calc
      1024 * i.sourceConstant * bins i * outerWidth i ^ 2 ≤
          2 ^ 40 * i.sourceConstant * bins i * outerWidth i ^ 2 := by
        gcongr
        norm_num
      _ = _ := by ring
  have hgraph : 1024 * i.sourceConstant * bins i * outerWidth i ^ 2 ≤ secondWidth i := by
    calc
      1024 * i.sourceConstant * bins i * outerWidth i ^ 2 ≤
          2 ^ 40 * i.sourceConstant * bins i * outerWidth i ^ 2 := by
        gcongr
        norm_num
      _ ≤
          2 ^ 40 * i.sourceConstant * bins i * outerWidth i ^ 2 * balanceOrder i ^ 4 := by
        exact Nat.le_mul_of_pos_right _ (pow_pos ht _)
      _ ≤ _ := ha.2.2.2
  have hNmargin : 1024 * i.sourceConstant * bins i * outerWidth i ^ 2 ≤ N := by
    apply hgraph.trans
    apply le_trans ?_ hN
    simpa using (Nat.pow_le_pow_right hq2 (by decide : 1 ≤ 2))
  have hNR : (0 : ℝ) < N := by
    have hn : 0 < N := (pow_pos hq2 _).trans_le hN
    exact_mod_cast hn
  have h := owner_budget_from_integer_margins
    (c := (i.sourceConstant : ℝ)) (s := (bins i : ℝ))
    (q := (outerWidth i : ℝ)) (P := ((2 : ℝ) ^ tailDepth i)) (R := (N : ℝ))
    (by positivity) (by positivity) hNR (by exact_mod_cast htNat) (by exact_mod_cast hNmargin)
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  unfold rowTolerance
  push_cast
  convert h using 1

theorem actual_owner_ceiling_budget (i : Input) (hc : 0 < i.sourceConstant)
    (ha : Accepted i) (N : ℕ) (hN : secondWidth i ^ 2 ≤ N) :
    (outerWidth i : ℝ) ^ 2 *
      (⌈2 * (2 : ℝ) ^ (-(tailDepth i : ℝ)) * N⌉₊ : ℝ) / N ≤
      ((rowTolerance i : ℚ) : ℝ) / 128 := by
  apply owner_ceiling_budget
  · have hn : 0 < N := (pow_pos (secondWidth_pos i) _).trans_le hN
    exact_mod_cast hn
  · positivity
  · exact actual_owner_loss_budget i hc ha N hN

end EthInapproximability.CurrentPaper.ParameterGates
