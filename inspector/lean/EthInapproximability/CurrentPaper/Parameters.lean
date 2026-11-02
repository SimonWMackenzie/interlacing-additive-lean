import Mathlib

/-!
# Literal parameters of the current replacement paper

Source: v8 `sections/F-parameter-choices.tex`,
`eq:paper-parameter-scale`--`eq:paper-tail-graph`.

These are the new single-scale formulas, not the previous route's searches.
All integer definitions are computable. Rational tolerances are kept exact.
This module proves a bounded arithmetic block; it does not assert that the
protocol-dependent conditions or all real-valued stopping conditions hold.
-/

namespace EthInapproximability.CurrentPaper.Parameters

/-- Public numerical data; no graph promise or proof of hardness is stored. -/
structure Input where
  sourceConstant : ℕ
  nextDepth : ℕ
  cost : ℕ
  rows : ℕ
  columns : ℕ
  edges : ℕ
  incomingDepth : ℕ

def namingLength (i : Input) : ℕ := max (Nat.clog 2 i.rows) (Nat.clog 2 i.columns)
def scaleBound (i : Input) : ℕ :=
  max i.sourceConstant (max i.nextDepth (max i.cost
    (max (namingLength i) (max (Nat.clog 2 (i.edges + 2)) 2))))
def scale (i : Input) : ℕ := max (2 ^ 24) (Nat.clog 2 (scaleBound i))
def auxiliaryLog (i : Input) : ℕ := Nat.clog 2 (scale i)
def firstExponent (i : Input) : ℕ := 256 * scale i ^ 2
def binExponent (i : Input) : ℕ := 10000 * auxiliaryLog i ^ 2
def bins (i : Input) : ℕ := 2 ^ binExponent i
def firstWidth (i : Input) : ℕ := 2 ^ firstExponent i - 2
def firstLength (i : Input) : ℕ := firstWidth i + bins i + 1
def firstDepth (i : Input) : ℕ := 2 ^ (7 * scale i)
def tailDepth (i : Input) : ℕ := 2 ^ (40 * auxiliaryLog i)
def secondExponent (i : Input) : ℕ := Nat.clog 2 (12 * bins i * i.edges)
def secondWidth (i : Input) : ℕ := 2 ^ secondExponent i
def secondDepth (i : Input) : ℕ := Nat.clog 2 (32 * bins i * firstWidth i * i.rows) + 6
def balanceExponent (i : Input) : ℕ := 100000000 * scale i ^ 4
def balanceOrder (i : Input) : ℕ := 2 ^ balanceExponent i
def outerExponent (i : Input) : ℕ := 1000 * scale i ^ 2
def outerWidth (i : Input) : ℕ := 2 ^ outerExponent i
def referenceExponent (i : Input) : ℕ := 100 * scale i ^ 2
def referenceWidth (i : Input) : ℕ := 2 ^ referenceExponent i
def rowTolerance (i : Input) : ℚ := 1 / (i.sourceConstant * bins i : ℕ)
def columnTolerance (i : Input) : ℚ := 2 / (i.sourceConstant * bins i : ℕ)
def columnLoss (i : Input) : ℚ := rowTolerance i / (16 * outerWidth i)
/-- `80 b⁺ / δ_U = 1280 b⁺ c_src s q` when the public inputs are positive. -/
def restorationTarget (i : Input) : ℕ :=
  1280 * i.nextDepth * i.sourceConstant * bins i * outerWidth i
def restorationExponent (i : Input) : ℕ := Nat.clog 2 (restorationTarget i)
def restorationWidth (i : Input) : ℕ := 2 ^ restorationExponent i
def retainedFraction (i : Input) : ℚ := 1 / (160 * restorationWidth i)
def retainedExponent (i : Input) : ℕ := Nat.clog 2 (160 * restorationWidth i)
def balanceError (i : Input) : ℚ := 1 / (100 * balanceOrder i)

/-- Exactly the matrix-domain checks and two integer acceptance tests.
Positivity of the public source constant and next depth is a separate input
domain condition, not a fabricated extra acceptance test. -/
def Accepted (i : Input) : Prop :=
  2 ≤ i.rows ∧ 2 ≤ i.columns ∧
  firstExponent i + 2 + binExponent i ≤ i.incomingDepth ∧
  2 ^ 40 * i.sourceConstant * bins i * outerWidth i ^ 2 * balanceOrder i ^ 4 ≤
    secondWidth i

theorem scale_floor (i : Input) : 2 ^ 24 ≤ scale i := le_max_left _ _

theorem scaleBound_le (i : Input) : scaleBound i ≤ 2 ^ scale i := by
  exact (Nat.le_pow_clog (by decide : 1 < 2) _).trans
    (Nat.pow_le_pow_right (by decide) (le_max_right _ _))

theorem public_bounds (i : Input) :
    i.sourceConstant ≤ 2 ^ scale i ∧ i.nextDepth ≤ 2 ^ scale i ∧
    i.cost ≤ 2 ^ scale i ∧ namingLength i ≤ 2 ^ scale i ∧
    Nat.clog 2 (i.edges + 2) ≤ 2 ^ scale i := by
  have h := scaleBound_le i
  unfold scaleBound at h
  omega

theorem auxiliaryLog_floor (i : Input) : 24 ≤ auxiliaryLog i := by
  have h := Nat.clog_mono_right 2 (scale_floor i)
  simpa [auxiliaryLog, Nat.clog_pow] using h

/-- The numerical induction used on every dyadic interval above the cutoff. -/
theorem quadratic_dyadic_bound {n : ℕ} (hn : 25 ≤ n) :
    10000 * n ^ 2 ≤ 2 ^ (n - 1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hp : 10000 * (n + 1) ^ 2 ≤ 2 * (10000 * n ^ 2) := by nlinarith
    calc
      10000 * (n + 1) ^ 2 ≤ 2 * (10000 * n ^ 2) := hp
      _ ≤ 2 * 2 ^ (n - 1) := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (n + 1 - 1) := by
        rw [show n + 1 - 1 = (n - 1) + 1 by omega, pow_succ]
        omega

theorem binExponent_le_scale (i : Input) : binExponent i ≤ scale i := by
  have hu := auxiliaryLog_floor i
  by_cases he : auxiliaryLog i = 24
  · have h := scale_floor i
    change 10000 * auxiliaryLog i ^ 2 ≤ scale i
    rw [he]
    norm_num at h ⊢
    omega
  · have hn : 25 ≤ auxiliaryLog i := by omega
    have hp := quadratic_dyadic_bound hn
    have hlt : 2 ^ (auxiliaryLog i - 1) < scale i := by
      apply Nat.pow_lt_of_lt_clog
      change auxiliaryLog i - 1 < auxiliaryLog i
      omega
    exact hp.trans hlt.le

theorem bins_le_scale_power (i : Input) : bins i ≤ 2 ^ scale i :=
  Nat.pow_le_pow_right (by decide) (binExponent_le_scale i)

theorem polynomial_le_power {n : ℕ} (hn : 32 ≤ n) :
    256 * n ^ 2 + n + 1 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    calc
      256 * (n + 1) ^ 2 + (n + 1) + 1 ≤ 2 * (256 * n ^ 2 + n + 1) := by
        nlinarith
      _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (n + 1) := by rw [pow_succ]; omega

theorem scale_polynomial_bound (i : Input) :
    firstExponent i + scale i + 1 ≤ 2 ^ scale i := by
  have h := scale_floor i
  norm_num at h
  exact polynomial_le_power (by omega)

theorem bins_pos (i : Input) : 0 < bins i := by unfold bins; positivity
theorem firstWidth_pos (i : Input) : 0 < firstWidth i := by
  have h := scale_floor i
  norm_num at h
  have ha : 2 ≤ firstExponent i := by unfold firstExponent; nlinarith
  have hp : 2 ^ 2 ≤ 2 ^ firstExponent i := Nat.pow_le_pow_right (by decide) ha
  unfold firstWidth
  norm_num at hp
  omega
theorem secondWidth_pos (i : Input) : 0 < secondWidth i := by unfold secondWidth; positivity
theorem balanceOrder_pos (i : Input) : 0 < balanceOrder i := by unfold balanceOrder; positivity
theorem outerWidth_pos (i : Input) : 0 < outerWidth i := by unfold outerWidth; positivity
theorem restorationWidth_pos (i : Input) : 0 < restorationWidth i := by
  unfold restorationWidth; positivity

theorem sixtyfour_dvd_bins (i : Input) : 64 ∣ bins i := by
  have hu := auxiliaryLog_floor i
  have h : 6 ≤ binExponent i := by unfold binExponent; nlinarith
  exact (by norm_num : (64 : ℕ) = 2 ^ 6) ▸
    (pow_dvd_pow 2 h)

theorem bins_le_firstPower (i : Input) : bins i ≤ 2 ^ firstExponent i := by
  have h := scale_floor i
  norm_num at h
  apply Nat.pow_le_pow_right (by decide)
  exact (binExponent_le_scale i).trans (by unfold firstExponent; nlinarith)

theorem tailDepth_four_le_bins (i : Input) : 4 * tailDepth i ≤ bins i := by
  have hu := auxiliaryLog_floor i
  have h : 40 * auxiliaryLog i + 2 ≤ binExponent i := by
    unfold binExponent
    nlinarith
  have hp := Nat.pow_le_pow_right (n := 2) (by decide) h
  simpa [tailDepth, bins, pow_add, Nat.mul_comm] using hp

theorem tailDepth_le_quarter_bins (i : Input) : tailDepth i ≤ bins i / 4 := by
  exact (Nat.le_div_iff_mul_le (by decide)).2 (by
    simpa [Nat.mul_comm] using tailDepth_four_le_bins i)

theorem bins_hard_seed_floor (i : Input) : 2 ^ (2 ^ 20) ≤ bins i / 4 := by
  have hu := auxiliaryLog_floor i
  have h : 2 ^ 20 + 2 ≤ binExponent i := by
    unfold binExponent
    norm_num
    nlinarith
  apply (Nat.le_div_iff_mul_le (by decide)).2
  change 2 ^ (2 ^ 20) * 4 ≤ 2 ^ binExponent i
  calc
    2 ^ (2 ^ 20) * 4 = 2 ^ (2 ^ 20 + 2) := (pow_add 2 (2 ^ 20) 2).symm
    _ ≤ 2 ^ binExponent i := Nat.pow_le_pow_right (by decide) h

theorem balanceOrder_sixteen_dvd (i : Input) : 16 ∣ balanceOrder i := by
  have hl := scale_floor i
  norm_num at hl
  have hs : 1 ≤ scale i ^ 4 := one_le_pow₀ (by omega)
  have h : 4 ≤ balanceExponent i := by unfold balanceExponent; omega
  exact (by norm_num : (16 : ℕ) = 2 ^ 4) ▸ pow_dvd_pow 2 h

theorem reference_four_lt_outer (i : Input) : 4 * referenceWidth i < outerWidth i := by
  have hl := scale_floor i
  norm_num at hl
  have h : referenceExponent i + 2 < outerExponent i := by
    unfold referenceExponent outerExponent
    nlinarith
  have hp := Nat.pow_lt_pow_right (by decide : 1 < 2) h
  simpa [referenceWidth, outerWidth, pow_add, Nat.mul_comm] using hp

theorem binExponent_lt_tailDepth (i : Input) : binExponent i < tailDepth i := by
  have hu := auxiliaryLog_floor i
  calc
    binExponent i ≤ scale i := binExponent_le_scale i
    _ ≤ 2 ^ auxiliaryLog i := Nat.le_pow_clog (by decide) _
    _ < 2 ^ (40 * auxiliaryLog i) := Nat.pow_lt_pow_right (by decide) (by omega)
    _ = tailDepth i := rfl

/-- Universal property of rounding a positive integer upwards to a power of two. -/
theorem roundedPower_bounds {n : ℕ} (hn : 0 < n) :
    n ≤ 2 ^ Nat.clog 2 n ∧ 2 ^ Nat.clog 2 n < 2 * n := by
  refine ⟨Nat.le_pow_clog (by decide) _, ?_⟩
  by_cases he : n = 1
  · simp [he]
  · have hgt : 1 < n := by omega
    have hc := Nat.clog_pos (by decide : 1 < 2) hgt
    have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hgt
    calc
      2 ^ Nat.clog 2 n = 2 ^ ((Nat.clog 2 n).pred + 1) :=
        congrArg (fun k : ℕ => 2 ^ k) (Nat.succ_pred_eq_of_pos hc).symm
      _ = 2 * 2 ^ (Nat.clog 2 n).pred := by rw [pow_succ]; omega
      _ < 2 * n := Nat.mul_lt_mul_of_pos_left hp (by decide)

theorem secondWidth_bounds (i : Input) (he : 0 < i.edges) :
    12 * bins i * i.edges ≤ secondWidth i ∧
    secondWidth i < 24 * bins i * i.edges := by
  have hn : 0 < 12 * bins i * i.edges := by have := bins_pos i; positivity
  have h := roundedPower_bounds hn
  refine ⟨h.1, ?_⟩
  calc
    secondWidth i < 2 * (12 * bins i * i.edges) := h.2
    _ = 24 * bins i * i.edges := by ring

theorem accepted_balance_four_le_second (i : Input)
    (hc : 0 < i.sourceConstant) (ha : Accepted i) :
    4 * balanceOrder i ≤ secondWidth i := by
  have hs := bins_pos i
  have hq := outerWidth_pos i
  have ht := balanceOrder_pos i
  have hf : 4 ≤ 2 ^ 40 * i.sourceConstant * bins i * outerWidth i ^ 2 := by
    calc
      4 ≤ 2 ^ 40 * 1 * 1 * 1 ^ 2 := by norm_num
      _ ≤ 2 ^ 40 * i.sourceConstant * bins i * outerWidth i ^ 2 := by gcongr <;> omega
  have ht4 : balanceOrder i ≤ balanceOrder i ^ 4 := by
    simpa using (Nat.pow_le_pow_right ht (by decide : 1 ≤ 4))
  exact (Nat.mul_le_mul hf ht4).trans ha.2.2.2

theorem accepted_balance_dvd_second (i : Input)
    (hc : 0 < i.sourceConstant) (ha : Accepted i) :
    balanceOrder i ∣ secondWidth i := by
  have h := accepted_balance_four_le_second i hc ha
  have hle : balanceOrder i ≤ secondWidth i := by omega
  have he : balanceExponent i ≤ secondExponent i :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).1 hle
  exact pow_dvd_pow 2 he

theorem outer_le_balanceOrder (i : Input) : outerWidth i ≤ balanceOrder i := by
  have hl := scale_floor i
  norm_num at hl
  have hs : 1 ≤ scale i ^ 2 := one_le_pow₀ (by omega)
  have hp : scale i ^ 2 ≤ scale i ^ 4 := by
    simpa using (Nat.pow_le_pow_right (by omega : 0 < scale i) (by decide : 2 ≤ 4))
  apply Nat.pow_le_pow_right (by decide)
  unfold outerExponent balanceExponent
  omega

theorem balanceOrder_hard_seed_floor (i : Input) : 2 ^ (2 ^ 20) ≤ balanceOrder i := by
  have hl := scale_floor i
  norm_num at hl
  have hs : 1 ≤ scale i ^ 4 := one_le_pow₀ (by omega)
  apply Nat.pow_le_pow_right (by decide)
  unfold balanceExponent
  norm_num
  omega

theorem restorationWidth_bounds (i : Input)
    (hc : 0 < i.sourceConstant) (hb : 0 < i.nextDepth) :
    restorationTarget i ≤ restorationWidth i ∧
    restorationWidth i < 2560 * i.nextDepth * i.sourceConstant * bins i * outerWidth i := by
  have hs := bins_pos i
  have hq := outerWidth_pos i
  have hn : 0 < restorationTarget i := by unfold restorationTarget; positivity
  have h := roundedPower_bounds hn
  refine ⟨h.1, ?_⟩
  calc
    restorationWidth i < 2 * restorationTarget i := h.2
    _ = 2560 * i.nextDepth * i.sourceConstant * bins i * outerWidth i := by
      unfold restorationTarget
      ring

theorem retainedExponent_eq (i : Input) :
    retainedExponent i = restorationExponent i + 8 := by
  have hp : 0 < 2 ^ restorationExponent i := by positivity
  have hu : 160 * restorationWidth i ≤ 2 ^ (restorationExponent i + 8) := by
    unfold restorationWidth
    rw [pow_add]
    norm_num
    omega
  have hl : 2 ^ (restorationExponent i + 7) < 160 * restorationWidth i := by
    unfold restorationWidth
    rw [pow_add]
    norm_num
    omega
  have h1 := Nat.clog_le_of_le_pow hu
  have h2 := (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).2 hl
  unfold retainedExponent
  omega

theorem scale_power_forty_le_tailDepth (i : Input) : scale i ^ 40 ≤ tailDepth i := by
  calc
    scale i ^ 40 ≤ (2 ^ auxiliaryLog i) ^ 40 :=
      Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) _) _
    _ = 2 ^ (40 * auxiliaryLog i) := by rw [← pow_mul, Nat.mul_comm]
    _ = tailDepth i := rfl

theorem tailDepth_polynomial_lower (i : Input) :
    10000 * scale i ^ 2 + 2 * scale i + 40 ≤ tailDepth i := by
  have hl := scale_floor i
  norm_num at hl
  have h1 : 10002 * scale i ^ 2 ≤ scale i ^ 3 := by
    have h := Nat.mul_le_mul_right (scale i ^ 2) (show 10002 ≤ scale i by omega)
    nlinarith
  have h2 : scale i ^ 3 ≤ scale i ^ 40 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have h3 : 10000 * scale i ^ 2 + 2 * scale i + 40 ≤ 10002 * scale i ^ 2 := by
    nlinarith
  exact h3.trans (h1.trans (h2.trans (scale_power_forty_le_tailDepth i)))

theorem secondExponent_le (i : Input) : secondExponent i ≤ 2 ^ (scale i + 1) := by
  have he : i.edges ≤ 2 ^ (2 ^ scale i) := by
    have h1 := Nat.le_pow_clog (by decide : 1 < 2) (i.edges + 2)
    have h2 := Nat.pow_le_pow_right (n := 2) (by decide) (public_bounds i).2.2.2.2
    omega
  have hb : 12 * bins i * i.edges ≤ 2 ^ (4 + scale i + 2 ^ scale i) := by
    calc
      12 * bins i * i.edges ≤ 2 ^ 4 * 2 ^ scale i * 2 ^ (2 ^ scale i) := by
        gcongr
        · norm_num
        · exact bins_le_scale_power i
      _ = 2 ^ (4 + scale i + 2 ^ scale i) := by rw [pow_add, pow_add]
  have hc := Nat.clog_le_of_le_pow hb
  have hp := scale_polynomial_bound i
  have hl := scale_floor i
  norm_num at hl
  have ha : 3 ≤ firstExponent i := by unfold firstExponent; nlinarith
  have hsmall : scale i + 4 ≤ 2 ^ scale i := by omega
  change Nat.clog 2 (12 * bins i * i.edges) ≤ _
  calc
    Nat.clog 2 (12 * bins i * i.edges) ≤ 4 + scale i + 2 ^ scale i := hc
    _ ≤ 2 ^ (scale i + 1) := by rw [pow_succ]; omega

theorem quartic_le_power {n : ℕ} (hn : 32 ≤ n) :
    2000000000 * n ^ 4 + 5000 * n ^ 2 + 2 * n + 100 ≤ 2 ^ (6 * n) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hbase : n + 1 ≤ 2 * n := by omega
    have h4 := Nat.pow_le_pow_left hbase 4
    have h2 := Nat.pow_le_pow_left hbase 2
    have hg :
        2000000000 * (n + 1) ^ 4 + 5000 * (n + 1) ^ 2 + 2 * (n + 1) + 100 ≤
          64 * (2000000000 * n ^ 4 + 5000 * n ^ 2 + 2 * n + 100) := by
      nlinarith
    calc
      2000000000 * (n + 1) ^ 4 + 5000 * (n + 1) ^ 2 + 2 * (n + 1) + 100 ≤
          64 * (2000000000 * n ^ 4 + 5000 * n ^ 2 + 2 * n + 100) := hg
      _ ≤ 64 * 2 ^ (6 * n) := Nat.mul_le_mul_left 64 ih
      _ = 2 ^ (6 * (n + 1)) := by
        rw [show 6 * (n + 1) = 6 * n + 6 by omega, pow_add]
        norm_num
        omega

theorem firstDepth_polynomial_lower (i : Input) :
    secondExponent i + 20 * balanceExponent i + 5000 * scale i ^ 2 +
      2 * scale i + 100 ≤ firstDepth i := by
  have hl := scale_floor i
  norm_num at hl
  have hpoly := quartic_le_power (show 32 ≤ scale i by omega)
  have hq := secondExponent_le i
  have hexp : scale i + 1 ≤ 6 * scale i := by omega
  have hp := Nat.pow_le_pow_right (n := 2) (by decide) hexp
  have hsum : secondExponent i + 20 * balanceExponent i + 5000 * scale i ^ 2 +
      2 * scale i + 100 ≤ 2 ^ (6 * scale i + 1) := by
    change secondExponent i + 20 * (100000000 * scale i ^ 4) +
      5000 * scale i ^ 2 + 2 * scale i + 100 ≤ _
    rw [pow_succ (2 : ℕ) (6 * scale i)]
    omega
  exact hsum.trans (Nat.pow_le_pow_right (by decide) (by omega))

theorem balanceOrder_le_firstDepth_power (i : Input) :
    balanceOrder i ≤ 2 ^ firstDepth i := by
  have h := firstDepth_polynomial_lower i
  exact Nat.pow_le_pow_right (by decide) (show balanceExponent i ≤ firstDepth i by omega)

theorem secondDepth_bound (i : Input) : secondDepth i ≤ 2 ^ (scale i + 2) := by
  have hx : i.rows ≤ 2 ^ Nat.clog 2 i.rows := Nat.le_pow_clog (by decide) _
  have hq : firstWidth i ≤ 2 ^ firstExponent i := Nat.sub_le _ _
  have hprod : 32 * bins i * firstWidth i * i.rows ≤
      2 ^ (5 + binExponent i + firstExponent i + Nat.clog 2 i.rows) := by
    calc
      32 * bins i * firstWidth i * i.rows ≤
          2 ^ 5 * 2 ^ binExponent i * 2 ^ firstExponent i * 2 ^ Nat.clog 2 i.rows := by
        change 2 ^ 5 * bins i * firstWidth i * i.rows ≤ _
        gcongr
        exact le_rfl
      _ = 2 ^ (5 + binExponent i + firstExponent i + Nat.clog 2 i.rows) := by
        rw [pow_add, pow_add, pow_add]
  have hc := Nat.clog_le_of_le_pow hprod
  have hp := scale_polynomial_bound i
  have hbin := binExponent_le_scale i
  have hxlog : Nat.clog 2 i.rows ≤ 2 ^ scale i :=
    (le_max_left _ _).trans (public_bounds i).2.2.2.1
  have htwo : 16 ≤ 2 ^ scale i := by
    have hl := scale_floor i
    norm_num at hl
    exact (by norm_num : (16 : ℕ) = 2 ^ 4) ▸
      Nat.pow_le_pow_right (by decide) (by omega)
  change Nat.clog 2 (32 * bins i * firstWidth i * i.rows) + 6 ≤ _
  rw [pow_add]
  norm_num
  omega

theorem bins_le_secondDepth_power (i : Input) (hx : 0 < i.rows) :
    bins i ≤ 2 ^ secondDepth i := by
  have hq := firstWidth_pos i
  have hb : bins i ≤ 32 * bins i * firstWidth i * i.rows := by
    calc
      bins i = 1 * bins i * 1 * 1 := by ring
      _ ≤ 32 * bins i * firstWidth i * i.rows := by gcongr <;> omega
  calc
    bins i ≤ 32 * bins i * firstWidth i * i.rows := hb
    _ ≤ 2 ^ Nat.clog 2 (32 * bins i * firstWidth i * i.rows) := Nat.le_pow_clog (by decide) _
    _ ≤ 2 ^ secondDepth i := Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _)

/-- The common public certificate `C` used in the parameter appendix. -/
def certificateCost (i : Input) : ℕ :=
  i.cost + firstExponent i + secondExponent i + binExponent i + 1

theorem certificateCost_bound (i : Input) : certificateCost i ≤ 2 ^ (scale i + 3) := by
  have hD := (public_bounds i).2.2.1
  have ha := scale_polynomial_bound i
  have hs := binExponent_le_scale i
  have hq := secondExponent_le i
  rw [pow_add] at hq ⊢
  norm_num at hq ⊢
  unfold certificateCost
  omega

theorem rowTolerance_pos (i : Input) (hc : 0 < i.sourceConstant) : 0 < rowTolerance i := by
  have hs := bins_pos i
  unfold rowTolerance
  positivity

theorem columnLoss_pos (i : Input) (hc : 0 < i.sourceConstant) : 0 < columnLoss i := by
  have hr := rowTolerance_pos i hc
  have hq := outerWidth_pos i
  unfold columnLoss
  positivity

theorem tolerance_identity (i : Input) : columnTolerance i = 2 * rowTolerance i := by
  unfold columnTolerance rowTolerance
  ring

theorem columnLoss_identity (i : Input) :
    columnLoss i = 1 / (16 * (i.sourceConstant : ℚ) * bins i * outerWidth i) := by
  unfold columnLoss rowTolerance
  push_cast
  ring

theorem restorationTarget_identity (i : Input) (hc : 0 < i.sourceConstant) :
    (restorationTarget i : ℚ) = 80 * i.nextDepth / columnLoss i := by
  have hcn : (i.sourceConstant : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
  have hsn : (bins i : ℚ) ≠ 0 := by exact_mod_cast (bins_pos i).ne'
  have hqn : (outerWidth i : ℚ) ≠ 0 := by exact_mod_cast (outerWidth_pos i).ne'
  rw [columnLoss_identity]
  unfold restorationTarget
  push_cast
  field_simp
  ring

theorem restoration_coverage (i : Input) (hc : 0 < i.sourceConstant) :
    80 * (i.nextDepth : ℚ) ≤ restorationWidth i * columnLoss i := by
  have hpos := columnLoss_pos i hc
  have h := Nat.le_pow_clog (by decide : 1 < 2) (restorationTarget i)
  have hcast : (restorationTarget i : ℚ) ≤ restorationWidth i := by exact_mod_cast h
  rw [restorationTarget_identity i hc] at hcast
  exact (div_le_iff₀ hpos).1 hcast

theorem retainedFraction_identity (i : Input) :
    (restorationWidth i : ℚ) * retainedFraction i = 1 / 160 := by
  have hn : (restorationWidth i : ℚ) ≠ 0 := by exact_mod_cast (restorationWidth_pos i).ne'
  unfold retainedFraction
  field_simp

theorem retainedFraction_pos (i : Input) : 0 < retainedFraction i := by
  have h := restorationWidth_pos i
  unfold retainedFraction
  positivity

theorem outer_polynomial_le_power {n : ℕ} (hn : 32 ≤ n) :
    1000 * n ^ 2 + 3 * n + 20 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    calc
      1000 * (n + 1) ^ 2 + 3 * (n + 1) + 20 ≤
          2 * (1000 * n ^ 2 + 3 * n + 20) := by nlinarith
      _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (n + 1) := by rw [pow_succ]; omega

theorem retainedExponent_bound (i : Input) :
    retainedExponent i ≤ 1000 * scale i ^ 2 + 3 * scale i + 20 := by
  have hc := (public_bounds i).1
  have hb := (public_bounds i).2.1
  have hs := bins_le_scale_power i
  have ht : restorationTarget i ≤ 2 ^ (11 + 3 * scale i + outerExponent i) := by
    calc
      restorationTarget i ≤
          2 ^ 11 * 2 ^ scale i * 2 ^ scale i * 2 ^ scale i * 2 ^ outerExponent i := by
        unfold restorationTarget outerWidth
        gcongr
        norm_num
      _ = 2 ^ (11 + 3 * scale i + outerExponent i) := by
        rw [show 11 + 3 * scale i + outerExponent i =
          (((11 + scale i) + scale i) + scale i) + outerExponent i by omega]
        rw [pow_add, pow_add, pow_add, pow_add]
  have he := Nat.clog_le_of_le_pow ht
  have hθ := retainedExponent_eq i
  change restorationExponent i ≤ 11 + 3 * scale i + 1000 * scale i ^ 2 at he
  omega

theorem retainedExponent_power_bound (i : Input) : retainedExponent i ≤ 2 ^ scale i := by
  have hl := scale_floor i
  norm_num at hl
  exact (retainedExponent_bound i).trans (outer_polynomial_le_power (by omega))

theorem columnLoss_lt (i : Input) (hc : 0 < i.sourceConstant) : columnLoss i < 1 / 64 := by
  have hs : (1 : ℚ) ≤ bins i := by exact_mod_cast (bins_pos i)
  have hcr : (1 : ℚ) ≤ i.sourceConstant := by exact_mod_cast hc
  have hl := scale_floor i
  norm_num at hl
  have hpow : 3 ≤ outerExponent i := by unfold outerExponent; nlinarith
  have hq : (8 : ℚ) ≤ outerWidth i := by
    exact_mod_cast (show 8 ≤ outerWidth i from
      (by norm_num : (8 : ℕ) = 2 ^ 3) ▸ Nat.pow_le_pow_right (by decide) hpow)
  rw [columnLoss_identity]
  have hd : (128 : ℚ) ≤ 16 * i.sourceConstant * bins i * outerWidth i := by
    calc
      (128 : ℚ) = 16 * 1 * 1 * 8 := by norm_num
      _ ≤ 16 * (i.sourceConstant : ℚ) * bins i * outerWidth i := by gcongr
  have hp : (0 : ℚ) < 16 * i.sourceConstant * bins i * outerWidth i := by linarith
  apply (div_lt_iff₀ hp).2
  linarith

/-- All width domains explicitly listed at the start of the appendix,
plus the second-interlace divisibility and width constraints. The row and
graph acceptance checks are not replaced by a hidden feasibility witness. -/
theorem width_domains (i : Input) (hc : 0 < i.sourceConstant) (ha : Accepted i) :
    64 ∣ bins i ∧ bins i ≤ 2 ^ firstExponent i ∧
    2 ^ (2 ^ 20) ≤ bins i / 4 ∧ binExponent i < tailDepth i ∧
    2 ^ (2 ^ 20) ≤ balanceOrder i ∧ 16 ∣ balanceOrder i ∧
    4 * balanceOrder i ≤ secondWidth i ∧ balanceOrder i ∣ secondWidth i ∧
    balanceOrder i ≤ 2 ^ firstDepth i ∧ bins i ≤ 2 ^ secondDepth i := by
  exact ⟨sixtyfour_dvd_bins i, bins_le_firstPower i, bins_hard_seed_floor i,
    binExponent_lt_tailDepth i, balanceOrder_hard_seed_floor i,
    balanceOrder_sixteen_dvd i, accepted_balance_four_le_second i hc ha,
    accepted_balance_dvd_second i hc ha, balanceOrder_le_firstDepth_power i,
    bins_le_secondDepth_power i (by have h := ha.1; omega)⟩

/-- The three final numerical hypotheses of robustness restoration. -/
theorem restoration_gates (i : Input) (hc : 0 < i.sourceConstant) :
    0 < columnLoss i ∧ columnLoss i < 1 / 64 ∧
    80 * (i.nextDepth : ℚ) ≤ restorationWidth i * columnLoss i ∧
    (restorationWidth i : ℚ) * retainedFraction i = 1 / 160 ∧
    (restorationWidth i : ℚ) * retainedFraction i < 1 / 20 := by
  refine ⟨columnLoss_pos i hc, columnLoss_lt i hc, restoration_coverage i hc,
    retainedFraction_identity i, ?_⟩
  rw [retainedFraction_identity]
  norm_num

end EthInapproximability.CurrentPaper.Parameters
