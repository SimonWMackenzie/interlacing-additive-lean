import EthInapproximability.CurrentPaper.ExactFiniteReduction
import EthInapproximability.CurrentPaper.ExactHardSeedGate
import EthInapproximability.CurrentPaper.ExactLossGates
import EthInapproximability.CurrentPaper.ExactNumericGates
import EthInapproximability.CurrentPaper.ExactBinNumericGates
import EthInapproximability.CurrentPaper.ExactSamplerInstances
import EthInapproximability.CurrentPaper.ExactSourcePadding

/-!
# Explicit parameters for the finite exact reduction

Source: v8 `03-exact-hardness.tex`, `eq:exact-parameters`, and the final
cutoff verification in `E-exact-details.tex`. We take the padded dimension
`d = 2^r` with `r = 2^s`. Rounding a logarithmic dimension to the next power
of two at most squares the dimension. The manuscript's least-power-of-two
formulas then give `a = 2s+1`, `t₁ = 64r`; the second width remains the exact
least power of two above `3r/s`, computed by integer ceiling division.
-/

namespace EthInapproximability.CurrentPaper.ExactParameters

open NPCC ExactConstruction

def dimensionLog (s : ℕ) : ℕ := 2 ^ s
def dimension (s : ℕ) : ℕ := 2 ^ dimensionLog s
def firstExponent (s : ℕ) : ℕ := 2 * s + 1
def firstOrderExponent (s : ℕ) : ℕ := s + 6
def firstOrder (s : ℕ) : ℕ := 64 * dimensionLog s
def firstResidualExponent (s : ℕ) : ℕ := s - 5
def firstStoppingRows (s : ℕ) : ℕ := 36 * dimensionLog s
def secondTarget (s : ℕ) : ℕ := (3 * dimensionLog s) ⌈/⌉ s
def secondExponent (s : ℕ) : ℕ := Nat.clog 2 (secondTarget s)
def secondOrder (s : ℕ) : ℕ := 2 ^ secondExponent s

theorem firstOrder_power (s : ℕ) : firstOrder s = 2 ^ firstOrderExponent s := by
  simp only [firstOrder, dimensionLog, firstOrderExponent, pow_add]
  norm_num
  ring

theorem firstWidth_exact (s : ℕ) : width (firstExponent s) = 2 * dimensionLog s ^ 2 := by
  simp only [width, firstExponent, dimensionLog, pow_add, pow_one]
  rw [show 2 * s = s * 2 by omega, pow_mul]
  ring

theorem firstResidual_sum {s : ℕ} (hs : 5 ≤ s) :
    firstExponent s = firstOrderExponent s + firstResidualExponent s := by
  simp only [firstExponent, firstOrderExponent, firstResidualExponent]
  omega

theorem firstWidth_split {s : ℕ} (hs : 5 ≤ s) :
    width (firstExponent s) = 2 ^ firstResidualExponent s * firstOrder s := by
  rw [firstOrder_power, ← pow_add]
  unfold width
  congr 1
  have hh := firstResidual_sum hs
  omega

theorem firstStopping_fraction (s : ℕ) :
    16 * firstStoppingRows s = 9 * firstOrder s := by
  unfold firstStoppingRows firstOrder
  ring

/-- The integer ceiling in the second-width algorithm is the usual real
ceiling, so a divisible target is not rounded up by an extra label. -/
theorem secondTarget_eq_ceil {s : ℕ} (hs : 0 < s) :
    secondTarget s = ⌈(3 : ℝ) * dimensionLog s / s⌉₊ := by
  apply Nat.le_antisymm
  · apply (ceilDiv_le_iff_le_mul hs).mpr
    have hc := Nat.le_ceil ((3 : ℝ) * dimensionLog s / s)
    have hc' := (div_le_iff₀ (by exact_mod_cast hs : (0 : ℝ) < s)).mp hc
    have hc'' : (3 : ℝ) * dimensionLog s ≤ s * ⌈(3 : ℝ) * dimensionLog s / s⌉₊ := by
      simpa [mul_comm] using hc'
    exact_mod_cast hc''
  · apply Nat.ceil_le.mpr
    apply (div_le_iff₀ (by exact_mod_cast hs : (0 : ℝ) < s)).mpr
    have hc : 3 * dimensionLog s ≤ s * secondTarget s :=
      (ceilDiv_le_iff_le_mul hs).mp (le_refl _)
    exact_mod_cast (by simpa [mul_comm] using hc)

theorem secondOrder_minimal (s k : ℕ) (hk : secondTarget s ≤ 2 ^ k) :
    secondExponent s ≤ k := Nat.clog_le_of_le_pow hk

theorem secondOrder_lower {s : ℕ} (hs : 0 < s) :
    3 * dimensionLog s ≤ s * secondOrder s := by
  have htarget : 3 * dimensionLog s ≤ s * secondTarget s :=
    (ceilDiv_le_iff_le_mul hs).mp (le_refl _)
  exact htarget.trans (Nat.mul_le_mul_left _ (Nat.le_pow_clog (by omega) _))

theorem secondExponent_upper {s : ℕ} (hs : 6 ≤ s) : secondExponent s ≤ s - 1 := by
  apply secondOrder_minimal
  apply (ceilDiv_le_iff_le_mul (by omega : 0 < s)).mpr
  have hpow : dimensionLog s = 2 * 2 ^ (s - 1) := by
    rw [dimensionLog, ← Nat.pow_succ', Nat.succ_eq_add_one,
      Nat.sub_add_cancel (by omega : 1 ≤ s)]
  rw [hpow]
  nlinarith

theorem secondExponent_lower {s : ℕ} (hs : 0 < s) : s / 2 ≤ secondExponent s := by
  have hsmall : s ≤ 2 ^ (s / 2 + 1) := by
    have hi : s / 2 + 1 ≤ 2 ^ (s / 2) := Nat.succ_le_of_lt Nat.lt_two_pow_self
    have hdiv : s ≤ 2 * (s / 2 + 1) := by omega
    have hm := Nat.mul_le_mul_left 2 hi
    rw [Nat.pow_succ']
    omega
  have hmul : s * 2 ^ (s / 2) ≤ 2 * dimensionLog s := by
    calc
      s * 2 ^ (s / 2) ≤ 2 ^ (s / 2 + 1) * 2 ^ (s / 2) := Nat.mul_le_mul_right _ hsmall
      _ = 2 ^ (s / 2 + 1 + s / 2) := by rw [← pow_add]
      _ ≤ 2 ^ (s + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      _ = 2 * dimensionLog s := by simp only [dimensionLog, Nat.pow_succ']
  have hpos : 0 < dimensionLog s := by unfold dimensionLog; positivity
  have hlt : s * 2 ^ (s / 2) < 3 * dimensionLog s := by omega
  have htarget : 2 ^ (s / 2) < secondTarget s := by
    by_contra hn
    have hc : 3 * dimensionLog s ≤ s * 2 ^ (s / 2) :=
      (ceilDiv_le_iff_le_mul hs).mp (Nat.le_of_not_gt hn)
    omega
  have hpow : 2 ^ (s / 2) ≤ 2 ^ secondExponent s :=
    htarget.le.trans (Nat.le_pow_clog (by omega) _)
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hpow

theorem secondOrder_upper {s : ℕ} (hs : 2 ≤ s) :
    s * secondOrder s < 6 * dimensionLog s := by
  have hm : 1 ≤ secondExponent s := (by omega : 1 ≤ s / 2).trans
    (secondExponent_lower (by omega))
  have htarget : 1 < secondTarget s := by
    have hh : 2 ^ (secondExponent s - 1) < secondTarget s :=
      Nat.pow_lt_of_lt_clog (by change secondExponent s - 1 < secondExponent s; omega)
    have hp : 1 ≤ (2 : ℕ) ^ (secondExponent s - 1) := Nat.one_le_pow _ _ (by omega)
    omega
  have hpred := Nat.pow_pred_clog_lt_self (by omega : 1 < 2) htarget
  change 2 ^ (secondExponent s - 1) < secondTarget s at hpred
  have hmul : s * 2 ^ (secondExponent s - 1) < 3 * dimensionLog s := by
    by_contra hn
    have hc : secondTarget s ≤ 2 ^ (secondExponent s - 1) :=
      (ceilDiv_le_iff_le_mul (by omega : 0 < s)).mpr (Nat.le_of_not_gt hn)
    omega
  have heq : secondOrder s = 2 * 2 ^ (secondExponent s - 1) := by
    rw [secondOrder, ← Nat.pow_succ', Nat.succ_eq_add_one, Nat.sub_add_cancel hm]
  rw [heq]
  nlinarith

/-- A fixed linear bound, used only above the absolute scalar cutoff. -/
theorem linear_lt_power {s : ℕ} (hs : 4 ≤ s) : s + 8 < dimensionLog s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num [dimensionLog]
  | succ s hs ih =>
      simp only [dimensionLog, pow_succ] at ih ⊢
      omega

theorem naming_exponent_bound {s : ℕ} (hs : 4 ≤ s) :
    firstExponent s + 1 ≤ dimensionLog s := by
  have hh : 2 * s + 2 ≤ 2 ^ s := by
    induction s, hs using Nat.le_induction with
    | base => norm_num
    | succ s hs ih =>
        rw [pow_succ]
        omega
  exact hh

/-- The size inequalities requested by the actual small-bias samplers. -/
theorem sampler_order_gates {s : ℕ} (hs : 8 ≤ s) :
    64 * dimensionLog s ≤ firstOrder s ∧
    firstOrder s ≤ 128 * dimensionLog s ∧
    firstOrder s ≤ prefixLength (firstExponent s) + 3 ∧
    6 * dimensionLog s ≤ firstExponent s * secondOrder s ∧
    firstExponent s * secondOrder s ≤ 18 * dimensionLog s ∧
    secondOrder s ≤ dimension s := by
  have hR : 32 ≤ dimensionLog s := by
    have hh := Nat.pow_le_pow_right (n := 2) (by omega : 1 ≤ 2) (by omega : 5 ≤ s)
    simpa [dimensionLog] using hh
  have hfirst := firstWidth_exact s
  have hprefix : prefixLength (firstExponent s) + 2 = width (firstExponent s) :=
    Construction.qOne_add_two _ (by unfold firstExponent; omega)
  have hlower := secondOrder_lower (s := s) (by omega)
  have hupper := secondOrder_upper (s := s) (by omega)
  have horder : secondOrder s ≤ dimensionLog s := by
    exact Nat.pow_le_pow_right (by omega) ((secondExponent_upper (by omega)).trans (Nat.sub_le _ _))
  refine ⟨le_refl _, ?_, ?_, ?_, ?_, ?_⟩
  · unfold firstOrder
    omega
  · unfold firstOrder
    nlinarith
  · unfold firstExponent
    nlinarith
  · unfold firstExponent
    nlinarith
  · exact horder.trans (Nat.le_of_lt Nat.lt_two_pow_self)

noncomputable def indexColumnDensity (s : ℕ) : ℝ :=
  1 / (2 : ℝ) ^ (3 * dimensionLog s)

noncomputable def indexStoppingDensity (s : ℕ) : ℝ :=
  indexColumnDensity s / (4 * (firstOrder s : ℝ))

theorem indexStopping_seed {s : ℕ} {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    indexStoppingDensity s ≤ indexColumnDensity s *
      (2 : ℝ) ^ (-((firstOrderExponent s + 1 : ℕ) : ℝ)) / (1 + ε) := by
  have ht : 0 < (firstOrder s : ℝ) := by
    unfold firstOrder dimensionLog
    positivity
  have hh : 0 < indexColumnDensity s := by unfold indexColumnDensity; positivity
  have hpow : (2 : ℝ) ^ (firstOrderExponent s + 1) = 2 * firstOrder s := by
    have hf : (firstOrder s : ℝ) = 2 ^ firstOrderExponent s := by
      exact_mod_cast firstOrder_power s
    rw [pow_succ, hf]
    ring
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, hpow]
  unfold indexStoppingDensity
  have hden : 0 < 1 + ε := by linarith
  rw [← one_div, ← mul_div_assoc, div_div]
  rw [mul_one]
  apply div_le_div_of_nonneg_left hh.le (by positivity)
  nlinarith

/-- The indexing rank threshold is strictly exceeded with the manuscript's
`p₁ = 9t₁/16` and `z₀ = d⁻³/(4t₁)`. -/
theorem indexStopping_rank {s : ℕ} (hs : 4 ≤ s) :
    2 ^ (2 ^ (firstOrderExponent s - 1)) <
      ⌈(2 : ℝ) ^ firstStoppingRows s * indexStoppingDensity s⌉₊ := by
  apply Nat.lt_ceil.mpr
  have hpow : 2 ^ (firstOrderExponent s - 1) = 32 * dimensionLog s := by
    unfold firstOrderExponent dimensionLog
    rw [show s + 6 - 1 = s + 5 by omega, pow_add]
    norm_num
    omega
  rw [Nat.cast_pow, Nat.cast_ofNat, hpow]
  unfold indexStoppingDensity indexColumnDensity
  rw [← mul_div_assoc]
  apply (lt_div_iff₀ (by unfold firstOrder dimensionLog; positivity)).mpr
  rw [mul_one_div]
  apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ (3 * dimensionLog s))).mpr
  have hden : (4 : ℝ) * firstOrder s = 2 ^ (s + 8) := by
    simp only [firstOrder, dimensionLog, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, pow_add]
    norm_num
    ring
  rw [hden, ← pow_add, ← pow_add]
  apply (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mpr
  have hslack := linear_lt_power hs
  unfold firstStoppingRows
  omega

noncomputable def errorDensity (s : ℕ) : ℝ := 1 / (dimension s : ℝ) ^ 8
noncomputable def coordinateDensity (s : ℕ) : ℝ := 1 / (2 : ℝ) ^ (3 * s)
noncomputable def indexRowDensity (s : ℕ) : ℝ := 1 / (2 : ℝ) ^ firstResidualExponent s
noncomputable def indexOutputDensity (s : ℕ) : ℝ :=
  yLoss (errorDensity s) (firstOrder s) (indexColumnDensity s) (firstExponent s + 1)
noncomputable def coordinateOutputDensity (s : ℕ) : ℝ :=
  yLoss (errorDensity s) (secondOrder s) (coordinateDensity s)
    (firstExponent s + 1 + dimensionLog s)

theorem error_bounds (s : ℕ) : 0 ≤ errorDensity s ∧ errorDensity s ≤ 1 / 256 := by
  have hr : 1 ≤ dimensionLog s := Nat.one_le_pow _ _ (by omega)
  have hd : (2 : ℝ) ≤ dimension s := by
    exact_mod_cast ExactSamplerInstances.two_le_width hr
  have hp : (256 : ℝ) ≤ (dimension s : ℝ) ^ 8 := by
    convert pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hd 8 using 1
    norm_num
  constructor
  · unfold errorDensity; positivity
  · exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp

theorem coordinateDensity_eq (s : ℕ) :
    coordinateDensity s = 1 / (dimensionLog s : ℝ) ^ 3 := by
  simp only [coordinateDensity, dimensionLog, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul]
  congr 2
  omega

theorem coordinate_density_gates {s : ℕ} (hs : 2 ≤ s) :
    0 < coordinateDensity s ∧ 0 ≤ 1 - 8 * coordinateDensity s ∧
    coordinateDensity s ≤ (1 - 8 * coordinateDensity s) / 2 ∧
    (1 + errorDensity s) * (3 / 5 : ℝ) ^ 2 ≤ (1 - 8 * coordinateDensity s) / 2 := by
  have hh : coordinateDensity s ≤ 1 / 64 := by
    have hp : (64 : ℝ) ≤ (2 : ℝ) ^ (3 * s) := by
      convert pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (by omega : 6 ≤ 3 * s) using 1
      norm_num
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp
  have hpos : 0 < coordinateDensity s := by unfold coordinateDensity; positivity
  have he := (error_bounds s).2
  refine ⟨hpos, ?_, ?_, ?_⟩ <;> nlinarith

theorem index_density_gates (s : ℕ) :
    0 < indexRowDensity s ∧ indexRowDensity s ≤ 1 ∧
    0 < indexColumnDensity s ∧ indexStoppingDensity s ≤ 1 ∧
    (2 : ℝ) ^ firstResidualExponent s * indexRowDensity s ≤ 1 ∧
    indexColumnDensity s ≤ ExactNumericGates.rowDensity (dimensionLog s) := by
  have hp : (1 : ℝ) ≤ 2 ^ firstResidualExponent s := one_le_pow₀ (by norm_num)
  have hq : (1 : ℝ) ≤ 2 ^ (3 * dimensionLog s) := one_le_pow₀ (by norm_num)
  have ht : (1 : ℝ) ≤ firstOrder s := by
    have hp : 0 < firstOrder s := by unfold firstOrder dimensionLog; positivity
    exact_mod_cast hp
  refine ⟨by unfold indexRowDensity; positivity, ?_,
    by unfold indexColumnDensity; positivity, ?_, ?_, ?_⟩
  · exact (div_le_one (by positivity)).mpr hp
  · have hh : indexColumnDensity s ≤ 1 := (div_le_one (by positivity)).mpr hq
    exact (div_le_one (by positivity)).mpr (by linarith)
  · unfold indexRowDensity
    field_simp
    exact le_refl _
  · unfold indexColumnDensity ExactNumericGates.rowDensity
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)

open ExactFiniteReduction ExactNumericGates

/-- Every scalar gate in the finite reduction, supplied by the literal
manuscript formulas. Only the two numerical list-length lower bounds are
inputs here; the next definition supplies the actual trace-list lengths. -/
noncomputable def parameters (s : ℕ) (hs : 2 ^ 21 ≤ s) (N₁ N₂ : ℕ)
    (hN₁ : (dimension s) ^ 64 ≤ N₁) (hN₂ : (dimension s) ^ 6 ≤ N₂) :
    NumericParameters := by
  have hs128 : 128 ≤ s := by omega
  have hs8 : 8 ≤ s := by omega
  have hr64 : 64 ≤ dimensionLog s := by
    have hp := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) (by omega : 6 ≤ s)
    simpa [dimensionLog] using hp
  have hr1 : 1 ≤ dimensionLog s := by omega
  have hmlow := secondExponent_lower (s := s) (by omega)
  have hmhigh := secondExponent_upper (s := s) (by omega)
  have hpower := linear_lt_power (s := s) (by omega)
  have hm : 2 ^ 20 ≤ secondExponent s := by omega
  have hres : secondExponent s + 1 ≤ dimensionLog s := by omega
  have hε0 := (error_bounds s).1
  have hεSmall := (error_bounds s).2
  have hε1 : errorDensity s ≤ 1 := by linarith
  have hidx := index_density_gates s
  have hindexLoss := ExactLossGates.indexing_density hs128 hε0 hε1
  have hcoordLoss := ExactLossGates.coordinate_density hs128
    (secondOrder_lower (s := s) (by omega)) hε0 hε1
  have hcoordRows := ExactLossGates.coordinate_rows hs128
    (secondOrder_lower (s := s) (by omega)) hε0 hε1
  have hcoordSeed := ExactHardSeedGate.column_density_le hs hmlow
    (hmhigh.trans (Nat.sub_le _ _)) hε0 hε1
  have hdensity := density_gates hr1 (by omega : secondExponent s ≤ dimensionLog s)
  have hcoordCounts := coordinate_gates (by omega : 5 ≤ dimensionLog s)
    (by omega : 5 ≤ secondExponent s) hres
  have hcoord := coordinate_density_gates (s := s) (by omega)
  have hrows :=
    row_gates (r := dimensionLog s) (m := secondExponent s) (N := N₁) hr1
  have hd : 1 ≤ dimension s := Nat.one_le_pow _ _ (by omega)
  have hNsmall : (2 ^ dimensionLog s) ^ 2 ≤ N₁ :=
    (Nat.pow_le_pow_right hd (by omega : 2 ≤ 64)).trans hN₁
  have hpairs := pair_gates (by omega : 4 ≤ dimensionLog s) hNsmall
  have hretained := retained_density (by omega : 4 ≤ dimensionLog s) hNsmall
    (show errorDensity s ≤ 1 / 4 by linarith)
  have hbin := ExactBinNumericGates.exact_bin_gates hr64 hN₂
  rw [← coordinateDensity_eq s] at hbin
  have hwReal : (width (firstExponent s) : ℝ) = 2 * (dimensionLog s : ℝ) ^ 2 := by
    exact_mod_cast firstWidth_exact s
  refine {
    a := firstExponent s
    r := dimensionLog s
    N₁ := N₁
    N₂ := N₂
    t₁ := firstOrder s
    m₁ := firstOrderExponent s
    R₁ := firstResidualExponent s
    p₁ := firstStoppingRows s
    m₂ := secondExponent s
    τ := pairThreshold (dimensionLog s) N₁
    xIndex := indexRowDensity s
    yIndex := indexOutputDensity s
    hIndex := indexColumnDensity s
    zIndex := indexStoppingDensity s
    x := rowDensity (dimensionLog s)
    h := coordinateDensity s
    ε := errorDensity s
    yzero := coordinateOutputDensity s
    a₀ := excessDensity (dimensionLog s) (secondExponent s)
    ha := by unfold firstExponent; omega
    haeq := firstResidual_sum (by omega)
    hR₁ := by unfold firstResidualExponent; omega
    hwidth := firstWidth_split (by omega)
    ht₁ := by unfold firstOrder dimensionLog; positivity
    hm₁ := by unfold firstOrderExponent; omega
    hlocalOrder := ?_
    hxIndex := hidx.1
    hxIndexOne := hidx.2.1
    hyIndex := hindexLoss.1
    hyIndexOne := hindexLoss.2
    hhIndex := hidx.2.2.1
    hzIndexOne := hidx.2.2.2.1
    hε := hε0
    hpLow := by unfold firstOrder firstStoppingRows; omega
    hpHigh := by unfold firstOrder firstStoppingRows; omega
    hpFraction := firstStopping_fraction s
    hw := ?_
    hindexRank := indexStopping_rank (by omega)
    hindexOne := ?_
    hindexSeed := indexStopping_seed hε0 hε1
    hindexRows := hidx.2.2.2.2.1
    hindexDensity := hidx.2.2.2.2.2
    hx := hdensity.1
    hxOne := hdensity.2.1
    hyzeroOne := hcoordLoss.2
    hnonconstantRows := ?_
    hm₂ := hm
    hResidual := hres
    hscale := hdensity.2.2.1
    hh := hcoord.1
    hσ := hcoord.2.1
    ha₀ := hdensity.2.2.2.2
    hcoordinateOne := le_refl _
    hcoordinateSeed := hcoordSeed
    hcoordinateSmall := hdensity.2.2.2.1
    hcoordinateFull := hcoordCounts.1
    hcoordinateHalf := hcoordCounts.2
    hhalf := hcoord.2.2.1
    hproject := hcoord.2.2.2
    hsmallRow := hrows.1
    hsmallOddRow := hrows.2.1
    hlargeRow := hrows.2.2.1
    hbaseRow := hrows.2.2.2.1
    hexcessRow := hrows.2.2.2.2.1
    hexcessFinal := hrows.2.2.2.2.2
    hpairRow := hpairs.1
    hτ := hpairs.2.1
    hgap := hpairs.2.2
    hbin := hbin.1
    hbinLoss := hbin.2.1
    hsurvive := ?_
    hdensity := hretained
  }
  · have hn := naming_exponent_bound (s := s) (by omega)
    unfold firstOrder
    omega
  · rw [firstWidth_exact]
    nlinarith
  · have he : firstResidualExponent s + (firstOrderExponent s + 1) =
        firstExponent s + 1 := by
      have hh := firstResidual_sum (s := s) (by omega)
      omega
    rw [he]
    exact le_refl _
  · simpa only [firstStoppingRows, firstExponent, dimensionLog, width,
      Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hcoordRows
  · rw [hwReal]
    exact hbin.2.2

open SmallBiasSampler Workspace.Types.CommComplexity

def firstListSize (s : ℕ) : ℕ :=
  exactFirstSize (firstExponent s) (firstOrder s) (dimension s)

def secondListSize (s : ℕ) : ℕ :=
  exactSecondSize (firstExponent s) (secondOrder s) (dimension s)

theorem actual_size_bounds {s : ℕ} (hs : 8 ≤ s) :
    ((dimension s) ^ 64 ≤ firstListSize s ∧ firstListSize s ≤ (dimension s) ^ 300) ∧
    ((dimension s) ^ 6 ≤ secondListSize s ∧ secondListSize s ≤ (dimension s) ^ 100) := by
  have ha : 2 ≤ firstExponent s := by unfold firstExponent; omega
  have hr : 1 ≤ dimensionLog s := Nat.one_le_pow _ _ (by omega)
  have har := naming_exponent_bound (s := s) (by omega)
  have hsmall : firstExponent s ≤ dimension s := by
    have hpow : dimensionLog s < dimension s := Nat.lt_two_pow_self
    omega
  obtain ⟨htLow, htHigh, htq, huLow, huHigh, huq⟩ := sampler_order_gates hs
  constructor
  · exact ExactSamplerInstances.firstSize_bounds hr
      (ExactSamplerInstances.firstWidth_le ha har) htq htLow htHigh
  · exact ExactSamplerInstances.secondSize_bounds (by omega) hr hsmall huq huLow huHigh

/-- All parameters and both list lengths are fixed from the one integer `s`.
This is no longer an assumed numerical certificate. -/
noncomputable def actualParameters (s : ℕ) (hs : 2 ^ 21 ≤ s) : NumericParameters :=
  parameters s hs (firstListSize s) (secondListSize s)
    (actual_size_bounds (by omega : 8 ≤ s)).1.1
    (actual_size_bounds (by omega : 8 ≤ s)).2.1

theorem actualParameters_r (s : ℕ) (hs : 2 ^ 21 ≤ s) :
    (actualParameters s hs).r = dimensionLog s := rfl

theorem actualParameters_a (s : ℕ) (hs : 2 ^ 21 ≤ s) :
    (actualParameters s hs).a = firstExponent s := rfl

theorem actualParameters_N₁ (s : ℕ) (hs : 2 ^ 21 ≤ s) :
    (actualParameters s hs).N₁ = firstListSize s := rfl

theorem actualParameters_N₂ (s : ℕ) (hs : 2 ^ 21 ≤ s) :
    (actualParameters s hs).N₂ = secondListSize s := rfl

theorem actual_r_pos (s : ℕ) (hs : 2 ^ 21 ≤ s) :
    1 ≤ (actualParameters s hs).r := Nat.one_le_pow _ _ (by omega)

/-- The literal finite graph matrix, with the actual two field-pair samplers.
Its construction is independent of the graph's colourability. -/
noncomputable def actualMatrix (s : ℕ) (hs : 2 ^ 21 ≤ s) {n d : ℕ}
    (e : Fin d → Fin 2 → Fin n) :
    Rows (secondListSize s) (5 * n) → Columns (dimension s) (firstListSize s) → Bool :=
  let p := actualParameters s hs
  matrix p.ha
    (ExactSamplerInstances.firstFamilyFor p (actual_r_pos s hs) rfl)
    (ExactSamplerInstances.secondFamilyFor p (actual_r_pos s hs) rfl)
    (sourceVectors (dimension s) e) (sourceVectors_cap (dimension s) e)

/-- Unconditional numerical and sampler instantiation of the finite
decision equivalence. Only enough coordinates for five graph copies and
distinct endpoints are required of the source encoding. -/
theorem actual_decision_equivalence (s : ℕ) (hs : 2 ^ 21 ≤ s) {n d : ℕ}
    (e : Fin d → Fin 2 → Fin n) (hD : 5 * d ≤ dimension s)
    (hinj : ∀ α, Function.Injective (e α)) :
    D (actualMatrix s hs e) ≤ firstExponent s + 1 + dimensionLog s + 2 ↔
      ∃ colour : Fin n → Fin 4, ∀ α : Fin d, colour (e α 0) ≠ colour (e α 1) :=
  ExactSamplerInstances.decision_equivalence (actualParameters s hs)
    (actual_r_pos s hs) rfl rfl rfl e hD hinj

/-- The exact adjacent costs, for the same matrix in both cases. -/
theorem actual_finite_gap (s : ℕ) (hs : 2 ^ 21 ≤ s) {n d : ℕ}
    (e : Fin d → Fin 2 → Fin n) (hD : 5 * d ≤ dimension s)
    (hinj : ∀ α, Function.Injective (e α)) :
    (∀ colour : Fin n → Fin 4, (∀ α : Fin d, colour (e α 0) ≠ colour (e α 1)) →
      D (actualMatrix s hs e) = firstExponent s + 1 + dimensionLog s + 2) ∧
    ((∀ colour : Fin n → Fin 4, ∃ α : Fin d, colour (e α 0) = colour (e α 1)) →
      D (actualMatrix s hs e) = firstExponent s + 1 + dimensionLog s + 3) := by
  let p := actualParameters s hs
  exact ExactFiniteReduction.finite_gap p
    (ExactSamplerInstances.firstFamilyFor p (actual_r_pos s hs) rfl)
    (ExactSamplerInstances.secondFamilyFor p (actual_r_pos s hs) rfl)
    (ExactSamplerInstances.firstFamilyFor_balanced p (actual_r_pos s hs) rfl rfl)
    (ExactSamplerInstances.secondFamilyFor_balanced p (actual_r_pos s hs) rfl rfl)
    e hD hinj

/-- Table size for the identical actual matrix. This is a cardinality
theorem, not a claim of polynomial-time finite-field implementation. -/
theorem actual_matrix_size {s : ℕ} (hs : 2 ^ 21 ≤ s) (n : ℕ) :
    Fintype.card (Rows (secondListSize s) (5 * n)) *
      Fintype.card (Columns (dimension s) (firstListSize s)) ≤
      8 * (4 * (dimension s) ^ 100 + 5 * n) * (dimension s) ^ 1204 := by
  have ha : 2 ≤ firstExponent s := by unfold firstExponent; omega
  have hr : 1 ≤ dimensionLog s := Nat.one_le_pow _ _ (by omega)
  have har := naming_exponent_bound (s := s) (by omega)
  have hsmall : firstExponent s ≤ dimension s := by
    have hpow : dimensionLog s < dimension s := Nat.lt_two_pow_self
    omega
  obtain ⟨_, htHigh, _, _, huHigh, _⟩ := sampler_order_gates (s := s) (by omega)
  exact ExactSamplerInstances.matrix_size_polynomial (by omega) hr
    (ExactSamplerInstances.firstWidth_le ha har) hsmall htHigh huHigh

/-- The one fixed matrix assigned to an arbitrary finite loopless graph.
Padding, numerical parameters, and sampler labels are all supplied here. -/
noncomputable def sourceMatrix {n d : ℕ} (e : Fin d → Fin 2 → Fin n) :=
  actualMatrix (ExactSourcePadding.paddedExponent d) (ExactSourcePadding.cutoff d) e

def sourceThreshold (edges : ℕ) : ℕ :=
  firstExponent (ExactSourcePadding.paddedExponent edges) + 1 +
    dimensionLog (ExactSourcePadding.paddedExponent edges) + 2

/-- Fully instantiated finite graph reduction. There are no supplied
samplers, density gates, rank bounds, or communication profiles. This does
not yet assert bit-computability of the finite-field representation. -/
theorem source_decision_equivalence {n d : ℕ} (e : Fin d → Fin 2 → Fin n)
    (hinj : ∀ α, Function.Injective (e α)) :
    D (sourceMatrix e) ≤ sourceThreshold d ↔
      ∃ colour : Fin n → Fin 4, ∀ α : Fin d, colour (e α 0) ≠ colour (e α 1) :=
  actual_decision_equivalence (ExactSourcePadding.paddedExponent d)
    (ExactSourcePadding.cutoff d) e (ExactSourcePadding.coverage d) hinj

/-- The same unconditional instance has an exact one-bit YES/NO gap. -/
theorem source_finite_gap {n d : ℕ} (e : Fin d → Fin 2 → Fin n)
    (hinj : ∀ α, Function.Injective (e α)) :
    (∀ colour : Fin n → Fin 4, (∀ α : Fin d, colour (e α 0) ≠ colour (e α 1)) →
      D (sourceMatrix e) = sourceThreshold d) ∧
    ((∀ colour : Fin n → Fin 4, ∃ α : Fin d, colour (e α 0) = colour (e α 1)) →
      D (sourceMatrix e) = sourceThreshold d + 1) := by
  simpa only [sourceMatrix, sourceThreshold, Nat.add_assoc] using
    actual_finite_gap (ExactSourcePadding.paddedExponent d)
      (ExactSourcePadding.cutoff d) e (ExactSourcePadding.coverage d) hinj

/-- A fixed polynomial bound on the literal table's cardinality in source
vertices and edges. The enormous coefficient is an absolute cutoff only. -/
theorem source_matrix_size (n d : ℕ) :
    let s := ExactSourcePadding.paddedExponent d
    let B := ExactSourcePadding.paddingConstant * (2 * max 1 (5 * d)) ^ 2
    Fintype.card (Rows (secondListSize s) (5 * n)) *
      Fintype.card (Columns (dimension s) (firstListSize s)) ≤
      8 * (4 * B ^ 100 + 5 * n) * B ^ 1204 := by
  dsimp only
  have hbound := ExactSourcePadding.dimension_le_polynomial d
  have hsize := actual_matrix_size (ExactSourcePadding.cutoff d) n
  apply hsize.trans
  change dimension (ExactSourcePadding.paddedExponent d) ≤ _ at hbound
  gcongr

end EthInapproximability.CurrentPaper.ExactParameters
