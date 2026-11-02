import EthInapproximability.CurrentPaper.DensityBucket

/-!
# Numerical bounds for the selected diagonal rows

Source: frozen v8 `A-stage4-details.tex`,
`eq:paper-early-dyadic-class` and its use in
`lem:paper-early-protected-closure`.

The selected density class has width `u`; half of these coordinates are
retained by template extraction. The statements below derive the width,
block count and row threshold needed for localized stopping. They contain
no communication-complexity hypotheses or conclusions.
-/

namespace EthInapproximability.CurrentPaper.ReceivingCapacityNumerics

variable {r B s κ : ℕ} {J : Finset (Fin (2 ^ r))}
    {density : Fin (2 ^ r) → ℝ}

/-- Halving the selected dyadic width subtracts exactly one exponent. -/
theorem half_width (sel : DensityBucket.Selection J density B s κ) :
    2 ^ sel.widthExponent / 2 = 2 ^ (sel.widthExponent - 1) := by
  have he : sel.widthExponent - 1 + 1 = sel.widthExponent := by
    have := sel.exponent_ge_four
    omega
  have hp : (2 : ℕ) ^ sel.widthExponent = 2 ^ (sel.widthExponent - 1) * 2 := by
    calc
      (2 : ℕ) ^ sel.widthExponent = 2 ^ (sel.widthExponent - 1 + 1) := by
        exact congrArg (fun n => (2 : ℕ) ^ n) he.symm
      _ = 2 ^ (sel.widthExponent - 1) * 2 := pow_succ _ _
  rw [hp]
  omega

/-- The whole selected inner width has the literal power-of-two form
required by localized stopping. -/
theorem packet_width (sel : DensityBucket.Selection J density B s κ)
    {qexp m : ℕ} (hm : m ≤ qexp) :
    (2 ^ sel.widthExponent / 2) * 2 ^ qexp =
      2 ^ (sel.widthExponent - 1 + qexp - m) * 2 ^ m := by
  rw [half_width sel, ← pow_add, ← pow_add]
  congr 1
  omega

/-- The class-width inequality supplies at least `K` usable coordinate
blocks after half the donors and half their row density are retained. -/
theorem packet_block_count (sel : DensityBucket.Selection J density B s κ)
    {qexp kexp m : ℕ} (hm : m ≤ kexp)
    (hK : 2 ^ kexp = s * κ * 2 ^ qexp) :
    (2 : ℝ) ^ (kexp - m + m) ≤
      ((2 ^ sel.widthExponent / 2 : ℕ) : ℝ) *
        ((1 / (2 : ℝ) ^ sel.classExponent) / 2) * (2 : ℝ) ^ qexp / 2 := by
  rw [Nat.sub_add_cancel hm, half_width sel]
  have hKR : (2 : ℝ) ^ kexp = (s : ℝ) * κ * (2 : ℝ) ^ qexp := by
    exact_mod_cast hK
  have he : sel.widthExponent - 1 + 1 = sel.widthExponent := by
    have := sel.exponent_ge_four
    omega
  have hwidth : (2 : ℝ) ^ sel.widthExponent =
      (2 : ℝ) ^ (sel.widthExponent - 1) * 2 := by
    calc
      (2 : ℝ) ^ sel.widthExponent = 2 ^ (sel.widthExponent - 1 + 1) := by
        exact congrArg (fun n => (2 : ℝ) ^ n) he.symm
      _ = 2 ^ (sel.widthExponent - 1) * 2 := pow_succ _ _
  have hscaled := mul_le_mul_of_nonneg_right sel.width_lower
    (show (0 : ℝ) ≤ (2 : ℝ) ^ qexp by positivity)
  rw [hwidth] at hscaled
  push_cast
  rw [hKR]
  nlinarith

/-- The block count in particular fits inside the complete selected width,
so the stopping exponent is within the ambient exponent. -/
theorem packet_exponent_le (sel : DensityBucket.Selection J density B s κ)
    {qexp kexp m : ℕ} (hm : m ≤ kexp)
    (hK : 2 ^ kexp = s * κ * 2 ^ qexp) :
    kexp - m ≤ sel.widthExponent - 1 + qexp - m := by
  have hcount := packet_block_count sel hm hK
  rw [Nat.sub_add_cancel hm, half_width sel] at hcount
  have hdc : 1 / (2 : ℝ) ^ sel.classExponent ≤ 1 := by
    apply (div_le_one (by positivity : (0 : ℝ) < (2 : ℝ) ^ sel.classExponent)).mpr
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hvq : (0 : ℝ) ≤ (2 : ℝ) ^ (sel.widthExponent - 1) * (2 : ℝ) ^ qexp :=
    by positivity
  have hprod := mul_le_mul_of_nonneg_right hdc hvq
  push_cast at hcount
  have hpow : (2 : ℝ) ^ kexp ≤ (2 : ℝ) ^ (sel.widthExponent - 1 + qexp) := by
    rw [pow_add]
    nlinarith
  have hexp := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hpow
  omega

/-- A single scalar parameter gate and the selected class's density bound
give the physical packet's row threshold. -/
theorem packet_row_threshold (sel : DensityBucket.Selection J density B s κ)
    {qexp kexp m : ℕ} {x : ℝ} (hm : m ≤ kexp)
    (hK : 2 ^ kexp = s * κ * 2 ^ qexp)
    (hgate : (2 : ℝ) ^ r * (2 : ℝ) ^ qexp * x ≤
      8 * (B : ℝ) * (r + 2 : ℕ)) :
    (2 : ℝ) ^ (kexp - m + m) * x ≤
      ((1 / (2 : ℝ) ^ sel.classExponent) / 2) / 2 := by
  rw [Nat.sub_add_cancel hm]
  have hKR : (2 : ℝ) ^ kexp = (s : ℝ) * κ * (2 : ℝ) ^ qexp := by
    exact_mod_cast hK
  have hrpos : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
  have hdensity := (div_le_iff₀ hrpos).mp sel.density_lower
  have hscaled := mul_le_mul_of_nonneg_right hgate
    (show (0 : ℝ) ≤ (s : ℝ) * κ by positivity)
  have hfour : 4 * ((2 : ℝ) ^ kexp * x) ≤ 1 / (2 : ℝ) ^ sel.classExponent := by
    apply le_of_mul_le_mul_right (a := (2 : ℝ) ^ r) _ hrpos
    calc
      4 * ((2 : ℝ) ^ kexp * x) * (2 : ℝ) ^ r =
          4 * (((2 : ℝ) ^ r * (2 : ℝ) ^ qexp * x) * ((s : ℝ) * κ)) := by
            rw [hKR]
            ring
      _ ≤ 4 * ((8 * (B : ℝ) * (r + 2 : ℕ)) * ((s : ℝ) * κ)) :=
        mul_le_mul_of_nonneg_left hscaled (by norm_num)
      _ = 32 * (B : ℝ) * (r + 2 : ℕ) * s * κ := by ring
      _ ≤ (1 / (2 : ℝ) ^ sel.classExponent) * (2 : ℝ) ^ r := hdensity
  linarith

/-- All four numerical premises for the physical packet follow from the
selected class, the intended value of `K`, and the scalar row gate. -/
theorem packet_stopping_numerics (sel : DensityBucket.Selection J density B s κ)
    {qexp kexp m : ℕ} {x : ℝ} (hmq : m ≤ qexp) (hmk : m ≤ kexp)
    (hK : 2 ^ kexp = s * κ * 2 ^ qexp)
    (hgate : (2 : ℝ) ^ r * (2 : ℝ) ^ qexp * x ≤
      8 * (B : ℝ) * (r + 2 : ℕ)) :
    (2 ^ sel.widthExponent / 2) * 2 ^ qexp =
      2 ^ (sel.widthExponent - 1 + qexp - m) * 2 ^ m ∧
    kexp - m ≤ sel.widthExponent - 1 + qexp - m ∧
    (2 : ℝ) ^ (kexp - m + m) ≤
      ((2 ^ sel.widthExponent / 2 : ℕ) : ℝ) *
        ((1 / (2 : ℝ) ^ sel.classExponent) / 2) * (2 : ℝ) ^ qexp / 2 ∧
    (2 : ℝ) ^ (kexp - m + m) * x ≤
      ((1 / (2 : ℝ) ^ sel.classExponent) / 2) / 2 := by
  exact ⟨packet_width sel hmq, packet_exponent_le sel hmk hK,
    packet_block_count sel hmk hK, packet_row_threshold sel hmk hK hgate⟩

end EthInapproximability.CurrentPaper.ReceivingCapacityNumerics
