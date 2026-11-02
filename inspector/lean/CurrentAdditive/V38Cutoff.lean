import CurrentAdditive.V38Schedule
import CurrentAdditive.DeterministicParameters

namespace V38Cutoff

open V38Schedule

#check V38Schedule.generated_product_exact
#check CurrentAdditive.DeterministicParameters.coefficient_mul_s_le_N

theorem ebar_unit (b : ℕ) :
    ebar b 1 = 2 ^ 90 * 2 ^ ((b + 63) / 64) := by
  unfold ebar
  simp only [one_pow, div_one]
  have hc : (2 ^ 90 : ℚ) * (2 ^ ((b + 63) / 64) : ℚ) =
      ((2 ^ 90 * 2 ^ ((b + 63) / 64) : ℕ) : ℚ) := by
    push_cast
    ring
  rw [hc]
  exact Nat.ceil_natCast _

/-- The moving tolerance contributes only a fixed coefficient and `s²`.
This is the revised v38 exceptional budget, with no real-power oracle. -/
def toleranceCoefficient (c : ℚ) : ℕ := Nat.ceil ((2 ^ 92 : ℚ) / c ^ 2)
def restorationCoefficient (c : ℚ) : ℕ := Nat.ceil ((2 ^ 100 : ℚ) / c ^ 2)

theorem ebar_half_eta_bound (b s : ℕ) (c : ℚ)
    (hc : 0 < c) (hs : 0 < s) :
    ebar b (c / (2 * s)) ≤
      toleranceCoefficient c * s ^ 2 * 2 ^ ((b + 63) / 64) := by
  let t := (b + 63) / 64
  let K := toleranceCoefficient c
  have hsQ : (0 : ℚ) < s := by exact_mod_cast hs
  have hτ : (0 : ℚ) < c / (2 * s) := by positivity
  have hK : (2 ^ 92 : ℚ) / c ^ 2 ≤ K := Nat.le_ceil _
  have heq : (2 ^ 90 : ℚ) / (c / (2 * s)) ^ 2 =
      ((2 ^ 92 : ℕ) : ℚ) / c ^ 2 * s ^ 2 := by
    field_simp
    ring
  unfold ebar
  apply (Nat.ceil_le).2
  have hpow : (0 : ℚ) ≤ (2 ^ t : ℕ) := by positivity
  have hsq : (0 : ℚ) ≤ (s : ℚ) ^ 2 := by positivity
  have hbound : (2 ^ 90 : ℚ) / (c / (2 * s)) ^ 2 ≤ (K : ℚ) * s ^ 2 := by
    rw [heq]
    nlinarith [mul_le_mul_of_nonneg_right hK hsq]
  have hmul := mul_le_mul_of_nonneg_right hbound hpow
  convert hmul using 1 <;> push_cast <;> ring

theorem ebar_restoration_bound (b s w : ℕ) (c : ℚ)
    (hc : 0 < c) (hs : 0 < s) (hw : 0 < w) :
    ebar b (c / (32 * s * w)) ≤
      restorationCoefficient c * s ^ 2 * w ^ 2 * 2 ^ ((b + 63) / 64) := by
  let t := (b + 63) / 64
  let K := restorationCoefficient c
  have hsQ : (0 : ℚ) < s := by exact_mod_cast hs
  have hwQ : (0 : ℚ) < w := by exact_mod_cast hw
  have hK : (2 ^ 100 : ℚ) / c ^ 2 ≤ K := Nat.le_ceil _
  have heq : (2 ^ 90 : ℚ) / (c / (32 * s * w)) ^ 2 =
      ((2 ^ 100 : ℕ) : ℚ) / c ^ 2 * s ^ 2 * w ^ 2 := by
    field_simp
    ring
  unfold ebar
  apply (Nat.ceil_le).2
  have hpow : (0 : ℚ) ≤ (2 ^ t : ℕ) := by positivity
  have hsq : (0 : ℚ) ≤ (s : ℚ) ^ 2 * w ^ 2 := by positivity
  have hbound : (2 ^ 90 : ℚ) / (c / (32 * s * w)) ^ 2 ≤
      (K : ℚ) * s ^ 2 * w ^ 2 := by
    rw [heq]
    nlinarith [mul_le_mul_of_nonneg_right hK hsq]
  have hmul := mul_le_mul_of_nonneg_right hbound hpow
  convert hmul using 1 <;> push_cast <;> ring

theorem coefficient_le_power (K : ℕ) : K ≤ 2 ^ K := by
  induction K with
  | zero => norm_num
  | succ K ih =>
      rw [pow_succ]
      have hp : 1 ≤ 2 ^ K := by
        have h : 0 < 2 ^ K := by positivity
        omega
      omega

theorem generated_owner_ebar_budget (c : ℚ) (L : ℕ)
    (hc : 0 < c) (hL : 4 * toleranceCoefficient c + 800 ≤ L) :
    8 * ebar (9 + generatedQlog L) (c / (2 * generatedS L)) ≤
      generatedW L := by
  let K := toleranceCoefficient c
  let t := (9 + 6 * L + 63) / 64
  let u := quarterCeil L
  have hs : 0 < generatedS L := by unfold generatedS; positivity
  have he := ebar_half_eta_bound (9 + generatedQlog L)
    (generatedS L) c hc hs
  have hK : K ≤ 2 ^ K := coefficient_le_power K
  have hExp : 3 + K + 2 * u + t ≤ 2 * L := by
    dsimp [u, t, quarterCeil]
    omega
  have hsPow : (generatedS L) ^ 2 = 2 ^ (2 * u) := by
    simp only [generatedS, u]
    rw [← pow_mul]
    congr 1
    omega
  have hwPow : generatedW L = 2 ^ (2 * L) := by
    simp only [generatedW, generatedN]
    rw [← pow_mul]
    congr 1
    omega
  calc
    8 * ebar (9 + generatedQlog L) (c / (2 * generatedS L)) ≤
        8 * (K * (generatedS L) ^ 2 * 2 ^ t) := by
      have ht : t = (9 + generatedQlog L + 63) / 64 := by
        simp only [t, generatedQlog]
      rw [ht]
      exact Nat.mul_le_mul_left 8 he
    _ ≤ 8 * (2 ^ K * (generatedS L) ^ 2 * 2 ^ t) := by
      gcongr
    _ = 2 ^ (3 + K + 2 * u + t) := by
      rw [hsPow, pow_add, pow_add, pow_add]
      norm_num
      ring
    _ ≤ generatedW L := by
      rw [hwPow]
      exact Nat.pow_le_pow_right (by decide) hExp

theorem generated_Eexc_quarter (c : ℚ) (L : ℕ)
    (hc : 0 < c) (hL : 4 * toleranceCoefficient c + 800 ≤ L) :
    Eexc (generatedQlog L) (generatedEta c L) ≤ generatedW L / 4 := by
  have h := generated_owner_ebar_budget c L hc hL
  have harg : generatedEta c L / 2 = c / (2 * generatedS L) := by
    unfold generatedEta
    ring
  rw [← harg] at h
  unfold Eexc e0 at *
  omega

theorem generated_restoration_ebar_budget (c : ℚ) (L : ℕ)
    (hc : 0 < c) (hL : 4 * restorationCoefficient c + 800 ≤ L) :
    128 * (ebar L (c / (32 * generatedS L * generatedW L)) + 1) ≤
      generatedQ L := by
  let K := restorationCoefficient c
  let u := quarterCeil L
  let t := (L + 63) / 64
  have hs : 0 < generatedS L := by unfold generatedS; positivity
  have hw : 0 < generatedW L := by unfold generatedW generatedN; positivity
  have hKpos : 0 < K := by
    have hrat : (0 : ℚ) < (2 ^ 100 : ℚ) / c ^ 2 := by positivity
    have hceil : (2 ^ 100 : ℚ) / c ^ 2 ≤ K := Nat.le_ceil _
    exact_mod_cast (lt_of_lt_of_le hrat hceil)
  have hK : K ≤ 2 ^ K := coefficient_le_power K
  have hExp : 8 + K + 2 * u + 4 * L + t ≤ 6 * L := by
    dsimp [u, t, quarterCeil]
    omega
  have hEB := ebar_restoration_bound L (generatedS L) (generatedW L) c hc hs hw
  change ebar L (c / (32 * generatedS L * generatedW L)) ≤
    K * generatedS L ^ 2 * generatedW L ^ 2 * 2 ^ t at hEB
  have hsPow : (generatedS L) ^ 2 = 2 ^ (2 * u) := by
    simp only [generatedS, u]
    rw [← pow_mul]
    congr 1
    omega
  have hwPow : (generatedW L) ^ 2 = 2 ^ (4 * L) := by
    simp only [generatedW, generatedN]
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  have hQPow : generatedQ L = 2 ^ (6 * L) := generatedQ_pow L
  have hBpos : 1 ≤ K * generatedS L ^ 2 * generatedW L ^ 2 * 2 ^ t := by
    have hp : 0 < K * generatedS L ^ 2 * generatedW L ^ 2 * 2 ^ t := by positivity
    omega
  calc
    128 * (ebar L (c / (32 * generatedS L * generatedW L)) + 1) ≤
        128 * (K * generatedS L ^ 2 * generatedW L ^ 2 * 2 ^ t + 1) := by
      exact Nat.mul_le_mul_left 128 (Nat.add_le_add_right hEB 1)
    _ ≤ 256 * (K * generatedS L ^ 2 * generatedW L ^ 2 * 2 ^ t) := by omega
    _ ≤ 256 * (2 ^ K * generatedS L ^ 2 * generatedW L ^ 2 * 2 ^ t) := by
      gcongr
    _ = 2 ^ (8 + K + 2 * u + 4 * L + t) := by
      rw [hsPow, hwPow, pow_add, pow_add, pow_add, pow_add]
      norm_num
      ring
    _ ≤ generatedQ L := by
      rw [hQPow]
      exact Nat.pow_le_pow_right (by decide) hExp

theorem ebar_generated_x_formula (L : ℕ) :
    ebar (8 * L) 1 = 2 ^ (90 + (L + 7) / 8) := by
  rw [ebar_unit, ← pow_add]
  congr 1
  omega

theorem generated_x_ebar_budget (L : ℕ) (hL : 800 ≤ L) :
    128 * ebar (8 * L) 1 ≤ generatedS L := by
  rw [ebar_generated_x_formula]
  unfold generatedS quarterCeil
  have he : 7 + (90 + (L + 7) / 8) ≤ (L + 3) / 4 := by omega
  calc
    128 * 2 ^ (90 + (L + 7) / 8) = 2 ^ (7 + (90 + (L + 7) / 8)) := by
      rw [pow_add]
      norm_num [pow_add]
    _ ≤ 2 ^ ((L + 3) / 4) := Nat.pow_le_pow_right (by decide) he

theorem generated_extra_ebar_tests (c : ℚ) (L : ℕ)
    (hc : 0 < c)
    (hL : max 800 (4 * restorationCoefficient c + 800) ≤ L) :
    ebar (8 * L) 1 ≤ generatedS L / 128 ∧
    generatedQ L ≥ 128 *
      (ebar L (deltaU (generatedEta c L) (generatedW L) / 2) + 1) := by
  have hx := generated_x_ebar_budget L ((le_max_left _ _).trans hL)
  have hr := generated_restoration_ebar_budget c L hc ((le_max_right _ _).trans hL)
  have harg : deltaU (generatedEta c L) (generatedW L) / 2 =
      c / (32 * generatedS L * generatedW L) := by
    unfold deltaU generatedEta
    ring
  rw [← harg] at hr
  constructor
  · omega
  · exact hr

/-- The exact dyadic ceiling fits the source coordinates for every graph
whose edge count obeys the bounded-degree promise. -/
theorem generated_source_width (L n m Δ : ℕ)
    (hn : n ≤ generatedN L) (hdegree : 2 * m ≤ Δ * n)
    (hL : 4 * Δ + 4 ≤ L) :
    pow2Ceil (4 * generatedS L * m) ≤ generatedQ₂ L := by
  have hs : 2 * Δ * generatedS L ≤ generatedN L := by
    simpa only [generatedS, generatedN, quarterCeil,
      CurrentAdditive.DeterministicParameters.s,
      CurrentAdditive.DeterministicParameters.N] using
      CurrentAdditive.DeterministicParameters.coefficient_mul_s_le_N
        (2 * Δ) L (by omega)
  have hN : 1 ≤ generatedN L := by
    have h : 0 < generatedN L := by unfold generatedN; positivity
    omega
  have hcount : 4 * generatedS L * m ≤ generatedQ₂ L := by
    unfold generatedQ₂
    have h1 := Nat.mul_le_mul_left (2 * generatedS L) hdegree
    have h2 := Nat.mul_le_mul_left (2 * Δ * generatedS L) hn
    have h3 := Nat.mul_le_mul_right (generatedN L) hs
    have h4 : (generatedN L) ^ 2 ≤ (generatedN L) ^ 4 :=
      Nat.pow_le_pow_right hN (by decide)
    nlinarith
  have hq : generatedQ₂ L = 2 ^ (4 * L) := by
    simp only [generatedQ₂, generatedN]
    rw [← pow_mul]
    congr 1
    omega
  have hclog : Nat.clog 2 (4 * generatedS L * m) ≤ 4 * L :=
    (Nat.clog_le_iff_le_pow (by decide)).2 (by simpa only [hq] using hcount)
  unfold pow2Ceil
  rw [hq]
  exact Nat.pow_le_pow_right (by decide) hclog

theorem full_source_width (L n m Δ : ℕ)
    (hn : n ≤ 2 ^ L) (hdegree : 2 * m ≤ Δ * n)
    (hsΔ : 2 * Δ ≤ fullS L) :
    pow2Ceil (4 * fullS L * m) ≤ fullQ₂ L := by
  have hcount : 4 * fullS L * m ≤ fullQ₂ L := by
    unfold fullQ₂
    have h1 := Nat.mul_le_mul_left (2 * fullS L) hdegree
    have h2 := Nat.mul_le_mul_left (2 * Δ * fullS L) hn
    have h3 := Nat.mul_le_mul_right (2 ^ L * fullS L) hsΔ
    nlinarith
  have hq : fullQ₂ L = 2 ^ (L + 2 * (16 + ell L)) := by
    unfold fullQ₂ fullS
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  have hclog : Nat.clog 2 (4 * fullS L * m) ≤ L + 2 * (16 + ell L) :=
    (Nat.clog_le_iff_le_pow (by decide)).2 (by simpa only [hq] using hcount)
  unfold pow2Ceil
  rw [hq]
  exact Nat.pow_le_pow_right (by decide) hclog

theorem full_ell_ge_16 (L : ℕ) (hL : 2 ^ 15 ≤ L) : 16 ≤ ell L := by
  have hlt : 2 ^ 15 < L + 1 := by omega
  have hclog : 15 < Nat.clog 2 (L + 1) :=
    (Nat.lt_clog_iff_pow_lt (by decide)).2 hlt
  unfold ell
  omega

theorem full_source_width_from_cutoff (L n m Δ : ℕ)
    (hn : n ≤ 2 ^ L) (hdegree : 2 * m ≤ Δ * n)
    (hL : Δ ≤ L) :
    pow2Ceil (4 * fullS L * m) ≤ fullQ₂ L := by
  have hpow : L + 1 ≤ 2 ^ ell L := by
    unfold ell
    exact Nat.le_pow_clog (by decide) (L + 1)
  have hsΔ : 2 * Δ ≤ fullS L := by
    unfold fullS
    rw [pow_add]
    norm_num
    nlinarith
  exact full_source_width L n m Δ hn hdegree hsΔ

theorem generated_theta_ebar_budget (L : ℕ) (hL : 100 ≤ L) :
    128 * ebar (9 + generatedQlog L) 1 ≤ generatedW L := by
  have he : 7 + (90 + (9 + 6 * L + 63) / 64) ≤ 2 * L := by omega
  rw [ebar_unit]
  have hw : generatedW L = 2 ^ (2 * L) := by
    simp only [generatedW, generatedN]
    rw [← pow_mul]
    congr 1
    omega
  rw [hw]
  calc
    128 * (2 ^ 90 * 2 ^ ((9 + generatedQlog L + 63) / 64)) =
        2 ^ (7 + (90 + (9 + 6 * L + 63) / 64)) := by
      simp only [generatedQlog]
      rw [pow_add, pow_add]
      norm_num
    _ ≤ 2 ^ (2 * L) := Nat.pow_le_pow_right (by decide) he

theorem generated_theta_quarter_ebar_budget (L : ℕ) (hL : 100 ≤ L) :
    ebar (11 + generatedQlog L) 1 ≤ generatedS L * generatedQ₂ L := by
  have he : 90 + (11 + 6 * L + 63) / 64 ≤ 4 * L := by omega
  have hs : 1 ≤ generatedS L := by
    have h : 0 < generatedS L := by unfold generatedS; positivity
    omega
  have hq : generatedQ₂ L = 2 ^ (4 * L) := by
    simp only [generatedQ₂, generatedN]
    rw [← pow_mul]
    congr 1
    omega
  calc
    ebar (11 + generatedQlog L) 1 =
        2 ^ (90 + (11 + 6 * L + 63) / 64) := by
      rw [ebar_unit, ← pow_add]
      simp only [generatedQlog]
    _ ≤ 2 ^ (4 * L) := Nat.pow_le_pow_right (by decide) he
    _ ≤ generatedS L * generatedQ₂ L := by rw [hq]; nlinarith

theorem full_theta_ebar_budget (L : ℕ) (hell : 16 ≤ ell L) :
    128 * ebar (9 + fullQlog L) 1 ≤ fullW L := by
  have he : 7 + (90 + (9 + 16 * ell L + 63) / 64) ≤ 8 * ell L := by omega
  rw [ebar_unit]
  calc
    128 * (2 ^ 90 * 2 ^ ((9 + fullQlog L + 63) / 64)) =
        2 ^ (7 + (90 + (9 + 16 * ell L + 63) / 64)) := by
      simp only [fullQlog]
      rw [pow_add, pow_add]
      norm_num
    _ ≤ fullW L := by
      exact (Nat.pow_le_pow_right (by decide) he)

theorem full_theta_quarter_ebar_budget (L : ℕ)
    (hL : 100 ≤ L) (hell : 16 ≤ ell L) :
    ebar (11 + fullQlog L) 1 ≤ fullS L * fullQ₂ L := by
  have he : 90 + (11 + 16 * ell L + 63) / 64 ≤
      L + 48 + 3 * ell L := by omega
  have hproduct : fullS L * fullQ₂ L = 2 ^ (L + 48 + 3 * ell L) := by
    simp only [fullS, fullQ₂]
    rw [pow_add, pow_add, pow_add]
    ring
  calc
    ebar (11 + fullQlog L) 1 =
        2 ^ (90 + (11 + 16 * ell L + 63) / 64) := by
      rw [ebar_unit, ← pow_add]
      simp only [fullQlog]
    _ ≤ 2 ^ (L + 48 + 3 * ell L) := Nat.pow_le_pow_right (by decide) he
    _ = fullS L * fullQ₂ L := hproduct.symm

#print axioms ebar_unit
#print axioms ebar_half_eta_bound
#print axioms ebar_restoration_bound
#print axioms generated_owner_ebar_budget
#print axioms generated_Eexc_quarter
#print axioms generated_restoration_ebar_budget
#print axioms generated_extra_ebar_tests
#print axioms generated_source_width
#print axioms full_source_width
#print axioms full_ell_ge_16
#print axioms full_source_width_from_cutoff
#print axioms ebar_generated_x_formula
#print axioms generated_x_ebar_budget
#print axioms generated_theta_ebar_budget
#print axioms generated_theta_quarter_ebar_budget
#print axioms full_theta_ebar_budget
#print axioms full_theta_quarter_ebar_budget

end V38Cutoff
