import EthInapproximability.CurrentPaper.Foundations
import EthInapproximability.CurrentPaper.HardSeedArithmetic

/-!
# Small-column-density bounds for the current paper

Source: the v8 `D-hard-seed.tex`, `thm:foundation-hard-seed`, and
`C-classical-calculus.tex`, `app:foundation-density-iteration`.

The density iteration below consumes the checked corrected-version-2 theorem
`NPCC.iterated_density_amplification`. Unlike the older `NPCC.hard_seed`, this
argument starts from exactly two bounds at an arbitrary certified level; that
level need not equal the complexity of the ambient matrix. The row fraction
is arbitrary, not required to be dyadic.
-/

namespace EthInapproximability.CurrentPaper.HardSeed

open NPCC
open Workspace.Types.CommComplexity Workspace.Types.Interlace
open Workspace.Types.BoolMat Workspace.Types.Bracket
open Workspace.Types.MatComplexity Workspace.Types.Lambda
open Workspace.BracketLemmas

/-- The exact integer `9t/16`, when the power-of-two width is `t = 2^m`. -/
def copyCount (m : ℕ) : ℕ := 18 * 2 ^ (m - 5)

/-- The absolute power-of-two threshold stated in the proof. It is fixed
before any matrix, certified cost or density is supplied. -/
def threshold : ℕ := 2 ^ (2 ^ 20)

theorem threshold_is_power_of_two : ∃ m : ℕ, threshold = 2 ^ m := ⟨2 ^ 20, rfl⟩

theorem threshold_ge_32 : 32 ≤ threshold := by
  change 32 ≤ (2 : ℕ) ^ (2 ^ 20)
  calc
    32 = (2 : ℕ) ^ 5 := by norm_num
    _ ≤ (2 : ℕ) ^ (2 ^ 20) :=
      (pow_le_pow_iff_right₀ (by norm_num : (1 : ℕ) < 2)).mpr (by norm_num)

/-- The current paper's column-density function, with binary logarithm. -/
noncomputable def columnDensity (t : ℝ) : ℝ :=
  (2 : ℝ) ^ (-((2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt (Real.logb 2 t))))

theorem copyCount_eq {m : ℕ} (hm : 5 ≤ m) :
    copyCount m = (9 * 2 ^ m) / 16 := by
  have hp : (2 : ℕ) ^ m = 32 * 2 ^ (m - 5) := by
    calc
      (2 : ℕ) ^ m = 2 ^ ((m - 5) + 5) := by rw [Nat.sub_add_cancel hm]
      _ = 32 * 2 ^ (m - 5) := by rw [pow_add]; ring
  unfold copyCount
  rw [hp]
  omega

theorem copyCount_bounds {m : ℕ} (hm : 5 ≤ m) :
    1 ≤ copyCount m ∧ 2 ^ m ≤ 2 * copyCount m ∧ copyCount m ≤ 2 ^ m := by
  have hp : (2 : ℕ) ^ m = 32 * 2 ^ (m - 5) := by
    calc
      (2 : ℕ) ^ m = 2 ^ ((m - 5) + 5) := by rw [Nat.sub_add_cancel hm]
      _ = 32 * 2 ^ (m - 5) := by rw [pow_add]; ring
  have hpos : 0 < (2 : ℕ) ^ (m - 5) := by positivity
  unfold copyCount
  rw [hp]
  omega

theorem columnDensity_pow (m : ℕ) :
    columnDensity ((2 : ℝ) ^ m) =
      (2 : ℝ) ^ (-((2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt (m : ℝ)))) := by
  unfold columnDensity
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
  simp only [mul_one]

theorem columnDensity_pos (t : ℝ) : 0 < columnDensity t := by
  unfold columnDensity
  positivity

theorem columnDensity_le_one (t : ℝ) : columnDensity t ≤ 1 := by
  unfold columnDensity
  calc
    (2 : ℝ) ^ (-((2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt (Real.logb 2 t)))) ≤
        (2 : ℝ) ^ (0 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (neg_nonpos.mpr (by positivity))
    _ = 1 := by rw [Real.rpow_zero]

/-- Monotonicity of all three bundled costs. The scalar ingredient is the
actual restricted-matrix monotonicity theorem, not an abstract cost axiom. -/
theorem lambda_mono {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (f : X → Y → Bool)
    {p q : ℕ} {x z w : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q)
    (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hz0 : 0 < z) (hzw : z ≤ w) (hw1 : w ≤ 1) :
    LambdaGE f p x z ≤ LambdaGE f q x w := by
  classical
  let eX : Fin (Fintype.card X) ≃ X := (Fintype.equivFin X).symm
  let eY : Fin (Fintype.card Y) ≃ Y := (Fintype.equivFin Y).symm
  let M : BoolMat := ⟨Fintype.card X, Fintype.card Y, fun i j => f (eX i) (eY j)⟩
  have he : ∀ i j, M.e i j = f (eX i) (eY j) := fun _ _ => rfl
  have hX : 1 ≤ Fintype.card X := Fintype.card_pos
  rw [LambdaGE_eq_Lambda f M eX eY he hx0 hx1 hz0 (hzw.trans hw1) hX,
    LambdaGE_eq_Lambda f M eX eY he hx0 hx1 (hz0.trans_le hzw) hw1 hX]
  unfold Lambda
  refine min_le_min ?_ (min_le_min ?_ ?_)
  · exact monotonicity M p q x x z w hp hpq hx0 le_rfl hx1 hz0 hzw hw1
  · exact Nat.add_le_add_left (monotonicity M p q x x (z / 2) (w / 2)
      hp hpq hx0 le_rfl hx1 (by positivity) (by linarith) (by linarith)) 1
  · exact Nat.add_le_add_left (monotonicity M p q x x (z / 4) (w / 4)
      hp hpq hx0 le_rfl hx1 (by positivity) (by linarith) (by linarith)) 2

/-- The iterated grid always has at least one block. -/
theorem gridFloor_pos {ρ : ℝ} (hρ : 2 < ρ) (k s p : ℕ) (hp : 1 ≤ p) :
    1 ≤ gridFloor ρ k s p := by
  unfold gridFloor
  apply Nat.le_floor
  have hb : 1 ≤ (ρ - 1) / (ρ - 2) := by
    rw [le_div_iff₀ (by linarith : 0 < ρ - 2)]
    linarith
  have htwo : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hbeta : (1 : ℝ) ≤ ((ρ - 1) / (ρ - 2)) ^ s := one_le_pow₀ hb
  have hpr : (1 : ℝ) ≤ p := by exact_mod_cast hp
  exact_mod_cast one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le htwo hbeta) hpr

/-- The uniform column guard which makes the hard-seed threshold independent
of the input matrix and its density. -/
theorem square_le_half {γ : ℝ} (hγ : 0 < γ) (hγsqrt : γ ≤ 1 / Real.sqrt 2) :
    γ ≤ 1 ∧ γ ^ 2 ≤ 1 / 2 := by
  have hs : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hs2 : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs1 : 1 ≤ Real.sqrt (2 : ℝ) := by nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have hprod : γ * Real.sqrt 2 ≤ 1 := (le_div_iff₀ hs).mp hγsqrt
  have hprod0 : 0 ≤ γ * Real.sqrt 2 := by positivity
  have hprodsq := mul_self_le_mul_self hprod0 hprod
  have hγsq : γ ^ 2 ≤ 1 / 2 := by
    nlinarith [show (γ * Real.sqrt 2) * (γ * Real.sqrt 2) = γ ^ 2 * 2 by
      calc
        _ = γ ^ 2 * Real.sqrt 2 ^ 2 := by ring
        _ = _ := by rw [hs2]]
  exact ⟨by nlinarith, hγsq⟩

/-- The combinatorial part of the small-column-density theorem, with only
explicit scalar inequalities separated out. The exact current-paper numeric
schedule supplies those scalar inequalities in `hardSeed` below. -/
theorem hardSeed_of_numeric_gates {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (f : X → Y → Bool)
    {H m s : ℕ} {x γ ρ χ : ℝ}
    (hH : 2 ≤ H) (hm : 5 ≤ m) (hx : 0 < x)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (h1 : H ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x γ))
    (h2 : H - 1 ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (γ / 2)))
    (hrow : (2 : ℝ) ^ m * x ≤ 1)
    (hρ : 2 < ρ) (hs : s ≤ m - 5)
    (hside : (ρ - 1) ^ (m - 5) ≤ ρ ^ ((m - 5) - s))
    (hgrid : gridFloor ρ (m - 5) s 17 ≤ 18 * 2 ^ (m - 5))
    (hcol : (γ ^ 2) ^ (ρ ^ s) ≤ χ) (hχ1 : χ ≤ 1) :
    H + m ≤ LambdaGE f (18 * 2 ^ (m - 5)) ((2 : ℝ) ^ m * x) χ := by
  have hpow : (2 : ℝ) ^ (m - 5) * 32 = (2 : ℝ) ^ m := by
    calc
      (2 : ℝ) ^ (m - 5) * 32 = (2 : ℝ) ^ (m - 5) * (2 : ℝ) ^ 5 := by norm_num
      _ = (2 : ℝ) ^ ((m - 5) + 5) := (pow_add _ _ _).symm
      _ = (2 : ℝ) ^ m := by rw [Nat.sub_add_cancel hm]
  have hrows : (2 : ℝ) ^ (m - 5) * (32 * x) = (2 : ℝ) ^ m * x := by
    rw [← mul_assoc, hpow]
  have h32 : (32 : ℝ) * x ≤ 1 := by
    have hp : (1 : ℝ) ≤ (2 : ℝ) ^ (m - 5) := one_le_pow₀ (by norm_num)
    rw [← hrows] at hrow
    nlinarith
  have hseed : H + 5 ≤ LambdaGE f 17 (32 * x) (γ ^ 2) := by
    convert repeatedRowDoubling f hH hx hγ hγ1 h1 h2 5 (by norm_num)
      (by norm_num; exact h32)
      using 1
    norm_num
  have hnonconstant : 1 ≤ Dfamily (interlaceFun f 17)
      (bracketGE X Y 17 (32 * x) (γ ^ 2 / 4)) := by
    have hh := hseed.trans ((min_le_right _ _).trans (min_le_right _ _))
    omega
  have hxk : 32 * x ≤ (2 : ℝ) ^ (-((m - 5 : ℕ) : ℝ)) := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (m - 5) := by positivity
    rw [← one_div, le_div_iff₀ hpos]
    nlinarith [hrow, hrows]
  have hiteration := (iterated_density_amplification f hρ (m - 5) s 17 hs
    (by norm_num) (by positivity : 0 < 32 * x) hxk
    (by positivity : 0 < γ ^ 2) (by nlinarith : γ ^ 2 ≤ 1)
    hnonconstant hside).1
  have htrans := lambda_mono f (gridFloor_pos hρ _ _ 17 (by norm_num)) hgrid
    (by positivity : 0 < (2 : ℝ) ^ m * x) hrow
    (Real.rpow_pos_of_pos (by positivity : 0 < γ ^ 2) _) hcol hχ1
  rw [hrows] at hiteration
  have hsum : H + m ≤ (m - 5) + LambdaGE f 17 (32 * x) (γ ^ 2) := by omega
  exact hsum.trans (hiteration.trans htrans)

/-- The same matrix argument at an arbitrary real certified level. Rounding
up is valid because both communicated costs are integers; this introduces no
third input bound and does not substitute the matrix's exact complexity. -/
theorem hardSeedReal_of_numeric_gates {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (f : X → Y → Bool)
    {H : ℝ} {m s : ℕ} {x γ ρ χ : ℝ}
    (hH : 2 ≤ H) (hm : 5 ≤ m) (hx : 0 < x)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (h1 : H ≤ (Dfamily (interlaceFun f 1) (bracketGE X Y 1 x γ) : ℝ))
    (h2 : H - 1 ≤ (Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (γ / 2)) : ℝ))
    (hrow : (2 : ℝ) ^ m * x ≤ 1)
    (hρ : 2 < ρ) (hs : s ≤ m - 5)
    (hside : (ρ - 1) ^ (m - 5) ≤ ρ ^ ((m - 5) - s))
    (hgrid : gridFloor ρ (m - 5) s 17 ≤ 18 * 2 ^ (m - 5))
    (hcol : (γ ^ 2) ^ (ρ ^ s) ≤ χ) (hχ1 : χ ≤ 1) :
    H + m ≤ (LambdaGE f (18 * 2 ^ (m - 5)) ((2 : ℝ) ^ m * x) χ : ℝ) := by
  have hceil : 2 ≤ ⌈H⌉₊ := by
    have hh := Nat.le_ceil H
    exact_mod_cast (show (2 : ℝ) ≤ (⌈H⌉₊ : ℝ) by linarith)
  have htop : ⌈H⌉₊ ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x γ) :=
    Nat.ceil_le.mpr h1
  have hhalf : ⌈H⌉₊ - 1 ≤ Dfamily (interlaceFun f 1)
      (bracketGE X Y 1 x (γ / 2)) := by
    have hh : ⌈H⌉₊ ≤ Dfamily (interlaceFun f 1)
        (bracketGE X Y 1 x (γ / 2)) + 1 := Nat.ceil_le.mpr (by push_cast; linarith)
    omega
  have hh := hardSeed_of_numeric_gates f hceil hm hx hγ hγ1 htop hhalf
    hrow hρ hs hside hgrid hcol hχ1
  have hhR := (Nat.cast_le (α := ℝ)).mpr hh
  push_cast at hhR
  linarith [Nat.le_ceil H]

/-- `thm:foundation-hard-seed`, at arbitrary natural certified level `H`,
with the exact exponent threshold printed in the current manuscript.
The width is `t = 2^m`, so the bound `H+m` is exactly `H+log₂ t`. -/
theorem hardSeed {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (f : X → Y → Bool)
    {H m : ℕ} {x γ : ℝ}
    (hH : 2 ≤ H) (hm : 2 ^ 20 ≤ m) (hx : 0 < x)
    (hγ : 0 < γ) (hγsqrt : γ ≤ 1 / Real.sqrt 2)
    (h1 : H ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x γ))
    (h2 : H - 1 ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (γ / 2)))
    (hrow : (2 : ℝ) ^ m * x ≤ 1) :
    H + m ≤ LambdaGE f (copyCount m) ((2 : ℝ) ^ m * x)
      (columnDensity ((2 : ℝ) ^ m)) := by
  obtain ⟨hm5, hρ, hs, hside, hgrid, hcol⟩ := HardSeedArithmetic.numeric_gates hm
  obtain ⟨hγ1, hγhalf⟩ := square_le_half hγ hγsqrt
  apply hardSeed_of_numeric_gates f hH hm5 hx hγ hγ1 h1 h2 hrow hρ hs hside hgrid
  · rw [columnDensity_pow]
    exact (Real.rpow_le_rpow (by positivity : 0 ≤ γ ^ 2) hγhalf
      (by positivity : 0 ≤ Real.sqrt (m : ℝ) ^ HardSeedArithmetic.depth m)).trans hcol
  · exact columnDensity_le_one _

/-- The scalar top-rung form used by the certified stopping argument. -/
theorem hardSeed_cost {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (f : X → Y → Bool)
    {H m : ℕ} {x γ : ℝ}
    (hH : 2 ≤ H) (hm : 2 ^ 20 ≤ m) (hx : 0 < x)
    (hγ : 0 < γ) (hγsqrt : γ ≤ 1 / Real.sqrt 2)
    (h1 : H ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x γ))
    (h2 : H - 1 ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (γ / 2)))
    (hrow : (2 : ℝ) ^ m * x ≤ 1) :
    H + m ≤ Dfamily (interlaceFun f (copyCount m))
      (bracketGE X Y (copyCount m) ((2 : ℝ) ^ m * x)
        (columnDensity ((2 : ℝ) ^ m))) :=
  (hardSeed f hH hm hx hγ hγsqrt h1 h2 hrow).trans (min_le_left _ _)

/-- Full real-certified-level statement of `thm:foundation-hard-seed`.
There is no assumption that `H` is an attained or exact protocol depth. -/
theorem hardSeedReal {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (f : X → Y → Bool)
    {H : ℝ} {m : ℕ} {x γ : ℝ}
    (hH : 2 ≤ H) (hm : 2 ^ 20 ≤ m) (hx : 0 < x)
    (hγ : 0 < γ) (hγsqrt : γ ≤ 1 / Real.sqrt 2)
    (h1 : H ≤ (Dfamily (interlaceFun f 1) (bracketGE X Y 1 x γ) : ℝ))
    (h2 : H - 1 ≤ (Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (γ / 2)) : ℝ))
    (hrow : (2 : ℝ) ^ m * x ≤ 1) :
    H + m ≤ (LambdaGE f (copyCount m) ((2 : ℝ) ^ m * x)
      (columnDensity ((2 : ℝ) ^ m)) : ℝ) := by
  obtain ⟨hm5, hρ, hs, hside, hgrid, hcol⟩ := HardSeedArithmetic.numeric_gates hm
  obtain ⟨hγ1, hγhalf⟩ := square_le_half hγ hγsqrt
  apply hardSeedReal_of_numeric_gates f hH hm5 hx hγ hγ1 h1 h2 hrow hρ hs hside hgrid
  · rw [columnDensity_pow]
    exact (Real.rpow_le_rpow (by positivity : 0 ≤ γ ^ 2) hγhalf
      (by positivity : 0 ≤ Real.sqrt (m : ℝ) ^ HardSeedArithmetic.depth m)).trans hcol
  · exact columnDensity_le_one _

/-- Literal width form of `thm:foundation-hard-seed`, including binary
logarithm, exact integer `9t/16`, and the matrix-independent absolute cutoff. -/
theorem hardSeed_width {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (f : X → Y → Bool)
    {H x γ : ℝ} {t : ℕ}
    (ht : ∃ m : ℕ, t = 2 ^ m) (hthreshold : threshold ≤ t)
    (hH : 2 ≤ H) (hx : 0 < x)
    (hγ : 0 < γ) (hγsqrt : γ ≤ 1 / Real.sqrt 2)
    (h1 : H ≤ (Dfamily (interlaceFun f 1) (bracketGE X Y 1 x γ) : ℝ))
    (h2 : H - 1 ≤ (Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (γ / 2)) : ℝ))
    (hrow : (t : ℝ) * x ≤ 1) :
    H + Real.logb 2 (t : ℝ) ≤
      (LambdaGE f ((9 * t) / 16) ((t : ℝ) * x) (columnDensity (t : ℝ)) : ℝ) := by
  obtain ⟨m, rfl⟩ := ht
  have hm : 2 ^ 20 ≤ m :=
    (pow_le_pow_iff_right₀ (by norm_num : (1 : ℕ) < 2)).mp hthreshold
  have hm5 : 5 ≤ m := by omega
  rw [← copyCount_eq hm5]
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hrow ⊢
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]
  exact hardSeedReal f hH hm hx hγ hγsqrt h1 h2 hrow

end EthInapproximability.CurrentPaper.HardSeed
