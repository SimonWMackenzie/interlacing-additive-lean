import Paper2.SourceRationalSchedule
import Paper2.RestorationCoverParameters
import Paper2.LIdent

set_option maxRecDepth 16384
set_option maxHeartbeats 64000000

/-! Lane owner:a-small-1, R16 part 2: the value identities of the printed binary rationals against the
ADMITTED schedule definitions of lock v12 `eq:schedule` (C-parameters.tex:18-29):

* eta     = `SourceRationalScheduleScratch.eta (V := Fin n) (E := Fin m) L γ Δ`   (ℚ, admitted)
* delta_U = `SourceRationalScheduleScratch.deltaU (V := Fin n) (E := Fin m) L γ Δ` (ℚ, admitted)
* rho     = `SourceProfileParameters.rho L`                 (ℝ, admitted: (1/2)^L)
* x       = `SourceProfileParameters.x L`                   (ℝ, admitted: (1/2)^(10L))
* theta   = `RestorationCoverParameters.theta Q`            (ℝ, admitted: 1/(320 Q))

Each printed value is a pair (numerator, denominator) of naturals; the identities say that the quotient
is the admitted value.  With a = γ.num.toNat, b = γ.den (γ > 0), s = width L, w = restorationWidth L:

  eta     = a·(a·m) / (65536·s·max(max(a·(a·m), a·(2bΔ·n)), 6144b·(a·m)))
  delta_U = a·(a·m) / (65536·s·max(max(a·(a·m), a·(2bΔ·n)), 6144b·(a·m)) · (16·w))

(unreduced fractions; `min(1, am/(2bΔn), a/(6144b)) = a²m / max(a²m, 2abΔn, 6144abm)` since a·m > 0). -/

namespace SmallRatValues

open Paper2

theorem div_max2 (x y1 y2 : ℚ) (hx : 0 < x) (h1 : 0 < y1) (h2 : 0 < y2) :
    x / max y1 y2 = min (x / y1) (x / y2) := by
  rcases le_total y1 y2 with h | h
  · rw [max_eq_right h, min_eq_right (div_le_div_of_nonneg_left hx.le h1 h)]
  · rw [max_eq_left h, min_eq_left (div_le_div_of_nonneg_left hx.le h2 h)]

theorem div_max3 (x y1 y2 y3 : ℚ) (hx : 0 < x) (h1 : 0 < y1) (h2 : 0 < y2) (h3 : 0 < y3) :
    x / max (max y1 y2) y3 = min (min (x / y1) (x / y2)) (x / y3) := by
  rw [div_max2 x _ y3 hx (lt_max_of_lt_left h1) h3, div_max2 x y1 y2 hx h1 h2]

/-- The numerator of eta and delta_U. -/
def etaNum (γ : ℚ) (m : ℕ) : ℕ := γ.num.toNat * (γ.num.toNat * m)

/-- The denominator of eta (exactly the program's output-cell value, with its inputs substituted). -/
def etaDen (n m L Δ : ℕ) (γ : ℚ) : ℕ :=
  (65536 * SourceProfileParameters.width L) *
    (max (max (γ.num.toNat * (γ.num.toNat * m)) (γ.num.toNat * ((2 * γ.den * Δ) * n)))
      ((6144 * γ.den) * (γ.num.toNat * m)))

/-- The denominator of delta_U. -/
def deltaUDen (n m L Δ : ℕ) (γ : ℚ) : ℕ :=
  etaDen n m L Δ γ * (16 * ParameterizedCanonicalSource.restorationWidth L)

theorem eta_value (n m L Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ) (hn : 0 < n) (hm : 0 < m) :
    ((etaNum γ m : ℕ) : ℚ) / ((etaDen n m L Δ γ : ℕ) : ℚ) =
      SourceRationalScheduleScratch.eta (V := Fin n) (E := Fin m) L γ Δ := by
  have hnum : 0 < γ.num := Rat.num_pos.mpr hγ
  have haq : ((γ.num.toNat : ℕ) : ℚ) = (γ.num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg hnum.le
  have hγeq : γ = (γ.num : ℚ) / (γ.den : ℚ) := (Rat.num_div_den γ).symm
  have hA : (0 : ℚ) < (γ.num : ℚ) := by exact_mod_cast hnum
  have hB : (0 : ℚ) < (γ.den : ℚ) := by exact_mod_cast γ.den_pos
  have hmq : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
  have hnq : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  have hΔq : (0 : ℚ) < (Δ : ℚ) := by exact_mod_cast hΔ
  have hsq : (0 : ℚ) < (SourceProfileParameters.width L : ℚ) := by
    exact_mod_cast (show 0 < SourceProfileParameters.width L by
      unfold SourceProfileParameters.width; positivity)
  unfold etaNum etaDen SourceRationalScheduleScratch.eta SourceRationalScheduleScratch.vertexTolerance
    SourceRationalScheduleScratch.witnessDensity
  simp only [Fintype.card_fin]
  push_cast
  rw [haq, div_mul_eq_div_div_swap]
  apply congrArg (fun z : ℚ => z / (65536 * (SourceProfileParameters.width L : ℚ)))
  rw [div_max3 _ _ _ _ (by positivity) (by positivity) (by positivity) (by positivity)]
  have e1 : (γ.num : ℚ) * ((γ.num : ℚ) * m) / ((γ.num : ℚ) * ((γ.num : ℚ) * m)) = 1 :=
    div_self (by positivity)
  have e2 : (γ.num : ℚ) * ((γ.num : ℚ) * m) / ((γ.num : ℚ) * (2 * (γ.den : ℚ) * Δ * n)) =
      γ * m / (2 * Δ * n) := by
    conv_rhs => rw [hγeq]
    field_simp
  have e3 : (γ.num : ℚ) * ((γ.num : ℚ) * m) / (6144 * (γ.den : ℚ) * ((γ.num : ℚ) * m)) =
      1 / 256 * (γ / 24) := by
    conv_rhs => rw [hγeq]
    field_simp
    ring
  rw [e1, e2, e3]

theorem restorationWidth_eq (L : ℕ) :
    SourceRationalScheduleScratch.restorationWidth L = ParameterizedCanonicalSource.restorationWidth L := by
  rw [LProducer.w_eq]
  unfold SourceRationalScheduleScratch.restorationWidth
  rw [sq]

theorem deltaU_value (n m L Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ) (hn : 0 < n) (hm : 0 < m) :
    ((etaNum γ m : ℕ) : ℚ) / ((deltaUDen n m L Δ γ : ℕ) : ℚ) =
      SourceRationalScheduleScratch.deltaU (V := Fin n) (E := Fin m) L γ Δ := by
  unfold SourceRationalScheduleScratch.deltaU deltaUDen
  rw [← eta_value n m L Δ γ hγ hΔ hn hm, restorationWidth_eq]
  push_cast
  rw [div_mul_eq_div_div]

theorem rho_value (L : ℕ) :
    ((((1 : ℕ) : ℚ) / ((2 ^ L : ℕ) : ℚ) : ℚ) : ℝ) = SourceProfileParameters.rho L := by
  unfold SourceProfileParameters.rho
  push_cast
  rw [one_div_pow]

theorem x_value (L : ℕ) :
    ((((1 : ℕ) : ℚ) / ((2 ^ (10 * L) : ℕ) : ℚ) : ℚ) : ℝ) = SourceProfileParameters.x L := by
  unfold SourceProfileParameters.x
  push_cast
  rw [one_div_pow]

theorem theta_value (Q : ℕ) :
    ((((1 : ℕ) : ℚ) / ((320 * Q : ℕ) : ℚ) : ℚ) : ℝ) = RestorationCoverParameters.theta Q := by
  unfold RestorationCoverParameters.theta
  push_cast
  rfl

end SmallRatValues

#print axioms SmallRatValues.eta_value
#print axioms SmallRatValues.deltaU_value
#print axioms SmallRatValues.rho_value
#print axioms SmallRatValues.x_value
#print axioms SmallRatValues.theta_value
