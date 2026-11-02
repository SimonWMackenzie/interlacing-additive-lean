import Paper2.SourceSmallnessSchedule

/-!
Frozen v12 Appendix C, eq:schedule and the four eta-sensitive checks in
eq:admissibility. This module proves the four displayed guards; complete machine costs remain separate.
-/

namespace Paper2.AllowanceSmallnessScratch

open SourceProfileParameters SourceDensityScheduleScratch
  SourceRationalScheduleScratch
open RestorationWidthScheduleScratch (depth)

set_option maxRecDepth 1000
set_option maxHeartbeats 1000000

variable {V E : Type*} [Fintype V] [Nonempty V] [Fintype E]

def allowanceExponent (Δ : ℕ) (γ : ℚ) : ℕ :=
  Nat.clog 2 (max 1 (Nat.ceil ((32 : ℚ) / etaConstant Δ γ)))

def cutoff (Δ : ℕ) (γ : ℚ) : ℕ :=
  max SourceSmallnessSchedule.cutoff
    (LogSquareCutoff.cutoff 2 6 (64 + allowanceExponent Δ γ))

private theorem allowance_power (Δ : ℕ) (γ : ℚ)
    (hΔ : 0 < Δ) (hγ : 0 < γ) :
    (32 : ℚ) ≤ etaConstant Δ γ * 2 ^ allowanceExponent Δ γ := by
  have hc := etaConstant_pos Δ γ hΔ hγ
  have hceil : (32 : ℚ) / etaConstant Δ γ ≤
      Nat.ceil ((32 : ℚ) / etaConstant Δ γ) := Nat.le_ceil _
  have hp : Nat.ceil ((32 : ℚ) / etaConstant Δ γ) ≤
      2 ^ allowanceExponent Δ γ :=
    (le_max_right 1 _).trans (Nat.le_pow_clog (by decide) _)
  have hpq : (Nat.ceil ((32 : ℚ) / etaConstant Δ γ) : ℚ) ≤
      (2 ^ allowanceExponent Δ γ : ℕ) := by exact_mod_cast hp
  have h := hceil.trans hpq
  calc
    (32 : ℚ) ≤ (2 ^ allowanceExponent Δ γ : ℕ) * etaConstant Δ γ :=
      (div_le_iff₀ hc).mp h
    _ = etaConstant Δ γ * 2 ^ allowanceExponent Δ γ := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using
        (mul_comm (2 ^ allowanceExponent Δ γ : ℚ) (etaConstant Δ γ))

private theorem exponent_budget (L Δ : ℕ) (γ : ℚ)
    (hL : cutoff Δ γ ≤ L) :
    2 * depth L + 3 * exponent L + allowanceExponent Δ γ ≤ L := by
  have h := LogSquareCutoff.quadratic_log_le 2 6
    (64 + allowanceExponent Δ γ) L (le_trans (le_max_right _ _) hL)
  have ha := SourceOverheadBounds.source_exponent_le L
  dsimp [depth] at *
  omega

private theorem dyadic_small (a b d : ℕ) (h : a + d ≤ b) :
    (2 : ℝ) ^ a * (1 / 2 : ℝ) ^ b ≤ 1 / (2 : ℝ) ^ d := by
  have hp : (2 : ℝ) ^ (a + d) ≤ (2 : ℝ) ^ b :=
    pow_le_pow_right₀ (by norm_num) h
  rw [pow_add] at hp
  rw [one_div, inv_pow, ← div_eq_mul_inv]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  simpa only [one_mul] using hp

private theorem graph_eta_lower (edge : E → Bool → V) (L Δ : ℕ) (γ : ℚ)
    (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ) :
    (etaConstant Δ γ : ℝ) ≤
      (SourceRationalScheduleScratch.eta (V := V) (E := E) L γ Δ : ℝ) *
        (SourceProfileParameters.width L : ℝ) := by
  have h := (eta_bounds edge L Δ γ hγ hΔ hincident hdegree).1
  have hr : (etaConstant Δ γ : ℝ) / (SourceProfileParameters.width L : ℝ) ≤
      (SourceRationalScheduleScratch.eta (V := V) (E := E) L γ Δ : ℝ) := by
    exact_mod_cast h
  have hs : (0 : ℝ) < SourceProfileParameters.width L := by
    exact_mod_cast (show 0 < SourceProfileParameters.width L by unfold SourceProfileParameters.width; positivity)
  exact (div_le_iff₀ hs).mp hr

private theorem dyadic_le_coefficient (a b Δ : ℕ) (γ : ℚ)
    (hΔ : 0 < Δ) (hγ : 0 < γ)
    (h : a + allowanceExponent Δ γ ≤ b) :
    (2 : ℝ) ^ a * (1 / 2 : ℝ) ^ b ≤
      (etaConstant Δ γ : ℝ) / 32 := by
  have hp := dyadic_small a b (allowanceExponent Δ γ) h
  have hcq := allowance_power Δ γ hΔ hγ
  have hc : (32 : ℝ) ≤
      (etaConstant Δ γ : ℝ) * (2 : ℝ) ^ allowanceExponent Δ γ := by
    exact_mod_cast hcq
  exact hp.trans ((div_le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ allowanceExponent Δ γ)
    (by norm_num : (0 : ℝ) < 32)).2 (by simpa using hc))

private theorem eta_div_bound (edge : E → Bool → V) (L Δ : ℕ) (γ : ℚ)
    (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (t : ℝ) (ht : t * (SourceProfileParameters.width L : ℝ) ≤ (etaConstant Δ γ : ℝ) / 32) :
    t ≤ (SourceRationalScheduleScratch.eta (V := V) (E := E) L γ Δ : ℝ) / 32 := by
  have hs : (0 : ℝ) < SourceProfileParameters.width L := by
    exact_mod_cast (show 0 < SourceProfileParameters.width L by unfold SourceProfileParameters.width; positivity)
  have hc := graph_eta_lower edge L Δ γ hγ hΔ hincident hdegree
  have hts : t * (SourceProfileParameters.width L : ℝ) ≤
      ((SourceRationalScheduleScratch.eta (V := V) (E := E) L γ Δ : ℝ) / 32) *
        (SourceProfileParameters.width L : ℝ) := by nlinarith
  exact (mul_le_mul_iff_of_pos_right hs).mp hts

private theorem first_product (L Δ : ℕ) (γ : ℚ)
    (hΔ : 0 < Δ) (hγ : 0 < γ) (hL : cutoff Δ γ ≤ L) :
    ((RestorationWidthScheduleScratch.width L : ℝ) ^ 2 * x L) *
      (SourceProfileParameters.width L : ℝ) ≤ (etaConstant Δ γ : ℝ) / 32 := by
  have he := exponent_budget L Δ γ hL
  have h := dyadic_le_coefficient (2 * depth L + exponent L) (10 * L)
    Δ γ hΔ hγ (by omega)
  simp only [RestorationWidthScheduleScratch.width, SourceProfileParameters.width,
    x, Nat.cast_pow, Nat.cast_ofNat]
  change (((2 : ℝ) ^ depth L) ^ 2 * (1 / 2 : ℝ) ^ (10 * L)) *
    (2 : ℝ) ^ exponent L ≤ _
  rw [← pow_mul, show depth L * 2 = 2 * depth L by omega]
  calc
    _ = (2 : ℝ) ^ (2 * depth L + exponent L) *
        (1 / 2 : ℝ) ^ (10 * L) := by rw [pow_add]; ring
    _ ≤ _ := h

private theorem second_product (L Δ : ℕ) (γ : ℚ)
    (hΔ : 0 < Δ) (hγ : 0 < γ) (hL : cutoff Δ γ ≤ L) :
    (((RestorationWidthScheduleScratch.width L : ℝ) * outerWidth L * x L) *
      (SourceProfileParameters.width L : ℝ)) ≤ (etaConstant Δ γ : ℝ) / 32 := by
  have he := exponent_budget L Δ γ hL
  have h := dyadic_le_coefficient
    (depth L + outerExponent L + exponent L) (10 * L)
    Δ γ hΔ hγ (by unfold outerExponent; omega)
  simp only [RestorationWidthScheduleScratch.width, SourceProfileParameters.width,
    outerWidth, x, Nat.cast_pow, Nat.cast_ofNat]
  change (((2 : ℝ) ^ depth L * (2 : ℝ) ^ outerExponent L *
    (1 / 2 : ℝ) ^ (10 * L)) * (2 : ℝ) ^ exponent L) ≤ _
  calc
    _ = (2 : ℝ) ^ (depth L + outerExponent L + exponent L) *
        (1 / 2 : ℝ) ^ (10 * L) := by rw [pow_add, pow_add]; ring
    _ ≤ _ := h

private theorem third_product (L Δ : ℕ) (γ : ℚ)
    (hΔ : 0 < Δ) (hγ : 0 < γ) (hL : cutoff Δ γ ≤ L) :
    ((RestorationWidthScheduleScratch.width L : ℝ) / outerWidth L) *
      (SourceProfileParameters.width L : ℝ) ≤ (etaConstant Δ γ : ℝ) / 32 := by
  have he := exponent_budget L Δ γ hL
  have h := dyadic_le_coefficient (depth L + exponent L) (outerExponent L)
    Δ γ hΔ hγ (by unfold outerExponent; omega)
  simp only [RestorationWidthScheduleScratch.width, SourceProfileParameters.width,
    outerWidth, Nat.cast_pow, Nat.cast_ofNat]
  change ((2 : ℝ) ^ depth L / (2 : ℝ) ^ outerExponent L) *
    (2 : ℝ) ^ exponent L ≤ _
  calc
    _ = (2 : ℝ) ^ (depth L + exponent L) *
        (1 / 2 : ℝ) ^ outerExponent L := by
      rw [pow_add, div_eq_mul_inv, ← inv_pow,
        show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
      ring
    _ ≤ _ := h

/-- The four eta-sensitive Appendix C checks, with exact source schedules and
one graph-only cutoff. Constants are the frozen literal g=127/128, mu=1/256. -/
theorem allowance_checks (edge : E → Bool → V) (L Δ : ℕ) (γ : ℚ)
    (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hL : cutoff Δ γ ≤ L) :
    let q₂ := outerWidth L
    let w := RestorationWidthScheduleScratch.width L
    let η := (SourceRationalScheduleScratch.eta (V := V) (E := E) L γ Δ : ℝ)
    2 * (w : ℝ) * x L + η / (16 * (127 / 128 : ℝ)) < 1 ∧
    2 * (w : ℝ) ^ 2 * x L ≤ η / (16 * (127 / 128 : ℝ)) ∧
    4 * (1 / 256 : ℝ) * w * q₂ * x L ≤ η / 32 ∧
    4 * (1 / 256 : ℝ) * w / q₂ ≤ η / 32 := by
  dsimp only
  have hfirst := eta_div_bound edge L Δ γ hγ hΔ hincident hdegree _
    (first_product L Δ γ hΔ hγ hL)
  have hsecond := eta_div_bound edge L Δ γ hγ hΔ hincident hdegree _
    (second_product L Δ γ hΔ hγ hL)
  have hthird := eta_div_bound edge L Δ γ hγ hΔ hincident hdegree _
    (third_product L Δ γ hΔ hγ hL)
  have hηlo : (0 : ℝ) ≤
      (SourceRationalScheduleScratch.eta (V := V) (E := E) L γ Δ : ℝ) := by
    have he := SourceRationalScheduleScratch.eta_pos (V := V) (E := E)
      L γ Δ hγ hΔ (edges_pos edge hincident)
    exact_mod_cast he.le
  have hηhi : (SourceRationalScheduleScratch.eta (V := V) (E := E)
      L γ Δ : ℝ) ≤ 1 / 65536 := by
    have hh := SourceRationalScheduleScratch.eta_le_inverse_65536
      (V := V) (E := E) L γ Δ
    have hhR : ((SourceRationalScheduleScratch.eta (V := V) (E := E)
        L γ Δ : ℚ) : ℝ) ≤ ((1 / 65536 : ℚ) : ℝ) := by exact_mod_cast hh
    norm_num at hhR ⊢
    exact hhR
  have hw := SourceSmallnessSchedule.restoration_small L
    (le_trans (le_max_left _ _) hL)
  constructor
  · norm_num only at ⊢
    nlinarith only [hw, hηhi]
  constructor
  · norm_num only at ⊢
    nlinarith only [hfirst, hηlo]
  constructor
  · norm_num only at ⊢
    nlinarith only [hsecond, hηlo]
  · norm_num only at ⊢
    have hfac : (1 / 64 : ℝ) *
        (RestorationWidthScheduleScratch.width L : ℝ) / outerWidth L =
        (1 / 64 : ℝ) * ((RestorationWidthScheduleScratch.width L : ℝ) /
          outerWidth L) := by ring
    rw [hfac]
    nlinarith only [hthird, hηlo]

end Paper2.AllowanceSmallnessScratch


