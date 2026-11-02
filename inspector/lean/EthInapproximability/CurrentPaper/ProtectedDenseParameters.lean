import EthInapproximability.CurrentPaper.ProtectedSourceSchedule

/-!
# Explicit scalar gates for the protected dense restriction

Source: frozen v8 `A-stage4-details.tex`, the defect calculation in the proof
of `lem:paper-protected-preparation`, and `F-parameter-choices.tex`, the
literal parameter schedule and `eq:paper-tail-graph`.

The balance width, graph-coordinate room, strict diagonal deletion margin,
and joint-density bound are consequences of the actual schedule and the
public source-constant bound. None is an additional acceptance test or a
communication lower-bound assumption.
-/

namespace EthInapproximability.CurrentPaper.ProtectedDenseParameters

open Construction ProtectedSourceSchedule

/-- The actual balance order covers every set of `8*q₁` selected coordinates. -/
theorem balance_order_gate (i : Parameters.Input) :
    8 * qOne (Parameters.firstExponent i) ≤ Parameters.balanceOrder i := by
  have h := ParameterGates.balanceOrder_ge_two_stoppingBudget i
  unfold ParameterGates.stoppingBudget at h
  change 8 * Parameters.firstWidth i ≤ Parameters.balanceOrder i
  omega

/-- The accepted graph width and source constant supply the source-witness
room. All divisions are exact rational divisions in this intermediate form. -/
theorem graph_room_rat (i : Parameters.Input) (ha : Parameters.Accepted i)
    {Δ : ℕ} (hΔ : 1 ≤ Δ) {γ : ℚ} (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hsource : 2 ^ 44 * (Δ : ℚ) / γ ≤ i.sourceConstant) :
    64 * (Parameters.bins i : ℚ) * qOne (Parameters.firstExponent i) ≤
      (γ / 24) * Parameters.secondWidth i := by
  have hc : (0 : ℚ) < i.sourceConstant := lt_of_lt_of_le (by positivity) hsource
  have htol := ParameterGates.source_tolerances i Δ γ (γ / (4 * (Δ : ℚ)))
    hΔ hγ hγone hsource (le_refl _)
  have hroom : (64 : ℚ) * i.sourceConstant * Parameters.bins i *
      Parameters.firstWidth i ≤ Parameters.secondWidth i := by
    exact_mod_cast ParameterGates.accepted_graph_item_room i ha
  have hdiv : (64 : ℚ) * Parameters.bins i * Parameters.firstWidth i ≤
      (i.sourceConstant : ℚ)⁻¹ * Parameters.secondWidth i := by
    rw [inv_mul_eq_div]
    apply (le_div_iff₀ hc).mpr
    nlinarith [hroom]
  exact hdiv.trans (mul_le_mul_of_nonneg_right htol.1 (Nat.cast_nonneg _))

/-- Real-valued form used by the actual aggregate defect count. -/
theorem graph_room (i : Parameters.Input) (ha : Parameters.Accepted i)
    {Δ : ℕ} (hΔ : 1 ≤ Δ) {γ : ℚ} (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hsource : 2 ^ 44 * (Δ : ℚ) / γ ≤ i.sourceConstant) :
    64 * (Parameters.bins i : ℝ) * qOne (Parameters.firstExponent i) ≤
      ((γ : ℝ) / 24) * Parameters.secondWidth i := by
  exact_mod_cast graph_room_rat i ha hΔ hγ hγone hsource

/-- The factor-two slack in the source tolerance gives the strictly smaller
diagonal-loss bound required when summing over all bins. -/
theorem row_tolerance_strict_rat (i : Parameters.Input)
    {Δ : ℕ} (hΔ : 1 ≤ Δ) {γ : ℚ} (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hsource : 2 ^ 44 * (Δ : ℚ) / γ ≤ i.sourceConstant) :
    Parameters.rowTolerance i < (1 / 184 : ℚ) * (γ / 24) /
      (32 * (Parameters.bins i : ℚ)) := by
  have htol := ParameterGates.source_tolerances i Δ γ (γ / (4 * (Δ : ℚ)))
    hΔ hγ hγone hsource (le_refl _)
  have hrow := (le_min_iff.mp (le_min_iff.mp htol.2.2).2).1
  have hs : (0 : ℚ) < Parameters.bins i := by exact_mod_cast Parameters.bins_pos i
  exact hrow.trans_lt (div_lt_div_of_pos_left (by positivity) (by positivity)
    (by nlinarith : (32 : ℚ) * Parameters.bins i < 64 * Parameters.bins i))

/-- Real-valued strict deletion margin for the physical diagonal group. -/
theorem row_tolerance_strict (i : Parameters.Input)
    {Δ : ℕ} (hΔ : 1 ≤ Δ) {γ : ℚ} (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hsource : 2 ^ 44 * (Δ : ℚ) / γ ≤ i.sourceConstant) :
    (Parameters.rowTolerance i : ℝ) < (1 / 184 : ℝ) * ((γ : ℝ) / 24) /
      (32 * (Parameters.bins i : ℝ)) := by
  have h := (Rat.cast_lt (K := ℝ)).mpr
    (row_tolerance_strict_rat i hΔ hγ hγone hsource)
  norm_num only [Rat.cast_mul, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one] at h
  exact h

/-- The actual balance error preserves joint density at least `98/100`
from the proved dominant-label fraction `998/1000`. -/
theorem dominant_density_gate (i : Parameters.Input) :
    (98 / 100 : ℝ) ≤ (998 / 1000 : ℝ) /
      (1 + 1 / (100 * (Parameters.balanceOrder i : ℝ))) := by
  have ht : (1 : ℝ) ≤ Parameters.balanceOrder i := by
    exact_mod_cast Parameters.balanceOrder_pos i
  have hε : (1 : ℝ) / (100 * Parameters.balanceOrder i) ≤ 1 / 100 :=
    one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  apply (le_div_iff₀ (by positivity : (0 : ℝ) <
    1 + 1 / (100 * (Parameters.balanceOrder i : ℝ)))).mpr
  nlinarith

/-- The positive threshold lets the natural subtraction in the source-item
count become the real subtraction used by the analytic defect estimate. -/
theorem threshold_defect_gate {X : Type*} [Fintype X] [Nonempty X]
    (i : Parameters.Input) (ha : Parameters.Accepted i) :
    (sourceThreshold X i : ℝ) - 1 < (Fintype.card X : ℝ) / 8 := by
  have ht := threshold_gates (X := X) i ha
  have h := ht.2.2
  rw [Nat.cast_sub (by omega : 1 ≤ sourceThreshold X i), Nat.cast_one] at h
  exact h

end EthInapproximability.CurrentPaper.ProtectedDenseParameters
