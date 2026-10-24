import Paper2.DefectInductionRational
import Paper2.DefectArithmetic

/-!
Recovered fixed-4/3 `cl:defect-induction` for the exact v38/v39 source.  The fixed correction is
`(4/3) log 2` in EthBridge's natural-log convention.
-/

namespace Paper2.V38DefectInduction

open Workspace.Types.CommComplexity Workspace.Types.Interlace
open EthBridge

variable {X Y : Type*} [Fintype X] [Fintype Y]

noncomputable def extra : ℝ := (4 / 3) * Real.log 2

private theorem extra_nonneg : 0 ≤ extra := by
  unfold extra
  positivity

noncomputable def oneState (p a : ℕ) (θ lam : ℝ) :
    Set (Finset (Fin p × X) × Finset (Fin p → Y)) :=
  { RC | NPCC.IsEquipartitionedGE RC.1 Finset.univ
      (EthBridge.rowThreshold (Fintype.card X) θ a) ∧
      ((Fintype.card Y : ℝ) ^ p) *
        Real.exp (-(EthBridge.cExcess a p * lam + extra)) ≤ (RC.2.card : ℝ) }

private theorem const_alice_selection (a p p₀ p₁ : ℕ)
    (L₀ L₁ lam : ℝ) (ha : 1 ≤ a) (hp : 2 ^ a < 2 * p)
    (hsum : p₀ + p₁ = p) (hlam : 0 < lam)
    (hL₀ : 0 ≤ L₀) (hL₁ : 0 ≤ L₁)
    (hadd : L₀ + L₁ ≤ EthBridge.cExcess a p * lam + extra) :
    (2 ^ (a - 1) < 2 * p₀ ∧
      L₀ ≤ EthBridge.cExcess (a - 1) p₀ * lam + extra) ∨
    (2 ^ (a - 1) < 2 * p₁ ∧
      L₁ ≤ EthBridge.cExcess (a - 1) p₁ * lam + extra) := by
  have hI : ∀ q : ℕ,
      EthBridge.cExcess (a - 1) q = (q : ℝ) - (2 : ℝ) ^ ((a : ℤ) - 2) := by
    intro q
    unfold EthBridge.cExcess
    rw [show ((a - 1 : ℕ) : ℤ) - 1 = (a : ℤ) - 2 by omega]
  have hA : EthBridge.cExcess a p =
      (p : ℝ) - 2 * (2 : ℝ) ^ ((a : ℤ) - 2) := by
    unfold EthBridge.cExcess
    rw [show (a : ℤ) - 1 = 1 + ((a : ℤ) - 2) by ring,
      zpow_one_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  have hpow_real : (2 : ℝ) ^ (a - 1) =
      2 * (2 : ℝ) ^ ((a : ℤ) - 2) := by
    rw [← zpow_natCast (2 : ℝ) (a - 1),
      show ((a - 1 : ℕ) : ℤ) = (a : ℤ) - 1 by omega,
      show (a : ℤ) - 1 = 1 + ((a : ℤ) - 2) by ring,
      zpow_one_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  have hbridge : ∀ q : ℕ,
      (2 ^ (a - 1) < 2 * q) ↔ ((2 : ℝ) ^ ((a : ℤ) - 2) < (q : ℝ)) := by
    intro q
    rw [← @Nat.cast_lt ℝ]
    push_cast
    rw [hpow_real]
    constructor <;> intro h <;> linarith
  have hsumR : (p₀ : ℝ) + (p₁ : ℝ) = (p : ℝ) := by
    exact_mod_cast hsum
  have hexp : ((p : ℝ) - 2 * (2 : ℝ) ^ ((a : ℤ) - 2)) * lam =
      ((p₀ : ℝ) - (2 : ℝ) ^ ((a : ℤ) - 2)) * lam +
      ((p₁ : ℝ) - (2 : ℝ) ^ ((a : ℤ) - 2)) * lam := by
    rw [show (p : ℝ) = (p₀ : ℝ) + (p₁ : ℝ) from hsumR.symm]
    ring
  rw [hA, hexp] at hadd
  by_contra hcon
  push Not at hcon
  obtain ⟨hc0, hc1⟩ := hcon
  by_cases he0 : 2 ^ (a - 1) < 2 * p₀ <;>
    by_cases he1 : 2 ^ (a - 1) < 2 * p₁
  · have hb0 := hc0 he0
    have hb1 := hc1 he1
    rw [hI p₀] at hb0
    rw [hI p₁] at hb1
    have he : 0 ≤ extra := extra_nonneg
    linarith
  · have hb0 := hc0 he0
    rw [hI p₀] at hb0
    have hp1le : (p₁ : ℝ) ≤ (2 : ℝ) ^ ((a : ℤ) - 2) :=
      not_lt.mp (fun h => he1 ((hbridge p₁).mpr h))
    have hnp1 : ((p₁ : ℝ) - (2 : ℝ) ^ ((a : ℤ) - 2)) * lam ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hlam.le
    linarith
  · have hb1 := hc1 he1
    rw [hI p₁] at hb1
    have hp0le : (p₀ : ℝ) ≤ (2 : ℝ) ^ ((a : ℤ) - 2) :=
      not_lt.mp (fun h => he0 ((hbridge p₀).mpr h))
    have hnp0 : ((p₀ : ℝ) - (2 : ℝ) ^ ((a : ℤ) - 2)) * lam ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hlam.le
    linarith
  · have hpow_nat : (2 : ℕ) ^ a = 2 * 2 ^ (a - 1) := by
      conv_lhs => rw [show a = (a - 1) + 1 by omega]
      rw [pow_succ']
    omega

private theorem ceil_half_ratio (p : ℕ) (hp : 6 ≤ p) :
    7 * Paper2.DefectArithmetic.ceilHalf p ≤ 4 * p := by
  have h := Paper2.DefectArithmetic.ceilHalf_bounds p
  rcases h with ⟨hlo, hhi, _⟩
  by_cases hp6 : p = 6
  · subst p
    decide
  · omega

private theorem const_bob_budget (a p : ℕ) (lam : ℝ)
    (ha : 3 ≤ a) (hp : 6 ≤ p) (hlam : 0 ≤ lam)
    (helig : 2 ^ (a - 1) < p) :
    (((p + 1) / 2 : ℕ) : ℝ) / (p : ℝ) *
      (EthBridge.cExcess a p * lam + extra + Real.log 2) ≤
      EthBridge.cExcess (a - 1) ((p + 1) / 2) * lam + extra := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hc : ((a : ℤ) - 1) = ((a - 1 : ℕ) : ℤ) := by omega
  have hpz : (2 : ℝ) ^ ((a : ℤ) - 1) < (p : ℝ) := by
    rw [hc, zpow_natCast]
    exact_mod_cast helig
  have hsur := EthBridge.cExcess_ceil_halving a p (by omega) hpz
  have hq : (7 : ℝ) * (((p + 1) / 2 : ℕ) : ℝ) ≤ 4 * (p : ℝ) := by
    exact_mod_cast ceil_half_ratio p hp
  have hr : (((p + 1) / 2 : ℕ) : ℝ) / (p : ℝ) ≤ 4 / 7 := by
    apply (div_le_iff₀ hpR).mpr
    linarith
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have he : (((p + 1) / 2 : ℕ) : ℝ) / (p : ℝ) *
      (extra + Real.log 2) ≤ extra := by
    unfold extra
    nlinarith [mul_le_mul_of_nonneg_right hr hlog]
  have hh := mul_le_mul_of_nonneg_right hsur hlam
  nlinarith

variable [Nonempty X] [Nonempty Y]

/-- A three-coordinate projection of any flag-one state at level at least two
has the two-copy ladder's three-copy density.  The projected matrix is an
actual restriction of the same original interlace. -/
theorem three_projection_from_base (F : X → Y → Bool) (C p a : ℕ)
    (θ lam : ℝ) (hθ : 0 < θ)
    (hlam : 0 < lam) (ha : 2 ≤ a) (hp : 2 ^ a < 2 * p)
    (hmargin : 3 * lam + (7 / 5) * Real.log 2 ≤ -2 * Real.log (3 / 5))
    (hThree : ∀ (R₃ : Finset (Fin 3 × X)) (K₃ : Finset (Fin 3 → Y)),
      (R₃, K₃) ∈ NPCC.bracketGE X Y 3 (4 * θ) ((3 / 5 : ℝ) ^ 2) →
      C + 1 ≤ D (NPCC.subgame (fullInterlace F 3) R₃ K₃))
    (RC : Finset (Fin p × X) × Finset (Fin p → Y))
    (hmem : RC ∈ oneState (X := X) (Y := Y) p a θ lam) :
    C + 1 ≤ D (NPCC.subgame (fullInterlace F p) RC.1 RC.2) := by
  classical
  obtain ⟨hrows, hcols⟩ := hmem
  have hp3 : 3 ≤ p := by
    have hcut := Paper2.DefectArithmetic.cutoff_mono ha
    rw [Paper2.DefectArithmetic.cutoff_two] at hcut
    have hreal := (Paper2.DefectArithmetic.cutoff_lt_iff_pow_lt a p).mpr hp
    have : (2 : ℝ) < p := lt_of_le_of_lt hcut hreal
    exact_mod_cast this
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hp0 : (0 : ℝ) < p := by linarith
  have hc_pos : 0 < EthBridge.cExcess a p := by
    change 0 < (p : ℝ) - Paper2.DefectArithmetic.cutoff a
    exact sub_pos.mpr ((Paper2.DefectArithmetic.cutoff_lt_iff_pow_lt a p).mpr hp)
  have harg_nonneg : 0 ≤ EthBridge.cExcess a p * lam + extra :=
    add_nonneg (mul_nonneg hc_pos.le hlam.le) extra_nonneg
  have hyp_one : Real.exp (-(EthBridge.cExcess a p * lam + extra)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  obtain ⟨R', K', hrows', hcols', hDle⟩ :=
    EthBridge.member_max_projection F p 3
      (EthBridge.rowThreshold (Fintype.card X) θ a)
      (Real.exp (-(EthBridge.cExcess a p * lam + extra)))
      (by norm_num) hp3 (Real.exp_pos _) hyp_one
      Fintype.card_pos Fintype.card_pos RC.1 RC.2 hrows hcols
  have hc_scaled : 3 / (p : ℝ) * EthBridge.cExcess a p ≤ 3 := by
    have hcut : 0 ≤ Paper2.DefectArithmetic.cutoff a :=
      (Paper2.DefectArithmetic.cutoff_pos a).le
    have hcle : EthBridge.cExcess a p ≤ (p : ℝ) := by
      change (p : ℝ) - Paper2.DefectArithmetic.cutoff a ≤ p
      linarith
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hp0).mpr
    nlinarith
  have hrat : 3 / (p : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hp0).mpr
    linarith
  have hcorr : 3 / (p : ℝ) * extra ≤ (7 / 5) * Real.log 2 := by
    have hmul := mul_le_mul_of_nonneg_right hrat extra_nonneg
    have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    unfold extra at *
    linarith
  have hbudget :
      3 / (p : ℝ) * (EthBridge.cExcess a p * lam + extra) ≤
        -2 * Real.log (3 / 5) := by
    calc
      3 / (p : ℝ) * (EthBridge.cExcess a p * lam + extra) =
          (3 / (p : ℝ) * EthBridge.cExcess a p) * lam +
            3 / (p : ℝ) * extra := by ring
      _ ≤ 3 * lam + (7 / 5) * Real.log 2 :=
        add_le_add (mul_le_mul_of_nonneg_right hc_scaled hlam.le) hcorr
      _ ≤ -2 * Real.log (3 / 5) := hmargin
  have hrpow_eq :
      Real.rpow (Real.exp (-(EthBridge.cExcess a p * lam + extra)))
          (3 / (p : ℝ)) =
        Real.exp (-(EthBridge.cExcess a p * lam + extra) * (3 / (p : ℝ))) := by
    change (Real.exp _) ^ (3 / (p : ℝ)) = _
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  have hy_sq_exp : ((3 : ℝ) / 5) ^ 2 = Real.exp (2 * Real.log (3 / 5)) := by
    calc
      ((3 : ℝ) / 5) ^ 2 = (Real.exp (Real.log (3 / 5))) ^ 2 := by
        rw [Real.exp_log (by norm_num : (0 : ℝ) < 3 / 5)]
      _ = Real.exp (2 * Real.log (3 / 5)) := by
        rw [← Real.exp_nat_mul]
        norm_num
  have hy2_le : ((3 : ℝ) / 5) ^ 2 ≤
      Real.rpow (Real.exp (-(EthBridge.cExcess a p * lam + extra)))
        (3 / (p : ℝ)) := by
    rw [hy_sq_exp, hrpow_eq, Real.exp_le_exp,
      show -(EthBridge.cExcess a p * lam + extra) * (3 / (p : ℝ)) =
        -(3 / (p : ℝ) * (EthBridge.cExcess a p * lam + extra)) from by ring]
    linarith
  have hmem3 : (R', K') ∈ NPCC.bracketGE X Y 3 (4 * θ) ((3 / 5 : ℝ) ^ 2) := by
    refine ⟨?_, ?_⟩
    · intro j hj
      refine le_trans ?_ (hrows' j hj)
      have hthr := EthBridge.rowThreshold_mono (Fintype.card X) θ hθ.le ha
      calc
        ⌈(Fintype.card X : ℝ) * (4 * θ)⌉₊ =
            EthBridge.rowThreshold (Fintype.card X) θ 2 := by
              unfold EthBridge.rowThreshold
              congr 1
              ring
        _ ≤ EthBridge.rowThreshold (Fintype.card X) θ a := hthr
    · apply Nat.ceil_le.mpr
      calc
        ((Fintype.card Y : ℝ) ^ 3) * ((3 / 5 : ℝ) ^ 2) ≤
            ((Fintype.card Y : ℝ) ^ 3) *
              Real.rpow (Real.exp (-(EthBridge.cExcess a p * lam + extra)))
                (3 / (p : ℝ)) :=
          mul_le_mul_of_nonneg_left hy2_le (by positivity)
        _ ≤ (K'.card : ℝ) := by exact_mod_cast hcols'
  exact (hThree R' K' hmem3).trans hDle

/-- The five-block induction base from an independently proved five-copy
restriction bound.  The state-to-restriction conversion is exact. -/
theorem five_block_from_base (F : X → Y → Bool) (C : ℕ) (θ lam : ℝ)
    (hlam : 0 < lam)
    (hmargin : 3 * lam + (7 / 5) * Real.log 2 ≤ -2 * Real.log (3 / 5))
    (hFive : ∀ (R₅ : Finset (Fin 5 × X)) (K₅ : Finset (Fin 5 → Y)),
      (R₅, K₅) ∈ NPCC.bracketGE X Y 5 ((2 : ℝ) ^ 3 * θ) (9 / 25 : ℝ) →
      C + 2 ≤ D (NPCC.subgame (fullInterlace F 5) R₅ K₅))
    (RC : Finset (Fin 5 × X) × Finset (Fin 5 → Y))
    (hmem : RC ∈ oneState (X := X) (Y := Y) 5 3 θ lam) :
    C + 2 ≤ D (NPCC.subgame (fullInterlace F 5) RC.1 RC.2) := by
  classical
  obtain ⟨hrows, hcols⟩ := hmem
  have hc : EthBridge.cExcess 3 5 = 1 := by norm_num [EthBridge.cExcess]
  have hcorr : extra ≤ (7 / 5) * Real.log 2 := by
    have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    unfold extra
    linarith
  have hbudget : EthBridge.cExcess 3 5 * lam + extra ≤
      -2 * Real.log (3 / 5) := by
    rw [hc]
    linarith
  have hdens : (9 : ℝ) / 25 ≤
      Real.exp (-(EthBridge.cExcess 3 5 * lam + extra)) := by
    have hsq : ((3 : ℝ) / 5) ^ 2 =
        Real.exp (2 * Real.log (3 / 5)) := by
      calc
        ((3 : ℝ) / 5) ^ 2 = (Real.exp (Real.log (3 / 5))) ^ 2 := by
          rw [Real.exp_log (by norm_num : (0 : ℝ) < 3 / 5)]
        _ = Real.exp (2 * Real.log (3 / 5)) := by
          rw [← Real.exp_nat_mul]
          norm_num
    norm_num at hsq ⊢
    rw [hsq, Real.exp_le_exp]
    linarith
  have hRC : (RC.1, RC.2) ∈
      ClassicalRows.restrictions (X := X) (Y := Y) 5 ((2 : ℝ) ^ 3 * θ) (9 / 25) := by
    refine ⟨?_, ?_⟩
    · intro j hj
      convert hrows j hj using 1
      unfold EthBridge.rowThreshold
      congr 1
      ring
    · apply Nat.ceil_le.mpr
      calc
        ((Fintype.card Y : ℝ) ^ 5) * (9 / 25 : ℝ) ≤
            ((Fintype.card Y : ℝ) ^ 5) *
              Real.exp (-(EthBridge.cExcess 3 5 * lam + extra)) :=
          mul_le_mul_of_nonneg_left hdens (by positivity)
        _ ≤ (RC.2.card : ℝ) := hcols
  exact hFive RC.1 RC.2 hRC

theorem one_alice_step (F : X → Y → Bool) (C p a : ℕ) (θ lam : ℝ)
    (ha : 3 ≤ a) (hp : 2 ^ a < 2 * p) (hθ : 0 < θ)
    (hscale : (2 : ℝ) ^ a * θ ≤ 1) (hlam : 0 < lam)
    (RC : Finset (Fin p × X) × Finset (Fin p → Y))
    (hmem : RC ∈ oneState (X := X) (Y := Y) p a θ lam)
    (α : (Fin p × X) → Bool)
    (hchild : ∀ b : Bool,
      D (NPCC.subgame (fullInterlace F p)
          (RC.1.filter fun r => α r = b) RC.2) + 1 ≤
        D (NPCC.subgame (fullInterlace F p) RC.1 RC.2))
    (IH : ∀ p' : ℕ, 2 ^ (a - 1) < 2 * p' →
      (2 : ℝ) ^ (a - 1) * θ ≤ 1 →
      ∀ RC' : Finset (Fin p' × X) × Finset (Fin p' → Y),
        RC' ∈ oneState (X := X) (Y := Y) p' (a - 1) θ lam →
        C + (a - 1) - 1 ≤ D (NPCC.subgame (fullInterlace F p') RC'.1 RC'.2)) :
    C + a - 1 ≤ D (NPCC.subgame (fullInterlace F p) RC.1 RC.2) := by
  classical
  obtain ⟨hrows, hcols⟩ := hmem
  have hp1 : 1 ≤ p := by
    have hh : 1 ≤ 2 ^ a := Nat.one_le_two_pow
    omega
  have hc_pos : 0 < EthBridge.cExcess a p := by
    change 0 < (p : ℝ) - Paper2.DefectArithmetic.cutoff a
    exact sub_pos.mpr ((Paper2.DefectArithmetic.cutoff_lt_iff_pow_lt a p).mpr hp)
  have hyp_one : Real.exp (-(EthBridge.cExcess a p * lam + extra)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have := add_nonneg (mul_nonneg hc_pos.le hlam.le) extra_nonneg
    linarith
  obtain ⟨p₀, p₁, y₀, y₁, S₀, K₀, S₁, K₁, hpsum, hyy,
      hy₀pos, hy₀le1, hy₁pos, hy₁le1, _hdeg₀, _hdeg₁, hside₀, hside₁⟩ :=
    EthBridge.alice_coordinate_split F p
      (EthBridge.rowThreshold (Fintype.card X) θ a)
      (Real.exp (-(EthBridge.cExcess a p * lam + extra)))
      hp1 (Real.exp_pos _) hyp_one Fintype.card_pos Fintype.card_pos
      RC.1 RC.2 α hrows hcols
  have hadd : -Real.log y₀ + -Real.log y₁ ≤
      EthBridge.cExcess a p * lam + extra :=
    EthBridge.neg_log_sum_le y₀ y₁ _ hy₀pos hy₁pos hyy
  have hsel := const_alice_selection a p p₀ p₁
    (-Real.log y₀) (-Real.log y₁) lam (by omega) hp hpsum hlam
    (neg_nonneg.mpr (Real.log_nonpos hy₀pos.le hy₀le1))
    (neg_nonneg.mpr (Real.log_nonpos hy₁pos.le hy₁le1)) hadd
  have hAhalf := EthBridge.rowThreshold_ceil_halving (Fintype.card X) θ a (by omega)
  have hscale' := Paper2.DefectArithmetic.pred_scale_guard a θ hθ.le hscale
  rcases hsel with ⟨helig, hbud⟩ | ⟨helig, hbud⟩
  · have hp₀ : 1 ≤ p₀ := by
      have hh : 1 ≤ 2 ^ (a - 1) := Nat.one_le_two_pow
      omega
    obtain ⟨hequi, hcolsb, hDle⟩ := hside₀ hp₀
    have hexp : Real.exp (-(EthBridge.cExcess (a - 1) p₀ * lam + extra)) ≤ y₀ := by
      have hlog : -(EthBridge.cExcess (a - 1) p₀ * lam + extra) ≤ Real.log y₀ := by
        linarith
      calc
        Real.exp (-(EthBridge.cExcess (a - 1) p₀ * lam + extra)) ≤
            Real.exp (Real.log y₀) := Real.exp_le_exp.mpr hlog
        _ = y₀ := Real.exp_log hy₀pos
    have hmem' : (S₀, K₀) ∈ oneState (X := X) (Y := Y) p₀ (a - 1) θ lam := by
      refine ⟨?_, ?_⟩
      · intro j hj
        exact le_trans hAhalf (hequi j hj)
      · calc
          ((Fintype.card Y : ℝ) ^ p₀) *
              Real.exp (-(EthBridge.cExcess (a - 1) p₀ * lam + extra)) ≤
              ((Fintype.card Y : ℝ) ^ p₀) * y₀ :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
          _ ≤ (K₀.card : ℝ) := hcolsb
    have hIH := IH p₀ helig hscale' (S₀, K₀) hmem'
    calc
      C + a - 1 = (C + (a - 1) - 1) + 1 := by omega
      _ ≤ D (NPCC.subgame (fullInterlace F p₀) S₀ K₀) + 1 :=
        Nat.add_le_add_right hIH 1
      _ ≤ D (NPCC.subgame (fullInterlace F p)
            (RC.1.filter fun r => α r = false) RC.2) + 1 :=
        Nat.add_le_add_right hDle 1
      _ ≤ D (NPCC.subgame (fullInterlace F p) RC.1 RC.2) := hchild false
  · have hp₁ : 1 ≤ p₁ := by
      have hh : 1 ≤ 2 ^ (a - 1) := Nat.one_le_two_pow
      omega
    obtain ⟨hequi, hcolsb, hDle⟩ := hside₁ hp₁
    have hexp : Real.exp (-(EthBridge.cExcess (a - 1) p₁ * lam + extra)) ≤ y₁ := by
      have hlog : -(EthBridge.cExcess (a - 1) p₁ * lam + extra) ≤ Real.log y₁ := by
        linarith
      calc
        Real.exp (-(EthBridge.cExcess (a - 1) p₁ * lam + extra)) ≤
            Real.exp (Real.log y₁) := Real.exp_le_exp.mpr hlog
        _ = y₁ := Real.exp_log hy₁pos
    have hmem' : (S₁, K₁) ∈ oneState (X := X) (Y := Y) p₁ (a - 1) θ lam := by
      refine ⟨?_, ?_⟩
      · intro j hj
        exact le_trans hAhalf (hequi j hj)
      · calc
          ((Fintype.card Y : ℝ) ^ p₁) *
              Real.exp (-(EthBridge.cExcess (a - 1) p₁ * lam + extra)) ≤
              ((Fintype.card Y : ℝ) ^ p₁) * y₁ :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
          _ ≤ (K₁.card : ℝ) := hcolsb
    have hIH := IH p₁ helig hscale' (S₁, K₁) hmem'
    calc
      C + a - 1 = (C + (a - 1) - 1) + 1 := by omega
      _ ≤ D (NPCC.subgame (fullInterlace F p₁) S₁ K₁) + 1 :=
        Nat.add_le_add_right hIH 1
      _ ≤ D (NPCC.subgame (fullInterlace F p)
            (RC.1.filter fun r => α r = true) RC.2) + 1 :=
        Nat.add_le_add_right hDle 1
      _ ≤ D (NPCC.subgame (fullInterlace F p) RC.1 RC.2) := hchild true

theorem one_bob_step (F : X → Y → Bool) (C p a : ℕ) (θ lam : ℝ)
    (ha : 3 ≤ a) (hp : 6 ≤ p) (helig : 2 ^ a < 2 * p)
    (hθ : 0 < θ) (hscale : (2 : ℝ) ^ a * θ ≤ 1) (hlam : 0 < lam)
    (RC : Finset (Fin p × X) × Finset (Fin p → Y))
    (hmem : RC ∈ oneState (X := X) (Y := Y) p a θ lam)
    (β : (Fin p → Y) → Bool)
    (hchild : ∀ b : Bool,
      D (NPCC.subgame (fullInterlace F p)
          RC.1 (RC.2.filter fun c => β c = b)) + 1 ≤
        D (NPCC.subgame (fullInterlace F p) RC.1 RC.2))
    (IH : ∀ p' : ℕ, 2 ^ (a - 1) < 2 * p' →
      (2 : ℝ) ^ (a - 1) * θ ≤ 1 →
      ∀ RC' : Finset (Fin p' × X) × Finset (Fin p' → Y),
        RC' ∈ oneState (X := X) (Y := Y) p' (a - 1) θ lam →
        C + (a - 1) - 1 ≤ D (NPCC.subgame (fullInterlace F p') RC'.1 RC'.2)) :
    C + a - 1 ≤ D (NPCC.subgame (fullInterlace F p) RC.1 RC.2) := by
  classical
  obtain ⟨hrows, hcols⟩ := hmem
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hc_pos : 0 < EthBridge.cExcess a p := by
    change 0 < (p : ℝ) - Paper2.DefectArithmetic.cutoff a
    exact sub_pos.mpr ((Paper2.DefectArithmetic.cutoff_lt_iff_pow_lt a p).mpr helig)
  have harg_nonneg : 0 ≤ EthBridge.cExcess a p * lam + extra :=
    add_nonneg (mul_nonneg hc_pos.le hlam.le) extra_nonneg
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hyc_one : Real.exp (-(EthBridge.cExcess a p * lam + extra + Real.log 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  obtain ⟨b, hb⟩ := EthBridge.exists_denser_child RC.2 β
  have hKb_cols :
      ((Fintype.card Y : ℝ) ^ p) *
          Real.exp (-(EthBridge.cExcess a p * lam + extra + Real.log 2)) ≤
        ((RC.2.filter fun c => β c = b).card : ℝ) := by
    have hsplit :
        Real.exp (-(EthBridge.cExcess a p * lam + extra + Real.log 2)) =
          Real.exp (-(EthBridge.cExcess a p * lam + extra)) / 2 := by
      rw [show -(EthBridge.cExcess a p * lam + extra + Real.log 2) =
          -(EthBridge.cExcess a p * lam + extra) + -Real.log 2 from by ring,
        Real.exp_add, Real.exp_neg (Real.log 2),
        Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      ring
    calc
      ((Fintype.card Y : ℝ) ^ p) *
          Real.exp (-(EthBridge.cExcess a p * lam + extra + Real.log 2)) =
          (((Fintype.card Y : ℝ) ^ p) *
            Real.exp (-(EthBridge.cExcess a p * lam + extra))) / 2 := by
        rw [hsplit]
        ring
      _ ≤ (RC.2.card : ℝ) / 2 := by linarith
      _ ≤ ((RC.2.filter fun c => β c = b).card : ℝ) := hb
  let q := (p + 1) / 2
  have hq1 : 1 ≤ q := by
    dsimp [q]
    omega
  have hqp : q ≤ p := by
    dsimp [q]
    omega
  obtain ⟨R', K', hrows', hcols', hDle⟩ :=
    EthBridge.member_max_projection F p q
      (EthBridge.rowThreshold (Fintype.card X) θ a)
      (Real.exp (-(EthBridge.cExcess a p * lam + extra + Real.log 2)))
      hq1 hqp (Real.exp_pos _) hyc_one Fintype.card_pos Fintype.card_pos
      RC.1 (RC.2.filter fun c => β c = b) hrows hKb_cols
  have hp' : 2 ^ (a - 1) < p := by
    have he : 2 ^ a = 2 * 2 ^ (a - 1) := by
      conv_lhs => rw [show a = (a - 1) + 1 by omega]
      rw [pow_succ']
    omega
  have hbudget : ((q : ℝ) / (p : ℝ)) *
      (EthBridge.cExcess a p * lam + extra + Real.log 2) ≤
      EthBridge.cExcess (a - 1) q * lam + extra := by
    simpa only [q] using const_bob_budget a p lam ha hp hlam.le hp'
  have hrpow_eq :
      Real.rpow (Real.exp (-(EthBridge.cExcess a p * lam + extra + Real.log 2)))
          ((q : ℝ) / (p : ℝ)) =
        Real.exp (-(EthBridge.cExcess a p * lam + extra + Real.log 2) *
          ((q : ℝ) / (p : ℝ))) := by
    change (Real.exp _) ^ ((q : ℝ) / (p : ℝ)) = _
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  have hdens :
      Real.exp (-(EthBridge.cExcess (a - 1) q * lam + extra)) ≤
        Real.rpow (Real.exp (-(EthBridge.cExcess a p * lam + extra + Real.log 2)))
          ((q : ℝ) / (p : ℝ)) := by
    rw [hrpow_eq, Real.exp_le_exp,
      show -(EthBridge.cExcess a p * lam + extra + Real.log 2) *
          ((q : ℝ) / (p : ℝ)) =
        -(((q : ℝ) / (p : ℝ)) *
          (EthBridge.cExcess a p * lam + extra + Real.log 2)) from by ring]
    linarith
  have hqElig : 2 ^ (a - 1) < 2 * q := by
    have hcut := (Paper2.DefectArithmetic.cutoff_lt_iff_pow_lt a p).mpr helig
    have hhalf := Paper2.DefectArithmetic.half_eligible a p (by omega) hcut
    exact (Paper2.DefectArithmetic.cutoff_lt_iff_pow_lt (a - 1) q).mp hhalf
  have hmem' : (R', K') ∈ oneState (X := X) (Y := Y) q (a - 1) θ lam := by
    refine ⟨?_, ?_⟩
    · intro j hj
      exact le_trans (EthBridge.rowThreshold_mono (Fintype.card X) θ hθ.le
        (by omega : a - 1 ≤ a)) (hrows' j hj)
    · calc
        ((Fintype.card Y : ℝ) ^ q) *
            Real.exp (-(EthBridge.cExcess (a - 1) q * lam + extra)) ≤
            ((Fintype.card Y : ℝ) ^ q) *
              Real.rpow (Real.exp
                (-(EthBridge.cExcess a p * lam + extra + Real.log 2)))
                ((q : ℝ) / (p : ℝ)) :=
          mul_le_mul_of_nonneg_left hdens (by positivity)
        _ ≤ (K'.card : ℝ) := by exact_mod_cast hcols'
  have hscale' := Paper2.DefectArithmetic.pred_scale_guard a θ hθ.le hscale
  have hIH := IH q hqElig hscale' (R', K') hmem'
  calc
    C + a - 1 = (C + (a - 1) - 1) + 1 := by omega
    _ ≤ D (NPCC.subgame (fullInterlace F q) R' K') + 1 :=
      Nat.add_le_add_right hIH 1
    _ ≤ D (NPCC.subgame (fullInterlace F p)
          RC.1 (RC.2.filter fun c => β c = b)) + 1 :=
      Nat.add_le_add_right hDle 1
    _ ≤ D (NPCC.subgame (fullInterlace F p) RC.1 RC.2) := hchild b

/-- The exact first-message two-block adapter for the main-state a=1 Bob branch. -/
theorem main_bob_step_a1_from_base
    (W : X → Y → Bool) (C p : ℕ) (x y lam : ℝ)
    (hp : 2 ≤ p)
    (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hlam : 0 < lam) (hX : 1 ≤ Fintype.card X)
    (hmargin : 3 * lam + (7 / 5) * Real.log 2 ≤ -2 * Real.log y)
    (hTwoHigh : ∀ (R₂ : Finset (Fin 2 × X)) (K₂ : Finset (Fin 2 → Y)),
      (R₂, K₂) ∈ NPCC.bracketGE X Y 2 (2 * x) (y ^ 2) →
      C ≤ D (NPCC.subgame (interlaceFun W 2) R₂ K₂))
    (RC : Finset (Fin p × X) × Finset (Fin p → Y))
    (hmem : RC ∈ stateDensity X Y p 1 x lam)
    (β : (Fin p → Y) → Bool)
    (hchild : ∀ b : Bool,
      D (NPCC.subgame (interlaceFun W p)
          RC.1 (RC.2.filter fun c => β c = b)) + 1 ≤
        D (NPCC.subgame (interlaceFun W p) RC.1 RC.2)) :
    C + 1 ≤ D (NPCC.subgame (interlaceFun W p) RC.1 RC.2) := by
  classical
  obtain ⟨hrows, hcols⟩ := hmem
  -- `hY` is derivable: empty `Y` (with `p ≥ 2`) empties the column set, so
  -- `hchild` would read `D + 1 ≤ D`.
  have hY : 1 ≤ Fintype.card Y := by
    by_contra hY0
    have hY0' : Fintype.card Y = 0 := by omega
    have hYempty : IsEmpty Y := Fintype.card_eq_zero_iff.mp hY0'
    have hnoc : ∀ c : Fin p → Y, False :=
      fun c => hYempty.false (c ⟨0, by omega⟩)
    have hempty2 : RC.2 = ∅ := by
      ext c
      exact (hnoc c).elim
    have h := hchild true
    rw [hempty2, Finset.filter_empty] at h
    omega
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  -- arithmetic facts about the level-1 budget `c_1(p) = p - 1`
  have hc1 : cExcess 1 p = (p : ℝ) - 1 := by
    unfold cExcess
    norm_num
  have hc_nonneg : 0 ≤ cExcess 1 p := by rw [hc1]; linarith
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hyc_one : Real.exp (-(cExcess 1 p * lam + Real.log 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ cExcess 1 p * lam := mul_nonneg hc_nonneg hlam.le
    linarith
  -- Bob's first bit: one fiber keeps at least half the columns —
  -- column density `y_p / 2`, i.e. defect budget `+ ln 2`
  obtain ⟨b, hb⟩ := exists_denser_child RC.2 β
  have hKb_cols :
      ((Fintype.card Y : ℝ) ^ p) *
          Real.exp (-(cExcess 1 p * lam + Real.log 2)) ≤
        (((RC.2.filter fun c => β c = b).card : ℝ)) := by
    have hsplit :
        Real.exp (-(cExcess 1 p * lam + Real.log 2)) =
          Real.exp (-(cExcess 1 p * lam)) / 2 := by
      rw [show -(cExcess 1 p * lam + Real.log 2) =
          -(cExcess 1 p * lam) + -Real.log 2 from by ring,
        Real.exp_add, Real.exp_neg (Real.log 2),
        Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      ring
    calc
      ((Fintype.card Y : ℝ) ^ p) *
          Real.exp (-(cExcess 1 p * lam + Real.log 2))
          = (((Fintype.card Y : ℝ) ^ p) *
              Real.exp (-(cExcess 1 p * lam))) / 2 := by
            rw [hsplit]; ring
      _ ≤ (RC.2.card : ℝ) / 2 := by linarith
      _ ≤ ((RC.2.filter fun c => β c = b).card : ℝ) := hb
  -- maximum projection to TWO coordinates (`ℓ = 2`, `T = A_1`)
  obtain ⟨R', C', hrows', hcols', hDle⟩ :=
    member_max_projection W p 2 (rowThreshold (Fintype.card X) x 1)
      (Real.exp (-(cExcess 1 p * lam + Real.log 2)))
      (by norm_num) hp (Real.exp_pos _) hyc_one hX hY
      RC.1 (RC.2.filter fun c => β c = b) hrows hKb_cols
  -- budget: `(2/p)(c_1(p)λ + ln 2) ≤ 2λ + ln 2 ≤ 3λ + (7/5)ln 2 ≤ -2 ln y`
  have hc_scaled : 2 / (p : ℝ) * cExcess 1 p ≤ 2 := by
    rw [hc1, div_mul_eq_mul_div, div_le_iff₀ hp0]
    nlinarith
  have hlog_scaled : 2 / (p : ℝ) * Real.log 2 ≤ Real.log 2 := by
    have h2p : 2 / (p : ℝ) ≤ 1 := by
      rw [div_le_one hp0]; linarith
    calc
      2 / (p : ℝ) * Real.log 2 ≤ 1 * Real.log 2 :=
        mul_le_mul_of_nonneg_right h2p hlog2
      _ = Real.log 2 := one_mul _
  have hbudget :
      2 / (p : ℝ) * (cExcess 1 p * lam + Real.log 2) ≤ -2 * Real.log y := by
    calc
      2 / (p : ℝ) * (cExcess 1 p * lam + Real.log 2)
          = (2 / (p : ℝ) * cExcess 1 p) * lam +
              2 / (p : ℝ) * Real.log 2 := by ring
      _ ≤ 2 * lam + Real.log 2 :=
        add_le_add (mul_le_mul_of_nonneg_right hc_scaled hlam.le) hlog_scaled
      _ ≤ 3 * lam + (7 / 5) * Real.log 2 := by linarith
      _ ≤ -2 * Real.log y := hmargin
  -- hence the projected density dominates `y²`
  have hrpow_eq :
      Real.rpow (Real.exp (-(cExcess 1 p * lam + Real.log 2))) (2 / (p : ℝ)) =
        Real.exp (-(cExcess 1 p * lam + Real.log 2) * (2 / (p : ℝ))) := by
    change (Real.exp _) ^ (2 / (p : ℝ)) = _
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  have hy_sq_exp : y ^ 2 = Real.exp (2 * Real.log y) := by
    calc
      y ^ 2 = (Real.exp (Real.log y)) ^ 2 := by rw [Real.exp_log hy0]
      _ = Real.exp (2 * Real.log y) := by
        rw [← Real.exp_nat_mul]
        norm_num
  have hy2_le :
      y ^ 2 ≤
        Real.rpow (Real.exp (-(cExcess 1 p * lam + Real.log 2)))
          (2 / (p : ℝ)) := by
    rw [hy_sq_exp, hrpow_eq, Real.exp_le_exp,
      show -(cExcess 1 p * lam + Real.log 2) * (2 / (p : ℝ)) =
        -(2 / (p : ℝ) * (cExcess 1 p * lam + Real.log 2)) from by ring]
    linarith
  -- the projected member lands in `NPCC.bracketGE X Y 2 (2x) (y²)`
  have hmem2 : (R', C') ∈ NPCC.bracketGE X Y 2 (2 * x) (y ^ 2) := by
    refine ⟨?_, ?_⟩
    · intro j hj
      refine le_trans (le_of_eq ?_) (hrows' j hj)
      unfold rowThreshold
      congr 1
      ring
    · apply Nat.ceil_le.mpr
      calc
        ((Fintype.card Y : ℝ) ^ 2) * y ^ 2
            ≤ ((Fintype.card Y : ℝ) ^ 2) *
                Real.rpow (Real.exp (-(cExcess 1 p * lam + Real.log 2)))
                  (2 / (p : ℝ)) :=
          mul_le_mul_of_nonneg_left hy2_le (by positivity)
        _ ≤ (C'.card : ℝ) := by exact_mod_cast hcols'
  have hchain :
      C ≤ D (NPCC.subgame (interlaceFun W p)
        RC.1 (RC.2.filter fun c => β c = b)) :=
    (hTwoHigh R' C' hmem2).trans hDle
  calc
    C + 1 ≤ D (NPCC.subgame (interlaceFun W p)
        RC.1 (RC.2.filter fun c => β c = b)) + 1 :=
      Nat.add_le_add_right hchain 1
    _ ≤ D (NPCC.subgame (interlaceFun W p) RC.1 RC.2) := hchild b


theorem one_state_from_bases (F : X → Y → Bool) (C p a : ℕ) (θ lam : ℝ)
    (hθ : 0 < θ) (hlam : 0 < lam)
    (ha : 2 ≤ a) (hp : 2 ^ a < 2 * p)
    (hscale : (2 : ℝ) ^ a * θ ≤ 1)
    (hmargin : 3 * lam + (7 / 5) * Real.log 2 ≤ -2 * Real.log (3 / 5))
    (hThree : ∀ (R₃ : Finset (Fin 3 × X)) (K₃ : Finset (Fin 3 → Y)),
      (R₃, K₃) ∈ NPCC.bracketGE X Y 3 (4 * θ) ((3 / 5 : ℝ) ^ 2) →
      C + 1 ≤ D (NPCC.subgame (fullInterlace F 3) R₃ K₃))
    (hFive : ∀ (R₅ : Finset (Fin 5 × X)) (K₅ : Finset (Fin 5 → Y)),
      (R₅, K₅) ∈ NPCC.bracketGE X Y 5 ((2 : ℝ) ^ 3 * θ) (9 / 25 : ℝ) →
      C + 2 ≤ D (NPCC.subgame (fullInterlace F 5) R₅ K₅))
    (RC : Finset (Fin p × X) × Finset (Fin p → Y))
    (hmem : RC ∈ oneState (X := X) (Y := Y) p a θ lam) :
    C + a - 1 ≤ D (NPCC.subgame (fullInterlace F p) RC.1 RC.2) := by
  have H : ∀ a : ℕ, 2 ≤ a →
      ∀ p : ℕ, 2 ^ a < 2 * p → (2 : ℝ) ^ a * θ ≤ 1 →
      ∀ RC : Finset (Fin p × X) × Finset (Fin p → Y),
        RC ∈ oneState (X := X) (Y := Y) p a θ lam →
        C + a - 1 ≤ D (NPCC.subgame (fullInterlace F p) RC.1 RC.2) := by
    intro a ha
    induction a, ha using Nat.le_induction with
    | base =>
        intro p hp hscale RC hmem
        simpa using three_projection_from_base F C p 2 θ lam hθ
          hlam (by omega) hp hmargin hThree RC hmem
    | succ a ha IH =>
        intro p hp hscale RC hmem
        have hp5 : 5 ≤ p := by
          have hcut := Paper2.DefectArithmetic.cutoff_mono
            (by omega : 3 ≤ a + 1)
          have hfour : Paper2.DefectArithmetic.cutoff 3 = 4 := by
            norm_num [Paper2.DefectArithmetic.cutoff]
          rw [hfour] at hcut
          have hreal :=
            (Paper2.DefectArithmetic.cutoff_lt_iff_pow_lt (a + 1) p).mpr hp
          exact_mod_cast lt_of_le_of_lt hcut hreal
        by_cases hpEq : p = 5
        · have ha3 : a + 1 = 3 := by
            by_contra hn
            have ha4 : 4 ≤ a + 1 := by omega
            have hpow : 16 ≤ 2 ^ (a + 1) := by
              calc
                16 = 2 ^ 4 := by norm_num
                _ ≤ 2 ^ (a + 1) := Nat.pow_le_pow_right (by norm_num) ha4
            omega
          subst p
          rw [ha3] at hscale hmem ⊢
          exact five_block_from_base F C θ lam hlam hmargin hFive RC hmem
        · have hp6 : 6 ≤ p := by omega
          have hrough := three_projection_from_base F C p (a + 1) θ lam
            hθ hlam (by omega) hp hmargin hThree RC hmem
          have hpos : 1 ≤ D (NPCC.subgame (fullInterlace F p) RC.1 RC.2) := by
            omega
          have IH' : ∀ p' : ℕ, 2 ^ ((a + 1) - 1) < 2 * p' →
              (2 : ℝ) ^ ((a + 1) - 1) * θ ≤ 1 →
              ∀ RC' : Finset (Fin p' × X) × Finset (Fin p' → Y),
                RC' ∈ oneState (X := X) (Y := Y) p' ((a + 1) - 1) θ lam →
                C + ((a + 1) - 1) - 1 ≤
                  D (NPCC.subgame (fullInterlace F p') RC'.1 RC'.2) := by
            simpa only [Nat.add_sub_cancel] using IH
          rcases EthBridge.subgame_first_bit_dichotomy (fullInterlace F p)
              RC.1 RC.2 hpos with ⟨α, hchild⟩ | ⟨β, hchild⟩
          · exact one_alice_step F C p (a + 1) θ lam (by omega) hp hθ
              hscale hlam RC hmem α hchild IH'
          · exact one_bob_step F C p (a + 1) θ lam (by omega) hp6 hp
              hθ hscale hlam RC hmem β hchild IH'
  exact H a ha p hp hscale RC hmem

/-- A Bob-first main state spends one bit and enters the fixed-allowance
flag-one state at the same scale. -/
theorem main_bob_step_from_one (F : X → Y → Bool) (C p a : ℕ) (θ lam : ℝ)
    (ha : 2 ≤ a) (hp : 2 ^ a < 2 * p)
    (RC : Finset (Fin p × X) × Finset (Fin p → Y))
    (hmem : RC ∈ EthBridge.stateDensity X Y p a θ lam)
    (β : (Fin p → Y) → Bool)
    (hchild : ∀ b : Bool,
      D (NPCC.subgame (fullInterlace F p)
          RC.1 (RC.2.filter fun c => β c = b)) + 1 ≤
        D (NPCC.subgame (fullInterlace F p) RC.1 RC.2))
    (hOne : ∀ RC' : Finset (Fin p × X) × Finset (Fin p → Y),
      RC' ∈ oneState (X := X) (Y := Y) p a θ lam →
      C + a - 1 ≤ D (NPCC.subgame (fullInterlace F p) RC'.1 RC'.2)) :
    C + a ≤ D (NPCC.subgame (fullInterlace F p) RC.1 RC.2) := by
  obtain ⟨hrows, hcols⟩ := hmem
  obtain ⟨b, hb⟩ := EthBridge.exists_denser_child RC.2 β
  have hlog : Real.log 2 ≤ extra := by
    unfold extra
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    linarith
  have hmem' : (RC.1, RC.2.filter fun c => β c = b) ∈
      oneState (X := X) (Y := Y) p a θ lam := by
    refine ⟨hrows, ?_⟩
    have hhalf : Real.exp (-(EthBridge.cExcess a p * lam + extra)) ≤
        Real.exp (-(EthBridge.cExcess a p * lam + Real.log 2)) := by
      rw [Real.exp_le_exp]
      linarith
    have hsplit :
        Real.exp (-(EthBridge.cExcess a p * lam + Real.log 2)) =
          Real.exp (-(EthBridge.cExcess a p * lam)) / 2 := by
      rw [show -(EthBridge.cExcess a p * lam + Real.log 2) =
          -(EthBridge.cExcess a p * lam) + -Real.log 2 from by ring,
        Real.exp_add, Real.exp_neg (Real.log 2),
        Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      ring
    calc
      ((Fintype.card Y : ℝ) ^ p) *
          Real.exp (-(EthBridge.cExcess a p * lam + extra))
          ≤ ((Fintype.card Y : ℝ) ^ p) *
              Real.exp (-(EthBridge.cExcess a p * lam + Real.log 2)) :=
            mul_le_mul_of_nonneg_left hhalf (by positivity)
      _ = (((Fintype.card Y : ℝ) ^ p) *
            Real.exp (-(EthBridge.cExcess a p * lam))) / 2 := by
          rw [hsplit]; ring
      _ ≤ (RC.2.card : ℝ) / 2 := by linarith
      _ ≤ ((RC.2.filter fun c => β c = b).card : ℝ) := hb
  have hout := hOne (RC.1, RC.2.filter fun c => β c = b) hmem'
  calc
    C + a = (C + a - 1) + 1 := by omega
    _ ≤ D (NPCC.subgame (fullInterlace F p)
          RC.1 (RC.2.filter fun c => β c = b)) + 1 :=
      Nat.add_le_add_right hout 1
    _ ≤ D (NPCC.subgame (fullInterlace F p) RC.1 RC.2) := hchild b

/-- An inhabited row-restriction family automatically satisfies the scale
guard: one block cannot retain more rows than its full input alphabet. -/
theorem scale_of_rows (p a : ℕ) (θ : ℝ) (hp : 1 ≤ p)
    (R : Finset (Fin p × X))
    (hrows : NPCC.IsEquipartitionedGE R Finset.univ
      (EthBridge.rowThreshold (Fintype.card X) θ a)) :
    (2 : ℝ) ^ a * θ ≤ 1 := by
  classical
  let q : Fin p := ⟨0, by omega⟩
  have hfib := hrows q (Finset.mem_univ q)
  have hle : (R.filter (fun z => z.1 = q)).card ≤ Fintype.card X := by
    rw [← Finset.card_univ]
    apply Finset.card_le_card_of_injOn (fun z => z.2)
    · intro z _; exact Finset.mem_univ _
    · intro z hz w hw hzw
      have hzq : z.1 = q := (Finset.mem_filter.mp hz).2
      have hwq : w.1 = q := (Finset.mem_filter.mp hw).2
      exact Prod.ext (hzq.trans hwq.symm) hzw
  have hceil : EthBridge.rowThreshold (Fintype.card X) θ a ≤ Fintype.card X :=
    hfib.trans hle
  have hreal : (Fintype.card X : ℝ) * ((2 : ℝ) ^ a * θ) ≤
      (Fintype.card X : ℝ) := by
    calc
      (Fintype.card X : ℝ) * ((2 : ℝ) ^ a * θ) =
          (Fintype.card X : ℝ) * (2 : ℝ) ^ a * θ := by ring
      _ ≤ (EthBridge.rowThreshold (Fintype.card X) θ a : ℝ) :=
        Nat.le_ceil _
      _ ≤ (Fintype.card X : ℝ) := by exact_mod_cast hceil
  have hm : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos (α := X)
  exact le_of_mul_le_mul_left (by simpa using hreal) hm

/-- The exact main-state induction consumes only the near-full one-copy base,
the two-copy high-density base, and the two flag-one small-block bases. -/
theorem main_state_from_bases (F : X → Y → Bool) (C p a : ℕ) (θ lam : ℝ)
    (hC : 3 ≤ C) (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 4) (hlam : 0 < lam)
    (hp : 2 ^ a < 2 * p) (hscale : (2 : ℝ) ^ a * θ ≤ 1)
    (hmargin : 3 * lam + (7 / 5) * Real.log 2 ≤ -2 * Real.log (3 / 5))
    (hNear : EthBridge.NearFull F C θ lam)
    (hTwoHigh : ∀ (R₂ : Finset (Fin 2 × X)) (K₂ : Finset (Fin 2 → Y)),
      (R₂, K₂) ∈ NPCC.bracketGE X Y 2 (2 * θ) ((3 / 5 : ℝ) ^ 2) →
      C ≤ D (NPCC.subgame (fullInterlace F 2) R₂ K₂))
    (hThree : ∀ (R₃ : Finset (Fin 3 × X)) (K₃ : Finset (Fin 3 → Y)),
      (R₃, K₃) ∈ NPCC.bracketGE X Y 3 (4 * θ) ((3 / 5 : ℝ) ^ 2) →
      C + 1 ≤ D (NPCC.subgame (fullInterlace F 3) R₃ K₃))
    (hFive : ∀ (R₅ : Finset (Fin 5 × X)) (K₅ : Finset (Fin 5 → Y)),
      (R₅, K₅) ∈ NPCC.bracketGE X Y 5 ((2 : ℝ) ^ 3 * θ) (9 / 25 : ℝ) →
      C + 2 ≤ D (NPCC.subgame (fullInterlace F 5) R₅ K₅))
    (RC : Finset (Fin p × X) × Finset (Fin p → Y))
    (hmem : RC ∈ EthBridge.stateDensity X Y p a θ lam) :
    C + a ≤ D (NPCC.subgame (fullInterlace F p) RC.1 RC.2) := by
  have H : ∀ a : ℕ, ∀ p : ℕ, 2 ^ a < 2 * p →
      (2 : ℝ) ^ a * θ ≤ 1 →
      ∀ RC : Finset (Fin p × X) × Finset (Fin p → Y),
        RC ∈ EthBridge.stateDensity X Y p a θ lam →
        C + a ≤ D (NPCC.subgame (fullInterlace F p) RC.1 RC.2) := by
    intro a
    induction a with
    | zero =>
        intro p hp hscale RC hmem
        have hp1 : 1 ≤ p := by omega
        exact EthBridge.terminal_a0_member F C p θ lam hp1 hθ (by linarith)
          hlam Fintype.card_pos hNear RC hmem
    | succ a IH =>
        intro p hp hscale RC hmem
        have hp1 : 1 ≤ p := by
          have hpow : 1 ≤ 2 ^ (a + 1) := Nat.one_le_two_pow
          omega
        have hnc : 1 ≤ D (NPCC.subgame (fullInterlace F p) RC.1 RC.2) :=
          EthBridge.main_nonconstant F C p (a + 1) θ lam hp1 hθ
            (by linarith) hlam Fintype.card_pos (by omega) hNear RC hmem
        rcases EthBridge.subgame_first_bit_dichotomy (fullInterlace F p)
            RC.1 RC.2 hnc with ⟨α, hchild⟩ | ⟨β, hchild⟩
        · have IH' : ∀ p' : ℕ, 2 ^ ((a + 1) - 1) < 2 * p' →
              ∀ RC' : Finset (Fin p' × X) × Finset (Fin p' → Y),
                RC' ∈ EthBridge.stateDensity X Y p' ((a + 1) - 1) θ lam →
                C + ((a + 1) - 1) ≤
                  D (NPCC.subgame (fullInterlace F p') RC'.1 RC'.2) := by
            intro p' hp' RC' hmem'
            have hp1' : 1 ≤ p' := by
              have hpow' : 1 ≤ 2 ^ ((a + 1) - 1) := Nat.one_le_two_pow
              omega
            have hscale' := scale_of_rows p' a θ hp1' RC'.1 hmem'.1
            simpa only [Nat.add_sub_cancel] using IH p' (by simpa using hp')
              hscale' RC' (by simpa using hmem')
          exact EthBridge.main_alice_step F C p (a + 1) θ lam
            (by omega) hp hlam Fintype.card_pos Fintype.card_pos
            RC hmem α hchild IH'
        · rcases Nat.eq_zero_or_pos a with rfl | ha1
          · have hp2 : 2 ≤ p := by norm_num at hp; omega
            exact main_bob_step_a1_from_base F C p θ (3 / 5) lam hp2
              (by norm_num) (by norm_num) hlam Fintype.card_pos hmargin
              hTwoHigh RC hmem β hchild
          · have ha2 : 2 ≤ a + 1 := by omega
            have hOne : ∀ RC' : Finset (Fin p × X) × Finset (Fin p → Y),
                RC' ∈ oneState (X := X) (Y := Y) p (a + 1) θ lam →
                C + (a + 1) - 1 ≤
                  D (NPCC.subgame (fullInterlace F p) RC'.1 RC'.2) := by
              intro RC' hm'
              exact one_state_from_bases F C p (a + 1) θ lam hθ hlam
                ha2 hp hscale hmargin hThree hFive RC' hm'
            exact main_bob_step_from_one F C p (a + 1) θ lam ha2 hp
              RC hmem β hchild hOne
  exact H a p hp hscale RC hmem

/-- The fixed-allowance defect theorem, conditional only on the three exact
small-block lower bounds that v38 derives by first-message analysis. -/
theorem defect_induction_from_bases (F : X → Y → Bool) (C p a e : ℕ) (θ δ : ℝ)
    (hC : 3 ≤ C) (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 4)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 64)
    (he : e ≤ 1) (ha : 2 * e ≤ a)
    (hp : 2 ^ a < 2 * p) (hscale : (2 : ℝ) ^ a * θ ≤ 1)
    (hnear : C ≤ Paper2.ClassicalRows.restrictionCost F 1 θ (1 - δ))
    (hTwoHigh : ∀ (R₂ : Finset (Fin 2 × X)) (K₂ : Finset (Fin 2 → Y)),
      (R₂, K₂) ∈ NPCC.bracketGE X Y 2 (2 * θ) ((3 / 5 : ℝ) ^ 2) →
      C ≤ D (NPCC.subgame (fullInterlace F 2) R₂ K₂))
    (hThree : ∀ (R₃ : Finset (Fin 3 × X)) (K₃ : Finset (Fin 3 → Y)),
      (R₃, K₃) ∈ NPCC.bracketGE X Y 3 (4 * θ) ((3 / 5 : ℝ) ^ 2) →
      C + 1 ≤ D (NPCC.subgame (fullInterlace F 3) R₃ K₃))
    (hFive : ∀ (R₅ : Finset (Fin 5 × X)) (K₅ : Finset (Fin 5 → Y)),
      (R₅, K₅) ∈ NPCC.bracketGE X Y 5 ((2 : ℝ) ^ 3 * θ) (9 / 25 : ℝ) →
      C + 2 ≤ D (NPCC.subgame (fullInterlace F 5) R₅ K₅))
    (R : Finset (Fin p × X)) (K : Finset (Fin p → Y)) (hK : K.Nonempty)
    (hR : NPCC.IsEquipartitionedGE R Finset.univ
      ⌈(Fintype.card X : ℝ) * (2 : ℝ) ^ a * θ⌉₊)
    (hdef : ProjectionDefect.defect (ProjectionDefect.columnDensity p K) ≤
      ((p : ℝ) - (2 : ℝ) ^ ((a : ℤ) - 1)) * δ +
        (e : ℝ) * (4 / 3)) :
    C + a - e ≤ D (NPCC.subgame (fullInterlace F p) R K) := by
  have hmargin := Paper2.DefectLogMargin.natural_log_margin hδ1
  have hlam : 0 < δ * Real.log 2 :=
    mul_pos hδ (Real.log_pos (by norm_num))
  have hNear := Paper2.DefectInduction.near_full_input F C θ δ hθ hθ1
    hδ hδ1 hnear
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp he with rfl | rfl
  · simp only [Nat.cast_zero, zero_mul, add_zero] at hdef
    have hc := Paper2.DefectInduction.natural_defect_bound p K _ hdef
    have hcn : EthBridge.colDefect Y p K ≤
        EthBridge.cExcess a p * (δ * Real.log 2) := by
      simpa only [EthBridge.cExcess, mul_assoc] using hc
    have hcols := (EthBridge.state_defect_iff_density Y p K _
      hK.card_pos Fintype.card_pos).mp hcn
    have hmem : (R, K) ∈ EthBridge.stateDensity X Y p a θ
        (δ * Real.log 2) := by
      refine ⟨?_, hcols⟩
      intro j hj
      simpa only [EthBridge.rowThreshold, mul_assoc] using hR j hj
    exact main_state_from_bases F C p a θ (δ * Real.log 2) hC hθ hθ1
      hlam hp hscale hmargin hNear hTwoHigh hThree hFive (R, K) hmem
  · simp only [Nat.cast_one, one_mul] at hdef
    have hc := Paper2.DefectInduction.natural_defect_bound p K _ hdef
    have hcn : EthBridge.colDefect Y p K ≤
        EthBridge.cExcess a p * (δ * Real.log 2) + extra := by
      dsimp only [EthBridge.cExcess, extra]
      nlinarith
    have hcols := (EthBridge.state_defect_iff_density Y p K _
      hK.card_pos Fintype.card_pos).mp hcn
    have hmem : (R, K) ∈ oneState (X := X) (Y := Y) p a θ
        (δ * Real.log 2) := by
      refine ⟨?_, hcols⟩
      intro j hj
      simpa only [EthBridge.rowThreshold, mul_assoc] using hR j hj
    exact one_state_from_bases F C p a θ (δ * Real.log 2) hθ hlam
      (by omega) hp hscale hmargin hThree hFive (R, K) hmem


end Paper2.V38DefectInduction
