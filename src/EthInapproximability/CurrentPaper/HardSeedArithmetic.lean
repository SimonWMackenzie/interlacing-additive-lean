import NPCC.Engine

/-!
# Explicit arithmetic for the current paper's small-column-density bound

Source: the locked v8 `sections/D-hard-seed.tex`,
`eq:foundation-hard-seed-gates`.  The depth uses a ceiling, unlike the
floor-depth asymptotic argument in `NPCC.Engine`.
-/

namespace EthInapproximability.CurrentPaper.HardSeedArithmetic

noncomputable def depth (m : ℕ) : ℕ :=
  ⌈Real.sqrt (m : ℝ) / Real.logb 2 (m : ℝ)⌉₊

noncomputable def chiExponent (m : ℕ) : ℝ :=
  (2 : ℝ) ^ (-((2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt (m : ℝ))))

theorem side_from_log {ρ : ℝ} {k s : ℕ}
    (hρ2 : 2 < ρ) (hs : s ≤ k)
    (hlog : (s : ℝ) * ρ * Real.log ρ ≤ (k : ℝ)) :
    (ρ - 1) ^ k ≤ ρ ^ (k - s) := by
  have hρpos : 0 < ρ := by linarith
  have hρone : 1 < ρ := by linarith
  have hρm1pos : 0 < ρ - 1 := by linarith
  have hunitpos : 0 < 1 - 1 / ρ := by
    rw [sub_pos]
    exact (div_lt_one hρpos).mpr hρone
  have hfactor : ρ - 1 = ρ * (1 - 1 / ρ) := by
    field_simp [ne_of_gt hρpos]
  have hlog_factor : Real.log (ρ - 1) = Real.log ρ + Real.log (1 - 1 / ρ) := by
    rw [hfactor]
    exact Real.log_mul (ne_of_gt hρpos) (ne_of_gt hunitpos)
  have hlog_unit_le : Real.log (1 - 1 / ρ) ≤ -1 / ρ := by
    have h := Real.log_le_sub_one_of_pos hunitpos
    have hsimp : 1 - 1 / ρ - 1 = -1 / ρ := by ring
    rwa [hsimp] at h
  have hlog_m1_le : Real.log (ρ - 1) ≤ Real.log ρ - 1 / ρ := by
    calc
      Real.log (ρ - 1) = Real.log ρ + Real.log (1 - 1 / ρ) := hlog_factor
      _ ≤ Real.log ρ + (-1 / ρ) := add_le_add_right hlog_unit_le _
      _ = Real.log ρ - 1 / ρ := by ring
  have hslog_le : (s : ℝ) * Real.log ρ ≤ (k : ℝ) / ρ := by
    rw [le_div_iff₀ hρpos]
    nlinarith [hlog]
  have hmain :
      (k : ℝ) * Real.log (ρ - 1) ≤ ((k : ℝ) - (s : ℝ)) * Real.log ρ := by
    have hmul := mul_le_mul_of_nonneg_left hlog_m1_le (by positivity : 0 ≤ (k : ℝ))
    nlinarith [hmul, hslog_le]
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, Nat.cast_sub hs]
  rw [Real.rpow_le_iff_le_log hρm1pos
    (Real.rpow_pos_of_pos hρpos ((k : ℝ) - (s : ℝ)))]
  rw [Real.log_rpow hρpos]
  exact hmain

theorem gridFloor_le_mul_of_beta {ρ : ℝ} {k s p q : ℕ}
    (hβ : ((ρ - 1) / (ρ - 2)) ^ s * (p : ℝ) ≤ (q : ℝ)) :
    NPCC.gridFloor ρ k s p ≤ q * 2 ^ k := by
  unfold NPCC.gridFloor
  apply Nat.floor_le_of_le
  calc
    (2 : ℝ) ^ k * ((ρ - 1) / (ρ - 2)) ^ s * (p : ℝ)
        ≤ (2 : ℝ) ^ k * (q : ℝ) := by
          nlinarith [mul_le_mul_of_nonneg_left hβ (by positivity : 0 ≤ (2 : ℝ) ^ k)]
    _ = ((q * 2 ^ k : ℕ) : ℝ) := by push_cast; ring

theorem beta_bound {ρ : ℝ} {s : ℕ}
    (hρ : 1024 ≤ ρ) (hs : (s : ℝ) ≤ ρ / 20 + 1) :
    ((ρ - 1) / (ρ - 2)) ^ s * (17 : ℝ) ≤ 18 := by
  have hm2 : 0 < ρ - 2 := by linarith
  have hbpos : 0 < (ρ - 1) / (ρ - 2) := div_pos (by linarith) hm2
  have hb1 : 1 ≤ (ρ - 1) / (ρ - 2) := by
    rw [le_div_iff₀ hm2]
    linarith
  have hlogb : Real.log ((ρ - 1) / (ρ - 2)) ≤ 1 / (ρ - 2) := by
    have h := Real.log_le_sub_one_of_pos hbpos
    have heq : (ρ - 1) / (ρ - 2) - 1 = 1 / (ρ - 2) := by
      field_simp
      ring
    simpa only [heq] using h
  have hratio : (ρ / 20 + 1) / (ρ - 2) ≤ (1 / 18 : ℝ) := by
    rw [div_le_iff₀ hm2]
    linarith
  have hlog18 : (1 / 18 : ℝ) ≤ Real.log (18 / 17 : ℝ) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 18 / 17)
    norm_num at h ⊢
    exact h
  have hlogpow : (s : ℝ) * Real.log ((ρ - 1) / (ρ - 2)) ≤
      Real.log (18 / 17 : ℝ) := by
    calc
      (s : ℝ) * Real.log ((ρ - 1) / (ρ - 2))
          ≤ (ρ / 20 + 1) * Real.log ((ρ - 1) / (ρ - 2)) :=
        mul_le_mul_of_nonneg_right hs (Real.log_nonneg hb1)
      _ ≤ (ρ / 20 + 1) * (1 / (ρ - 2)) :=
        mul_le_mul_of_nonneg_left hlogb (by linarith)
      _ = (ρ / 20 + 1) / (ρ - 2) := by ring
      _ ≤ 1 / 18 := hratio
      _ ≤ Real.log (18 / 17 : ℝ) := hlog18
  have hp : ((ρ - 1) / (ρ - 2)) ^ s ≤ (18 / 17 : ℝ) := by
    rw [← Real.rpow_natCast]
    exact (Real.rpow_le_iff_le_log hbpos (by norm_num)).mpr hlogpow
  linarith

theorem large_log_bound (r : ℝ) (hr : 1024 ≤ r) :
    Real.log r ≤ r / 4 * Real.log 2 := by
  have hrpos : 0 < r := by linarith
  have hlower : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hupper : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hsixteen : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 4 using 1
    norm_num
  have hdiv := Real.log_le_sub_one_of_pos
    (div_pos hrpos (by norm_num : (0 : ℝ) < 16))
  rw [Real.log_div (ne_of_gt hrpos) (by norm_num : (16 : ℝ) ≠ 0), hsixteen] at hdiv
  nlinarith [mul_nonneg (by linarith : 0 ≤ r / 4) (sub_nonneg.mpr hlower)]

theorem base_estimates {m : ℕ} (hm : 2 ^ 20 ≤ m) :
    1024 ≤ Real.sqrt (m : ℝ) ∧
    20 ≤ Real.logb 2 (m : ℝ) ∧
    Real.logb 2 (m : ℝ) ≤ Real.sqrt (m : ℝ) / 2 := by
  have hmr : (2 : ℝ) ^ (20 : ℕ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hr : 1024 ≤ Real.sqrt (m : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    norm_num at hmr ⊢
    exact hmr
  have hl20 : 20 ≤ Real.logb 2 (m : ℝ) := by
    have h := Real.logb_le_logb_of_le (b := 2) (by norm_num : (1 : ℝ) < 2)
      (by positivity : (0 : ℝ) < (2 : ℝ) ^ (20 : ℕ)) hmr
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at h
    simpa only [Nat.cast_ofNat, mul_one] using h
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hls := large_log_bound (Real.sqrt (m : ℝ)) hr
  rw [Real.log_sqrt hm0] at hls
  have hlupper : Real.logb 2 (m : ℝ) ≤ Real.sqrt (m : ℝ) / 2 := by
    rw [Real.logb, div_le_iff₀ hlog2]
    nlinarith
  exact ⟨hr, hl20, hlupper⟩

theorem depth_bounds {m : ℕ} (hm : 2 ^ 20 ≤ m) :
    Real.sqrt (m : ℝ) / Real.logb 2 (m : ℝ) ≤ (depth m : ℝ) ∧
    (depth m : ℝ) ≤ Real.sqrt (m : ℝ) / Real.logb 2 (m : ℝ) + 1 ∧
    (depth m : ℝ) ≤ Real.sqrt (m : ℝ) / 20 + 1 := by
  obtain ⟨hr, hl, _⟩ := base_estimates hm
  have hnonneg : 0 ≤ Real.sqrt (m : ℝ) / Real.logb 2 (m : ℝ) := by positivity
  have hceil : (depth m : ℝ) ≤
      Real.sqrt (m : ℝ) / Real.logb 2 (m : ℝ) + 1 :=
    le_of_lt (Nat.ceil_lt_add_one hnonneg)
  refine ⟨Nat.le_ceil _, hceil, ?_⟩
  have hdiv : Real.sqrt (m : ℝ) / Real.logb 2 (m : ℝ) ≤
      Real.sqrt (m : ℝ) / 20 :=
    div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by norm_num) hl
  linarith

theorem log_gate {m : ℕ} (hm : 2 ^ 20 ≤ m) :
    (depth m : ℝ) * Real.sqrt (m : ℝ) * Real.log (Real.sqrt (m : ℝ)) ≤
      ((m - 5 : ℕ) : ℝ) := by
  obtain ⟨hr, hl, hlu⟩ := base_estimates hm
  obtain ⟨_, hs, _⟩ := depth_bounds hm
  have hm5 : 5 ≤ m := by omega
  have hlpos : 0 < Real.logb 2 (m : ℝ) := by linarith
  have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog2upper : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hlogrho : Real.log (Real.sqrt (m : ℝ)) =
      Real.logb 2 (m : ℝ) * Real.log 2 / 2 := by
    rw [Real.log_sqrt (Nat.cast_nonneg m), Real.logb]
    field_simp
  have hsquare := Real.sq_sqrt (Nat.cast_nonneg m)
  have hexpand :
      (Real.sqrt (m : ℝ) / Real.logb 2 (m : ℝ) + 1) *
        Real.sqrt (m : ℝ) * Real.log (Real.sqrt (m : ℝ)) =
      (Real.log 2 / 2) *
        ((m : ℝ) + Real.sqrt (m : ℝ) * Real.logb 2 (m : ℝ)) := by
    rw [hlogrho]
    field_simp [ne_of_gt hlpos]
    nlinarith [hsquare]
  have hprod : Real.sqrt (m : ℝ) * Real.logb 2 (m : ℝ) ≤ (m : ℝ) / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hlu (Real.sqrt_nonneg (m : ℝ)), hsquare]
  have hbound : (Real.log 2 / 2) *
      ((m : ℝ) + Real.sqrt (m : ℝ) * Real.logb 2 (m : ℝ)) ≤
      3 / 4 * (m : ℝ) := by
    have hp0 : 0 ≤ (m : ℝ) + Real.sqrt (m : ℝ) * Real.logb 2 (m : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hlog2upper hp0]
  have hsbound := mul_le_mul_of_nonneg_right hs
    (show 0 ≤ Real.sqrt (m : ℝ) * Real.log (Real.sqrt (m : ℝ)) by
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (by linarith)))
  rw [Nat.cast_sub hm5]
  norm_num
  have hmr : (1048576 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  calc
    (depth m : ℝ) * Real.sqrt (m : ℝ) * Real.log (Real.sqrt (m : ℝ))
        ≤ (Real.sqrt (m : ℝ) / Real.logb 2 (m : ℝ) + 1) *
          Real.sqrt (m : ℝ) * Real.log (Real.sqrt (m : ℝ)) := by
            simpa only [mul_assoc] using hsbound
    _ = (Real.log 2 / 2) *
        ((m : ℝ) + Real.sqrt (m : ℝ) * Real.logb 2 (m : ℝ)) := hexpand
    _ ≤ 3 / 4 * (m : ℝ) := hbound
    _ ≤ (m : ℝ) - 5 := by linarith

theorem column_bound {m : ℕ} (hm : 2 ^ 20 ≤ m) :
    (1 / 2 : ℝ) ^ (Real.sqrt (m : ℝ) ^ depth m) ≤ chiExponent m := by
  obtain ⟨hr, hl, _⟩ := base_estimates hm
  obtain ⟨hs, _, _⟩ := depth_bounds hm
  have hrpos : 0 < Real.sqrt (m : ℝ) := by linarith
  have hlpos : 0 < Real.logb 2 (m : ℝ) := by linarith
  have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogrho : Real.log (Real.sqrt (m : ℝ)) =
      Real.logb 2 (m : ℝ) * Real.log 2 / 2 := by
    rw [Real.log_sqrt (Nat.cast_nonneg m), Real.logb]
    field_simp
  have hpoweq : Real.sqrt (m : ℝ) ^
      (Real.sqrt (m : ℝ) / Real.logb 2 (m : ℝ)) =
      (2 : ℝ) ^ ((1 / 2 : ℝ) * Real.sqrt (m : ℝ)) := by
    rw [Real.rpow_def_of_pos hrpos,
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), hlogrho]
    congr 1
    field_simp
  have hexplower : (2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt (m : ℝ)) ≤
      Real.sqrt (m : ℝ) ^ depth m := by
    calc
      (2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt (m : ℝ))
          ≤ (2 : ℝ) ^ ((1 / 2 : ℝ) * Real.sqrt (m : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (by nlinarith [Real.sqrt_nonneg (m : ℝ)])
      _ = Real.sqrt (m : ℝ) ^
          (Real.sqrt (m : ℝ) / Real.logb 2 (m : ℝ)) := hpoweq.symm
      _ ≤ Real.sqrt (m : ℝ) ^ (depth m : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hs
      _ = Real.sqrt (m : ℝ) ^ depth m := Real.rpow_natCast _ _
  have hhalf : (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) := by norm_num
  rw [hhalf, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  unfold chiExponent
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  linarith

/-- All explicit numerical hypotheses used at the density-iteration call in
the current small-column-density theorem, at the manuscript's fixed cutoff. -/
theorem numeric_gates {m : ℕ} (hm : 2 ^ 20 ≤ m) :
    5 ≤ m ∧
    2 < Real.sqrt (m : ℝ) ∧
    depth m ≤ m - 5 ∧
    (Real.sqrt (m : ℝ) - 1) ^ (m - 5) ≤
      Real.sqrt (m : ℝ) ^ ((m - 5) - depth m) ∧
    NPCC.gridFloor (Real.sqrt (m : ℝ)) (m - 5) (depth m) 17 ≤ 18 * 2 ^ (m - 5) ∧
    (1 / 2 : ℝ) ^ (Real.sqrt (m : ℝ) ^ depth m) ≤ chiExponent m := by
  obtain ⟨hr, _, _⟩ := base_estimates hm
  obtain ⟨_, _, hsupper⟩ := depth_bounds hm
  have hlog := log_gate hm
  have hr2 : 2 < Real.sqrt (m : ℝ) := by linarith
  have hrlog : 1 ≤ Real.sqrt (m : ℝ) * Real.log (Real.sqrt (m : ℝ)) := by
    have hloglow := Real.one_sub_inv_le_log_of_pos (by linarith : 0 < Real.sqrt (m : ℝ))
    have hmul := mul_le_mul_of_nonneg_left hloglow (Real.sqrt_nonneg (m : ℝ))
    have heq : Real.sqrt (m : ℝ) * (1 - (Real.sqrt (m : ℝ))⁻¹) =
        Real.sqrt (m : ℝ) - 1 := by field_simp
    rw [heq] at hmul
    linarith
  have hsk : depth m ≤ m - 5 := by
    have hmul := mul_le_mul_of_nonneg_left hrlog (Nat.cast_nonneg (depth m) : (0 : ℝ) ≤ depth m)
    have hreal : (depth m : ℝ) ≤ ((m - 5 : ℕ) : ℝ) := by nlinarith
    exact_mod_cast hreal
  refine ⟨by omega, hr2, hsk, side_from_log hr2 hsk hlog, ?_, column_bound hm⟩
  exact gridFloor_le_mul_of_beta (beta_bound hr hsupper)

end EthInapproximability.CurrentPaper.HardSeedArithmetic
