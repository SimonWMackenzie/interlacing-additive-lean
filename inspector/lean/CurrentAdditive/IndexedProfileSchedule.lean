import CurrentAdditive.IndexedProfileBudget
import CurrentAdditive.DeterministicParameters

/-! Numerical continuation for Appendix I `det:profiles`. The finite ratio
estimates are supplied by the checked deterministic schedule module; this
file converts them into the exact population budgets used by the profile
proofs. Frozen proof modules are not edited. -/

namespace CurrentAdditive.DeterministicIndexedMatrix

open CurrentAdditive.DeterministicParameters
open Paper2 Paper2.SourcePopulation
open Workspace.Types.CommComplexity

private theorem beta_power (j : ℕ) :
    (1/2 : ℝ)^j = 1 / (2 : ℝ)^j := by
  rw [div_pow]
  simp

private theorem ratio_A_identity
    (p u ρ : ℝ) (hp : 0 < p) (hu : 0 < u) :
    (p*u-2) * ((3/5 : ℝ)/p-u*ρ) =
      u*((3/5 : ℝ)*(1-2/(p*u))-(p*u-2)*ρ) := by
  field_simp

private theorem ratio_T_identity
    (p u x : ℝ) (hp : 0 < p) :
    (p*u)*((3/5 : ℝ)/p-u*x) =
      u*((3/5 : ℝ)-(p*u)*x) := by
  field_simp

private theorem ratio_N_identity
    (p u β x : ℝ) :
    (p*u)*(β-u*x) = u*(p*β-(p*u)*x) := by
  ring

private theorem source_power_relation (L : ℕ) (j : Fin 3)
    (hL : 2004 ≤ L) :
    s L = 2^j.val * 2^(((L+3)/4)-j.val) := by
  have ha : j.val ≤ (L+3)/4 := by omega
  calc
    s L = 2^((L+3)/4) := rfl
    _ = 2^(((L+3)/4-j.val)+j.val) := by congr 1; omega
    _ = 2^(((L+3)/4)-j.val) * 2^j.val := by rw [pow_add]
    _ = 2^j.val * 2^(((L+3)/4)-j.val) := by ac_rfl

private theorem second_power_relation (L : ℕ) (j : Fin 3)
    (hL : 2004 ≤ L) :
    q₂ L = 2^j.val * 2^(4*L-j.val) := by
  have hj : j.val ≤ 4*L := by omega
  calc
    q₂ L = 2^(4*L) := q₂_eq_pow L
    _ = 2^((4*L-j.val)+j.val) := by congr 1; omega
    _ = 2^(4*L-j.val) * 2^j.val := by rw [pow_add]
    _ = 2^j.val * 2^(4*L-j.val) := by ac_rfl

private theorem small_exception_on_first (L : ℕ) (hL : 2004 ≤ L)
    (j : Fin 3) :
    32 * CurrentAdditive.conditioningExceptionCountR 1024 (x L : ℝ) 1 ≤
      2^(((L+3)/4)-j.val) := by
  have he := conditioning_exception_x_small L hL
  have hcount : CurrentAdditive.conditioningExceptionCountR 1024 (x L : ℝ) 1 =
      CurrentAdditive.conditioningExceptionCount (x L : ℝ) 1 := rfl
  rw [← hcount] at he
  have hp := source_power_relation L j hL
  fin_cases j <;> norm_num at hp ⊢ <;> omega

private theorem small_exception_on_second (L : ℕ) (hL : 2004 ≤ L)
    (j : Fin 3) :
    32 * CurrentAdditive.conditioningExceptionCountR 1024 (x L : ℝ) 1 ≤
      2^(4*L-j.val) := by
  have hfirst := small_exception_on_first L hL j
  have ha : (L+3)/4-j.val ≤ 4*L-j.val := by omega
  exact hfirst.trans (Nat.pow_le_pow_right (by decide) ha)

theorem profile_A_budget (L : ℕ) (hL : 2004 ≤ L) (j : Fin 3) :
    ((2 ^ (((L+3)/4) - j.val - 1) + 1 +
      CurrentAdditive.conditioningExceptionCountR 1024 (x L : ℝ) 1 : ℕ) : ℝ) *
        (1 - (2 : ℝ)^(((L+3)/4) - j.val) * (ρ L : ℝ)) ≤
      (q₁ L : ℝ) * ((3/5 : ℝ) * (1/2 : ℝ)^j.val -
        (2 : ℝ)^(((L+3)/4) - j.val) * (ρ L : ℝ)) := by
  let k := ((L+3)/4)-j.val
  let u : ℝ := (2 : ℝ)^k
  let p : ℝ := (2 : ℝ)^j.val
  have hk : 5 ≤ k := by dsimp [k]; omega
  have he := small_exception_on_first L hL j
  have ht : (0 : ℝ) ≤ u * (ρ L : ℝ) := by
    have hρ : (0 : ℝ) < (ρ L : ℝ) := by
      unfold ρ N
      positivity
    positivity
  have hp : 0 < p := by dsimp [p]; positivity
  have hu : 0 < u := by dsimp [u]; positivity
  have hpow : (s L : ℝ) = p*u := by
    simpa only [p, u, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      congrArg (fun n : ℕ => (n : ℝ)) (source_power_relation L j hL)
  have hs2 : 2 ≤ s L := by
    have hs := s_ge_64 L (by omega)
    omega
  have hqnat : q₁ L + 2 = s L := by
    dsimp [q₁]
    exact Nat.sub_add_cancel hs2
  have hq : (q₁ L : ℝ) = p*u-2 := by
    have hqR : (q₁ L : ℝ)+2 = (s L : ℝ) := by exact_mod_cast hqnat
    linarith
  have hratio := profile_A_ratio_real L hL
  rw [hpow, hq] at hratio
  have hbeta : (3/5 : ℝ) * (1/2 : ℝ)^j.val = (3/5 : ℝ)/p := by
    rw [beta_power]
    dsimp [p]
    ring
  have htotal : (9/16 : ℝ) * (2^k : ℝ) ≤
      (q₁ L : ℝ) * ((3/5 : ℝ) * (1/2 : ℝ)^j.val - u*(ρ L : ℝ)) := by
    have hid := ratio_A_identity p u (ρ L : ℝ) hp hu
    calc
      (9/16 : ℝ) * (2^k : ℝ) ≤
          u*((3/5 : ℝ)*(1-2/(p*u))-(p*u-2)*(ρ L : ℝ)) := by
        have hm := mul_le_mul_of_nonneg_right hratio.le hu.le
        dsimp [u] at *
        nlinarith
      _ = (q₁ L : ℝ) *
          ((3/5 : ℝ) * (1/2 : ℝ)^j.val - u*(ρ L : ℝ)) := by
        rw [hq, hbeta]
        exact hid.symm
  exact dyadic_budget_of_ratio k
    (CurrentAdditive.conditioningExceptionCountR 1024 (x L : ℝ) 1)
    hk he (u * (ρ L : ℝ)) _ ht htotal

theorem profile_T_budget (L : ℕ) (hL : 2004 ≤ L) (j : Fin 3) :
    ((2 ^ (4*L - j.val - 1) + 1 +
      CurrentAdditive.conditioningExceptionCountR 1024 (x L : ℝ) 1 : ℕ) : ℝ) *
        (1 - (2 : ℝ)^(4*L-j.val) * (x L : ℝ)) ≤
      (q₂ L : ℝ) * ((3/5 : ℝ) * (1/2 : ℝ)^j.val -
        (2 : ℝ)^(4*L-j.val) * (x L : ℝ)) := by
  let k := 4*L-j.val
  let u : ℝ := (2 : ℝ)^k
  let p : ℝ := (2 : ℝ)^j.val
  have hk : 5 ≤ k := by dsimp [k]; omega
  have he := small_exception_on_second L hL j
  have ht : (0 : ℝ) ≤ u * (x L : ℝ) := by
    have hx := x_real_pos L
    positivity
  have hp : 0 < p := by dsimp [p]; positivity
  have hpow : (q₂ L : ℝ) = p*u := by
    simpa only [p, u, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      congrArg (fun n : ℕ => (n : ℝ)) (second_power_relation L j hL)
  have hratio := profile_T_ratio_real L (by omega)
  rw [hpow] at hratio
  have hbeta : (3/5 : ℝ) * (1/2 : ℝ)^j.val = (3/5 : ℝ)/p := by
    rw [beta_power]
    dsimp [p]
    ring
  have htotal : (9/16 : ℝ) * (2^k : ℝ) ≤
      (q₂ L : ℝ) * ((3/5 : ℝ) * (1/2 : ℝ)^j.val - u*(x L : ℝ)) := by
    have hid := ratio_T_identity p u (x L : ℝ) hp
    calc
      (9/16 : ℝ) * (2^k : ℝ) ≤
          u*((3/5 : ℝ)-(p*u)*(x L : ℝ)) := by
        have hm := mul_le_mul_of_nonneg_right hratio.le (by positivity : 0 ≤ u)
        dsimp [u] at *
        nlinarith
      _ = (q₂ L : ℝ) *
          ((3/5 : ℝ) * (1/2 : ℝ)^j.val - u*(x L : ℝ)) := by
        rw [hpow, hbeta]
        exact hid.symm
  exact dyadic_budget_of_ratio k
    (CurrentAdditive.conditioningExceptionCountR 1024 (x L : ℝ) 1)
    hk he (u * (x L : ℝ)) _ ht htotal

theorem profile_Nref_budget (L : ℕ) (hL : 2004 ≤ L) (j : Fin 3) :
    ((2 ^ (((L+3)/4) - j.val - 1) + 1 +
      CurrentAdditive.conditioningExceptionCountR 1024 (x L : ℝ) 1 : ℕ) : ℝ) *
        (1 - (2 : ℝ)^(((L+3)/4) - j.val) * (x L : ℝ)) ≤
      (s L : ℝ) *
        (((((3/5 : ℝ) * (1/2 : ℝ)^j.val) - (1-255/256)) /
          (255/256)) - (2 : ℝ)^(((L+3)/4) - j.val) * (x L : ℝ)) := by
  let k := ((L+3)/4)-j.val
  let u : ℝ := (2 : ℝ)^k
  let p : ℝ := (2 : ℝ)^j.val
  let β : ℝ := (((3/5 : ℝ) * (1/2 : ℝ)^j.val) - (1-255/256)) /
    (255/256)
  have hk : 5 ≤ k := by dsimp [k]; omega
  have he := small_exception_on_first L hL j
  have ht : (0 : ℝ) ≤ u * (x L : ℝ) := by
    have hx := x_real_pos L
    positivity
  have hpow : (s L : ℝ) = p*u := by
    simpa only [p, u, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      congrArg (fun n : ℕ => (n : ℝ)) (source_power_relation L j hL)
  have hratio := profile_Nref_ratio_real L hL j
  rw [hpow] at hratio
  have htotal : (9/16 : ℝ) * (2^k : ℝ) ≤
      (s L : ℝ) * (β - u*(x L : ℝ)) := by
    have hid := ratio_N_identity p u β (x L : ℝ)
    calc
      (9/16 : ℝ) * (2^k : ℝ) ≤
          u*(p*β-(p*u)*(x L : ℝ)) := by
        have hm := mul_le_mul_of_nonneg_right hratio.le (by positivity : 0 ≤ u)
        dsimp [u, β] at *
        nlinarith
      _ = (s L : ℝ) * (β - u*(x L : ℝ)) := by
        rw [hpow]
        exact hid.symm
  exact dyadic_budget_of_ratio k
    (CurrentAdditive.conditioningExceptionCountR 1024 (x L : ℝ) 1)
    hk he (u * (x L : ℝ)) _ ht htotal

private theorem power_le_s (L : ℕ) (hL : 2004 ≤ L) (j : Fin 3) :
    2^(((L+3)/4)-j.val) ≤ s L := by
  have hp := source_power_relation L j hL
  rw [hp]
  have h : 1 ≤ 2^j.val := by
    have hh : 0 < 2^j.val := by positivity
    omega
  calc
    2^(((L+3)/4)-j.val) = 1 * 2^(((L+3)/4)-j.val) := by omega
    _ ≤ 2^j.val * 2^(((L+3)/4)-j.val) := Nat.mul_le_mul_right _ h

private theorem power_le_q₂ (L : ℕ) (hL : 2004 ≤ L) (j : Fin 3) :
    2^(4*L-j.val) ≤ q₂ L := by
  have hp := second_power_relation L j hL
  rw [hp]
  have h : 1 ≤ 2^j.val := by
    have hh : 0 < 2^j.val := by positivity
    omega
  calc
    2^(4*L-j.val) = 1 * 2^(4*L-j.val) := by omega
    _ ≤ 2^j.val * 2^(4*L-j.val) := Nat.mul_le_mul_right _ h

theorem profile_A_scale (L : ℕ) (hL : 2004 ≤ L) (j : Fin 3) :
    (2 : ℝ)^(((L+3)/4)-j.val) * (ρ L : ℝ) < 1 := by
  have hp : ((2^(((L+3)/4)-j.val) : ℕ) : ℝ) ≤ (s L : ℝ) := by
    exact_mod_cast power_le_s L hL j
  have hr : (0 : ℝ) ≤ (ρ L : ℝ) := by
    unfold ρ N
    positivity
  have hsmall : (s L : ℝ) * (ρ L : ℝ) ≤ 1/1000 := by
    have hh : ((((s L : ℚ) * ρ L : ℚ)) : ℝ) ≤ ((1/1000 : ℚ) : ℝ) := by
      exact_mod_cast s_rho_small L hL
    simpa only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_div,
      Rat.cast_one, Rat.cast_ofNat] using hh
  have hm := mul_le_mul_of_nonneg_right hp hr
  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hm
  linarith

theorem profile_T_scale (L : ℕ) (hL : 2004 ≤ L) (j : Fin 3) :
    (2 : ℝ)^(4*L-j.val) * (x L : ℝ) < 1 := by
  have hp : ((2^(4*L-j.val) : ℕ) : ℝ) ≤ (q₂ L : ℝ) := by
    exact_mod_cast power_le_q₂ L hL j
  have hx := x_real_pos L
  have hm := mul_le_mul_of_nonneg_right hp hx.le
  have hr := profile_T_ratio_real L (by omega)
  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hm
  linarith

theorem profile_Nref_scale (L : ℕ) (hL : 2004 ≤ L) (j : Fin 3) :
    (2 : ℝ)^(((L+3)/4)-j.val) * (x L : ℝ) < 1 := by
  have hp : ((2^(((L+3)/4)-j.val) : ℕ) : ℝ) ≤ (s L : ℝ) := by
    exact_mod_cast power_le_s L hL j
  have hx := x_real_pos L
  have hm := mul_le_mul_of_nonneg_right hp hx.le
  have hsmall : (s L : ℝ) * (x L : ℝ) ≤ 1/1000 := by
    have hh : ((((s L : ℚ) * x L : ℚ)) : ℝ) ≤ ((1/1000 : ℚ) : ℝ) := by
      exact_mod_cast s_x_small L hL
    simpa only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_div,
      Rat.cast_one, Rat.cast_ofNat] using hh
  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hm
  linarith

theorem profile_A_width (L : ℕ) : q₁ L ≤ 2^((L+3)/4) := by
  dsimp [q₁, s]
  exact Nat.sub_le _ _

theorem profile_T_width (L : ℕ) : q₂ L ≤ 2^(4*L) := by
  rw [q₂_eq_pow]

/-- The checked manuscript parameter schedule, on one generated source triple.
The only mathematical input is the base matrix's exact cost and restriction
profile; the source and its three successor matrices are unchanged. -/
theorem Sources.generated_profiles_at_parameters
    {G V A X Y : Type*} [Fintype G] [Fintype V] [Fintype A]
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (L : ℕ) (hL : 2004 ≤ L)
    [NeZero (q₁ L)] [NeZero (q₂ L)] [NeZero (s L)]
    {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
    (src : Sources (D := 8192) (q₁ := q₁ L) (q₂ := q₂ L)
      (s := s L) μX μY)
    (μI : PositiveRationalLaw (G × (V ⊕ A)))
    (R : X → Y → Bool)
    (activity : (G × (V ⊕ A)) → Fin (q₂ L) → Option (Fin (s L)))
    (ξ₀ : Paper2.SourceMatrix.Tail (s L) Y)
    (d : ℕ) (hd : 3 ≤ d)
    (hD : D R = d)
    (hp : RestrictionProfile R μX.toFiniteLaw μY.toFiniteLaw
      (ρ L : ℝ) (d : ℤ)) :
    D (Sources.M₁ src R) = d + (L+3)/4 ∧
    RestrictionProfile (Sources.A src R)
      src.gamma.law.toFiniteLaw
      (((PositiveRationalLaw.uniform (Fin (q₁ L))).prod μX).toFiniteLaw)
      (x L : ℝ) ((d+(L+3)/4 : ℕ) : ℤ) ∧
    D (Sources.T src R) = d+(L+3)/4+4*L ∧
    RestrictionProfile (Sources.T src R)
      src.inner.law.toFiniteLaw
      (((PositiveRationalLaw.uniform (Fin (q₂ L))).prod
        src.gamma.law).toFiniteLaw)
      (x L : ℝ) ((d+(L+3)/4+4*L : ℕ) : ℤ) ∧
    RestrictionProfile (Sources.Nref src R activity ξ₀)
      (ordinaryLaw src).toFiniteLaw (rowLaw src μI).toFiniteLaw
      (x L : ℝ) ((d+(L+3)/4+4*L+(L+3)/4 : ℕ) : ℤ) := by
  have hρ : (0 : ℝ) < (ρ L : ℝ) := by
    unfold ρ
    have hN := N_pos L
    positivity
  exact Sources.generated_profiles_from_schedule src μI R activity ξ₀
    d ((L+3)/4) (4*L) (ρ L : ℝ) (x L : ℝ) 1
    hd (by omega) (by omega) hρ (x_real_pos L) (x_real_le_one L)
    (by positivity) hD hp (profile_A_width L) (profile_T_width L)
    (profile_A_scale L hL) (profile_T_scale L hL)
    (profile_Nref_scale L hL) (profile_A_budget L hL)
    (profile_T_budget L hL) (profile_Nref_budget L hL)

end CurrentAdditive.DeterministicIndexedMatrix
