import CurrentAdditive.GeneratedWProfileRungV2
import CurrentAdditive.IndexedProfileBudget
import CurrentAdditive.DeterministicParameters

/-! The literal dyadic schedule pays the conditioned-source exception count
at each of the three generated internal profile levels. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open CurrentAdditive.DeterministicParameters

private theorem w_power_relation (L : ℕ) (hL : 2004 ≤ L)
    (j : Fin 3) :
    w L = 2^j.val * 2^(2*L-j.val) := by
  have hj : j.val ≤ 2*L := by omega
  calc
    w L = 2^(2*L) := w_eq_pow L
    _ = 2^((2*L-j.val)+j.val) := by congr 1; omega
    _ = 2^(2*L-j.val) * 2^j.val := by rw [pow_add]
    _ = 2^j.val * 2^(2*L-j.val) := by ac_rfl

private theorem w_exception_count (L : ℕ) (hL : 2004 ≤ L)
    (he : 128 * CurrentAdditive.conditioningExceptionCount
      (θ L : ℝ) 1 ≤ w L) (j : Fin 3) :
    32 * CurrentAdditive.conditioningExceptionCountR 1024 (θ L : ℝ) 1 ≤
      2^(2*L-j.val) := by
  have hc : CurrentAdditive.conditioningExceptionCountR 1024 (θ L : ℝ) 1 =
      CurrentAdditive.conditioningExceptionCount (θ L : ℝ) 1 := rfl
  rw [hc]
  have hp := w_power_relation L hL j
  fin_cases j <;> norm_num at hp ⊢ <;> omega

private theorem w_profile_ratio (L : ℕ) (hL : 2004 ≤ L)
    (hx : (w L : ℝ) * (x L : ℝ) ≤ 1/10000) (j : Fin 3) :
    (9/16 : ℝ) * (2^(2*L-j.val) : ℝ) ≤
      (w L : ℝ) *
        (((3/5 : ℝ) * (1/2 : ℝ)^j.val - (1-127/128)) /
          (127/128) - (2 : ℝ)^(2*L-j.val) * (x L : ℝ)) := by
  let u : ℝ := (2 : ℝ)^(2*L-j.val)
  let p : ℝ := (2 : ℝ)^j.val
  have hu : 0 < u := by dsimp [u]; positivity
  have hwp : (w L : ℝ) = p*u := by
    simpa only [p,u,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using
      congrArg (fun n : ℕ => (n : ℝ)) (w_power_relation L hL j)
  have hsmall : p*u*(x L : ℝ) ≤ 1/10000 := by
    rw [← hwp]
    exact hx
  have hratio : (9/16 : ℝ) ≤
      p * (((3/5 : ℝ) * (1/2 : ℝ)^j.val - (1-127/128)) /
        (127/128)) - p*u*(x L : ℝ) := by
    fin_cases j <;> norm_num [p] at * <;> nlinarith
  change (9/16 : ℝ)*u ≤ (w L : ℝ) *
    (((3/5 : ℝ) * (1/2 : ℝ)^j.val - (1-127/128)) /
      (127/128) - u * (x L : ℝ))
  rw [hwp]
  have hscaled := mul_le_mul_of_nonneg_left hratio hu.le
  nlinarith [hscaled]

theorem generated_W_profile_budget (L : ℕ) (hL : 2004 ≤ L)
    (he : 128 * CurrentAdditive.conditioningExceptionCount
      (θ L : ℝ) 1 ≤ w L)
    (hx : (w L : ℝ) * (x L : ℝ) ≤ 1/10000)
    (j : Fin 3) :
    (((2^((2*L-j.val)-1)+1) +
      CurrentAdditive.conditioningExceptionCountR 1024 (θ L : ℝ) 1 : ℕ) : ℝ) *
      (1 - (2 : ℝ)^(2*L-j.val) * (x L : ℝ)) ≤
    (w L : ℝ) *
      (((3/5 : ℝ) * (1/2 : ℝ)^j.val - (1-127/128)) /
        (127/128) - (2 : ℝ)^(2*L-j.val) * (x L : ℝ)) := by
  apply CurrentAdditive.DeterministicIndexedMatrix.dyadic_budget_of_ratio
    (2*L-j.val)
    (CurrentAdditive.conditioningExceptionCountR 1024 (θ L : ℝ) 1)
    (by omega) (w_exception_count L hL he j)
    ((2 : ℝ)^(2*L-j.val) * (x L : ℝ)) _
    (by have hxpos := x_real_pos L; positivity)
  exact w_profile_ratio L hL hx j

end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.generated_W_profile_budget
