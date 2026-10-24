import CurrentAdditive.QuarticExactFinite

/-! The exact real-logarithmic remainder in the manuscript's rectangular
quartic size display. Its upper bound retains every lower-order entropy term
and the row ceiling. -/

namespace CurrentAdditive.QuarticExactAsymptotics

open Paper2

theorem entries_log_remainder (B k L : ℕ)
    (hB : 1 ≤ B) (hL : 1 ≤ L) :
    let r := 2^(B-1)
    let v := 2^(B+k-1)
    let A := r*r*v
    let Z := compressionEntropy r (B+k)
    let T := Paper2.ReductionDimensions.entries Z L
    let p := 6*B+2*k-5
    let e : ℝ := Real.logb 2 (((L*T : ℕ) : ℝ) / (2^p : ℝ))
    0 ≤ e ∧
    e ≤ Real.logb 2
      (((2*(A+15*r*v)*(A+15*r*v+L) : ℕ) : ℝ) / (2^p : ℝ)) ∧
    Real.logb 2 (T : ℝ) = (p : ℝ) - Real.logb 2 (L : ℝ) + e := by
  dsimp
  let r := 2^(B-1)
  let v := 2^(B+k-1)
  let A := r*r*v
  let Z := compressionEntropy r (B+k)
  let T := Paper2.ReductionDimensions.entries Z L
  let p := 6*B+2*k-5
  let P := 2^p
  have hs := entries_principal_sandwich B k L hL
  have hp := principal_pow_exact B k hB
  change 2*A^2 ≤ L*T ∧ L*T <
    2*(A+15*r*v)*(A+15*r*v+L) at hs
  change 2*A^2 = P at hp
  rw [hp] at hs
  have hP : (0 : ℝ) < (P : ℝ) := by dsimp [P]; positivity
  have hLT : (0 : ℝ) < ((L*T : ℕ) : ℝ) := by
    have hn : 0 < L*T := by
      have hPnat : 0 < P := by dsimp [P]; positivity
      omega
    exact_mod_cast hn
  have hT : (0 : ℝ) < (T : ℝ) := by
    have hn : 0 < T := by
      by_contra hn
      have hzero : T = 0 := by omega
      simp [hzero] at hLT
    exact_mod_cast hn
  have hLreal : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
  let e : ℝ := Real.logb 2 (((L*T : ℕ) : ℝ) / (P : ℝ))
  have hratio : (1 : ℝ) ≤ ((L*T : ℕ) : ℝ) / (P : ℝ) := by
    apply (le_div_iff₀ hP).2
    simpa using (show (P : ℝ) ≤ ((L*T : ℕ) : ℝ) from by exact_mod_cast hs.1)
  have he0 : 0 ≤ e := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hratio
  have hupper : ((L*T : ℕ) : ℝ) / (P : ℝ) ≤
      ((2*(A+15*r*v)*(A+15*r*v+L) : ℕ) : ℝ) / (P : ℝ) := by
    apply (div_le_div_iff_of_pos_right hP).2
    exact_mod_cast hs.2.le
  have heup : e ≤ Real.logb 2
      (((2*(A+15*r*v)*(A+15*r*v+L) : ℕ) : ℝ) / (P : ℝ)) := by
    exact (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2)
      (by positivity) (by positivity)).2 hupper
  have hpLog : Real.logb 2 (P : ℝ) = (p : ℝ) := by
    simp only [P, Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]
  have hmul : Real.logb 2 (((L*T : ℕ) : ℝ)) =
      Real.logb 2 (L : ℝ) + Real.logb 2 (T : ℝ) := by
    push_cast
    exact Real.logb_mul (by positivity) (by positivity)
  have hdiv : e = Real.logb 2 (((L*T : ℕ) : ℝ)) -
      Real.logb 2 (P : ℝ) := by
    dsimp [e]
    exact Real.logb_div (ne_of_gt hLT) (ne_of_gt hP)
  simpa only [e, P, p, T, Z, A, v, r, Nat.cast_pow, Nat.cast_ofNat]
    using (show 0 ≤ e ∧ e ≤ Real.logb 2
      (((2*(A+15*r*v)*(A+15*r*v+L) : ℕ) : ℝ) / (P : ℝ)) ∧
        Real.logb 2 (T : ℝ) = (p : ℝ) - Real.logb 2 (L : ℝ) + e
      from ⟨he0, heup, by linarith⟩)

private theorem relative_numer_bound (r v L : ℕ)
    (hr : 1 ≤ r) (hv : 1 ≤ v) (hLr : L ≤ r) :
    (2 * (r*r*v + 15*r*v) * (r*r*v + 15*r*v + L)) * r ≤
      (2 * (r*r*v)^2) * (r+271) := by
  have hLrv : L ≤ r*v := by nlinarith
  have hb : (r+15)*(r+16) ≤ r*(r+271) := by nlinarith
  have hfirst : r*r*v + 15*r*v = (r*v)*(r+15) := by ring
  have hsecond : r*r*v + 15*r*v + L ≤ (r*v)*(r+16) := by
    rw [hfirst]
    nlinarith
  have hp : 0 < r*v := by positivity
  calc
    (2 * (r*r*v + 15*r*v) * (r*r*v + 15*r*v + L)) * r
        ≤ (2 * ((r*v)*(r+15)) * ((r*v)*(r+16))) * r := by
            rw [hfirst]
            exact Nat.mul_le_mul_right _
              (Nat.mul_le_mul_left _
                (by simpa only [hfirst] using hsecond))
    _ = (2*(r*v)^2) * ((r+15)*(r+16)) * r := by ring
    _ ≤ (2*(r*v)^2) * (r*(r+271)) * r := by
      gcongr
    _ = (2*(r*r*v)^2) * (r+271) := by ring

theorem entries_log_remainder_small (B k L : ℕ)
    (hB : 1 ≤ B) (hL : 1 ≤ L)
    (hLr : L ≤ 2^(B-1)) :
    let r := 2^(B-1)
    let Z := compressionEntropy r (B+k)
    let T := Paper2.ReductionDimensions.entries Z L
    let p := 6*B+2*k-5
    let e : ℝ := Real.logb 2 (((L*T : ℕ) : ℝ) / (2^p : ℝ))
    0 ≤ e ∧ e ≤ Real.logb 2 (1 + 271/(r : ℝ)) ∧
      Real.logb 2 (T : ℝ) = (p : ℝ) - Real.logb 2 (L : ℝ) + e := by
  dsimp
  let r := 2^(B-1)
  let v := 2^(B+k-1)
  let A := r*r*v
  let Z := compressionEntropy r (B+k)
  let T := Paper2.ReductionDimensions.entries Z L
  let p := 6*B+2*k-5
  let P := 2^p
  let U := 2*(A+15*r*v)*(A+15*r*v+L)
  have hmain := entries_log_remainder B k L hB hL
  dsimp at hmain
  have hmain' : 0 ≤ Real.logb 2 (((L*T : ℕ) : ℝ)/(P : ℝ)) ∧
      Real.logb 2 (((L*T : ℕ) : ℝ)/(P : ℝ)) ≤
        Real.logb 2 (((U : ℕ) : ℝ)/(P : ℝ)) ∧
      Real.logb 2 (T : ℝ) = (p : ℝ) - Real.logb 2 (L : ℝ) +
        Real.logb 2 (((L*T : ℕ) : ℝ)/(P : ℝ)) := by
    simpa only [P, p, T, Z, U, A, v, r, Nat.cast_pow, Nat.cast_ofNat]
      using hmain
  have hp := principal_pow_exact B k hB
  change 2*A^2 = P at hp
  have hr : 1 ≤ r := by
    have hh : 0 < r := by dsimp [r]; positivity
    omega
  have hv : 1 ≤ v := by
    have hh : 0 < v := by dsimp [v]; positivity
    omega
  have hnum := relative_numer_bound r v L hr hv hLr
  change U*r ≤ (2*A^2)*(r+271) at hnum
  rw [hp] at hnum
  have hPr : (0:ℝ) < (P:ℝ) := by dsimp [P]; positivity
  have hrr : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr
  have hnumR : (U:ℝ)*(r:ℝ) ≤ (P:ℝ)*((r+271:ℕ):ℝ) := by
    exact_mod_cast hnum
  have hratio : (U:ℝ)/(P:ℝ) ≤ ((r+271:ℕ):ℝ)/(r:ℝ) := by
    apply (div_le_div_iff₀ hPr hrr).2
    nlinarith [hnumR]
  have hratio' : (U:ℝ)/(P:ℝ) ≤ 1 + 271/(r:ℝ) := by
    convert hratio using 1
    push_cast
    field_simp
  have hUpos : (0:ℝ) < (U:ℝ)/(P:ℝ) := by
    have hA : 0 < A := by dsimp [A]; positivity
    dsimp [U]
    positivity
  have hsimple := (Real.logb_le_logb
    (by norm_num : (1:ℝ) < 2) hUpos (by positivity)).2 hratio'
  simpa only [P, p, T, Z, r, Nat.cast_pow, Nat.cast_ofNat] using
    (show 0 ≤ Real.logb 2 (((L*T : ℕ) : ℝ)/(P : ℝ)) ∧
        Real.logb 2 (((L*T : ℕ) : ℝ)/(P : ℝ)) ≤
          Real.logb 2 (1 + 271/(r:ℝ)) ∧
        Real.logb 2 (T:ℝ) = (p:ℝ) - Real.logb 2 (L:ℝ) +
          Real.logb 2 (((L*T : ℕ) : ℝ)/(P : ℝ))
      from ⟨hmain'.1, hmain'.2.1.trans hsimple, hmain'.2.2⟩)

end CurrentAdditive.QuarticExactAsymptotics
