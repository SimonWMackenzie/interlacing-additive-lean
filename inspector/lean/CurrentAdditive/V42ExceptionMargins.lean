import CurrentAdditive.V42CommonMargins

namespace CurrentAdditive.V42Schedule

set_option maxRecDepth 10000

open V39ExceptionBudget

def ownerBudget (k : ℕ) : ℕ :=
  V38Schedule.ebar (9+24*k) (eta k/2)
def EexcBudget (k : ℕ) : ℕ := 2*ownerBudget k

theorem cast_rho_dyadic (b : ℕ) : (rho b : ℝ)=dyadic b := by
  unfold rho dyadic
  rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast]
  push_cast
  simp [one_div]

theorem ownerBudget_exact (k : ℕ) :
    ownerBudget k=2^(92+4*k+(72+24*k)/64) := by
  have hη : eta k/2=(1:ℚ)/2^(2*k+1) := by
    unfold eta
    rw [pow_succ]
    ring
  unfold ownerBudget
  rw [hη,ebar_dyadic]
  congr 1
  omega

theorem EexcBudget_exact (k : ℕ) :
    EexcBudget k=2^(93+4*k+(72+24*k)/64) := by
  unfold EexcBudget
  rw [ownerBudget_exact,show 93+4*k+(72+24*k)/64=(92+4*k+(72+24*k)/64)+1 by omega,pow_succ]
  omega

theorem theta_real (k : ℕ) : (theta k : ℝ)=dyadic (9+24*k) :=
  cast_rho_dyadic (9+24*k)

theorem theta_quarter_real (k : ℕ) : (theta k : ℝ)/4=dyadic (11+24*k) := by
  have he : theta k/4=rho (11+24*k) := by
    unfold theta rho
    rw [show 11+24*k=(9+24*k)+2 by omega,pow_add]
    norm_num
    ring
  have hh := congrArg (fun q:ℚ => (q:ℝ)) he
  push_cast at hh
  rw [hh]
  exact cast_rho_dyadic _

theorem owner_count_bound (k : ℕ) :
    V38Moments.exceptionCount (theta k:ℝ) ((eta k:ℝ)/2) ≤ ownerBudget k := by
  rw [theta_real]
  have hη : 0 < eta k/2 := by unfold eta; positivity
  have hη1 : eta k/2 ≤ 1 := by
    have hp : (1:ℚ) ≤ 2^(2*k) := one_le_pow₀ (by norm_num)
    unfold eta
    have hh : (1:ℚ)/2^(2*k) ≤ 1 := (div_le_one (by positivity)).2 hp
    linarith
  have hh := V39GeneralExceptionBudget.exception_le_ebar (9+24*k) (eta k/2) hη hη1
  simpa only [Rat.cast_div,Rat.cast_ofNat,ownerBudget] using hh

theorem unit_count_bound (k : ℕ) :
    V38Moments.exceptionCount (theta k:ℝ) 1 ≤ 2^(90+(72+24*k)/64) := by
  rw [theta_real]
  have hh := V39ExceptionBudget.exception_le_ebar (9+24*k)
  rw [V38Cutoff.ebar_unit,←pow_add] at hh
  convert hh using 1 <;> congr 1 <;> omega

theorem quarter_count_bound (k : ℕ) :
    V38Moments.exceptionCount ((theta k:ℝ)/4) 1 ≤ 2^(90+(74+24*k)/64) := by
  rw [theta_quarter_real]
  have hh := V39ExceptionBudget.exception_le_ebar (11+24*k)
  rw [V38Cutoff.ebar_unit,←pow_add] at hh
  convert hh using 1 <;> congr 1 <;> omega

theorem exception_common (k b : ℕ) (hk : 200 ≤ k) (hb : 4*k ≤ b) :
    V38Moments.exceptionCount ((theta k:ℝ)/4) 1 ≤ s k*q₂ k b ∧
    128*V38Moments.exceptionCount (theta k:ℝ) 1 ≤ w k ∧
    (32*(s k:ℚ))*(EexcBudget k:ℚ) ≤ eta k*w k := by
  have ht : 98+(72+24*k)/64 ≤ k := by omega
  refine ⟨?_,?_,?_⟩
  · calc
      V38Moments.exceptionCount ((theta k:ℝ)/4) 1 ≤ 2^(90+(74+24*k)/64) := quarter_count_bound k
      _ ≤ 2^(b+3*k) := Nat.pow_le_pow_right (by decide) (by omega)
      _ = s k*q₂ k b := by unfold s q₂; rw [←pow_add]; congr 1; omega
  · have hh := Nat.mul_le_mul_left 128 (unit_count_bound k)
    calc
      128*V38Moments.exceptionCount (theta k:ℝ) 1 ≤ 128*2^(90+(72+24*k)/64) := hh
      _ = 2^(97+(72+24*k)/64) := by
        change (2:ℕ)^7*2^(90+(72+24*k)/64)=_
        rw [←pow_add]; congr 1; omega
      _ ≤ w k := Nat.pow_le_pow_right (by decide) (by omega)
  · have he : (32*(s k:ℚ))*(EexcBudget k:ℚ)=2^(98+5*k+(72+24*k)/64) := by
      rw [EexcBudget_exact]
      simp only [s,Nat.cast_pow,Nat.cast_ofNat]
      rw [show 98+5*k+(72+24*k)/64=5+k+(93+4*k+(72+24*k)/64) by omega,pow_add,pow_add]
      norm_num
      ring
    have he2 : eta k*(w k:ℚ)=2^(6*k) := by
      simp only [eta,w,Nat.cast_pow,Nat.cast_ofNat]
      rw [show 8*k=6*k+2*k by omega,pow_add]
      field_simp
    rw [he,he2]
    exact_mod_cast Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 98+5*k+(72+24*k)/64 ≤ 6*k by omega)

theorem flag_margin (k : ℕ) (hk : 22 ≤ k) :
    V38Schedule.C128/(s k:ℚ)^128 ≤ theta k/4 := by
  have hbase : (2^14:ℚ)/((255/256:ℚ)-1/2)^2 ≤ 2^17 := by norm_num
  have hC : V38Schedule.C128 ≤ (2:ℚ)^2176 := by
    unfold V38Schedule.C128
    have hh := pow_le_pow_left₀ (by positivity : (0:ℚ) ≤ (2^14:ℚ)/((255/256:ℚ)-1/2)^2) hbase 128
    rw [←pow_mul] at hh
    change V38Schedule.C128 ≤ (2:ℚ)^(17*128)
    exact hh
  have hden : (s k:ℚ)^128=2^(128*k) := by
    simp only [s,Nat.cast_pow,Nat.cast_ofNat,←pow_mul]
    congr 1; omega
  have htheta : theta k/4=(1:ℚ)/2^(11+24*k) := by
    unfold theta
    rw [show 11+24*k=(9+24*k)+2 by omega,pow_add]
    norm_num
    ring
  rw [hden,htheta]
  exact (div_le_div_of_nonneg_right hC (by positivity)).trans
    (by simpa using ratio_le 2176 (128*k) 0 (11+24*k) (by omega))

theorem generated_tuple_count (k : ℕ) (hk : 200 ≤ k) :
    128*V38Moments.exceptionCount (x (4*k):ℝ) 1 ≤ s k := by
  have he : (x (4*k):ℝ)=dyadic (32*k) := by
    change (rho (8*(4*k)):ℝ)=_
    rw [cast_rho_dyadic]
    congr 1; omega
  rw [he]
  have hh := V39ExceptionBudget.exception_le_ebar (32*k)
  rw [V38Cutoff.ebar_unit,←pow_add] at hh
  calc
    128*V38Moments.exceptionCount (dyadic (32*k)) 1 ≤ 128*2^(90+(32*k+63)/64) := Nat.mul_le_mul_left _ hh
    _ = 2^(97+(32*k+63)/64) := by
      change (2:ℕ)^7*2^(90+(32*k+63)/64)=_
      rw [←pow_add]; congr 1; omega
    _ ≤ s k := Nat.pow_le_pow_right (by decide) (by omega)

theorem generated_restoration_count (k : ℕ) (hk : 200 ≤ k) :
    128*(V38Moments.exceptionCount (rho (4*k):ℝ) ((deltaU k:ℝ)/2)+1) ≤ Q k := by
  have hτ : deltaU k/2=(1:ℚ)/2^(5+10*k) := by
    unfold deltaU
    rw [show 5+10*k=(4+10*k)+1 by omega,pow_succ]
    ring
  have hh := V39GeneralExceptionBudget.exception_le_ebar (4*k) (deltaU k/2)
    (by unfold deltaU; positivity) (by
      have hpow : (1:ℚ) ≤ 2^(4+10*k) := one_le_pow₀ (by norm_num)
      have h := (div_le_one (by positivity : (0:ℚ) < 2^(4+10*k))).2 hpow
      change ((1:ℚ)/2^(4+10*k))/2 ≤ 1
      linarith)
  rw [hτ,ebar_dyadic] at hh
  have hcast : ((deltaU k/2:ℚ):ℝ)=(deltaU k:ℝ)/2 := by push_cast; rfl
  rw [←hτ,hcast,←cast_rho_dyadic] at hh
  have he : 90+2*(5+10*k)+(4*k+63)/64=100+20*k+(4*k+63)/64 := by omega
  rw [he] at hh
  have hpos : 1 ≤ (2:ℕ)^(100+20*k+(4*k+63)/64) := Nat.one_le_pow _ _ (by decide)
  calc
    128*(V38Moments.exceptionCount (rho (4*k):ℝ) ((deltaU k:ℝ)/2)+1) ≤
        256*2^(100+20*k+(4*k+63)/64) := by omega
    _ = 2^(108+20*k+(4*k+63)/64) := by
      change (2:ℕ)^8*2^(100+20*k+(4*k+63)/64)=_
      rw [←pow_add]; congr 1; omega
    _ ≤ Q k := Nat.pow_le_pow_right (by decide) (by omega)

end CurrentAdditive.V42Schedule
