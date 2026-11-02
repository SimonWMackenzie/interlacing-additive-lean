import CurrentAdditive.V38Cutoff
import CurrentAdditive.V39SourceConstant

namespace V39FullCutoff
open V38Schedule V38Cutoff

def inverseExponent (c : ℚ) : ℕ := Nat.ceil (1 / c)
def ownerCoefficient (c : ℚ) : ℕ := Nat.ceil ((2 ^ 124 : ℚ) / c ^ 2)
def ellCutoff (c : ℚ) : ℕ := inverseExponent c + ownerCoefficient c + 300
def exponentCutoff (c : ℚ) (Δ : ℕ) : ℕ := max Δ (2 ^ ellCutoff c)

theorem two_ratio_le (a b d e : ℕ) (h : a + e ≤ d + b) :
    (2 : ℚ)^a / 2^b ≤ 2^d / 2^e := by
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  rw [← pow_add, ← pow_add]
  exact_mod_cast Nat.pow_le_pow_right (by decide : 1 ≤ 2) h

theorem inverse_bound (c : ℚ) (hc : 0 < c) :
    1 / (2 : ℚ)^inverseExponent c ≤ c := by
  have hceil : 1 / c ≤ (inverseExponent c : ℚ) := Nat.le_ceil _
  have hp : (inverseExponent c : ℚ) ≤ 2^inverseExponent c := by
    exact_mod_cast coefficient_le_power (inverseExponent c)
  apply (div_le_iff₀ (by positivity)).2
  have h := (div_le_iff₀ hc).1 (hceil.trans hp)
  nlinarith

theorem linear_le_exp (k : ℕ) (hk : 16 ≤ k) :
    512 * k ≤ 2 ^ (k - 1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction j with
  | zero => norm_num
  | succ j ih =>
      have hexp : 16 + (j + 1) - 1 = (16 + j - 1) + 1 := by omega
      rw [hexp, pow_succ]
      have hlow : 512 ≤ 512 * (16 + j) := by omega
      omega

theorem cutoff_bounds (c : ℚ) (Δ L : ℕ) (hL : exponentCutoff c Δ ≤ L) :
    ellCutoff c ≤ ell L ∧ 512 * ell L ≤ L ∧ Δ ≤ L := by
  have hpow : 2 ^ ellCutoff c ≤ L := (le_max_right _ _).trans hL
  have he : ellCutoff c < ell L := by
    apply (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).2
    exact lt_of_le_of_lt hpow (by omega)
  have hk : 16 ≤ ell L := by
    have : 300 ≤ ellCutoff c := by unfold ellCutoff; omega
    omega
  have hlower : 2 ^ (ell L - 1) ≤ L := by
    have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) (show 1 < L+1 by
      have hp : 0 < 2 ^ ellCutoff c := by positivity
      omega)
    change 2 ^ (ell L - 1) < L + 1 at hp
    omega
  exact ⟨by omega, (linear_le_exp _ hk).trans hlower, (le_max_left _ _).trans hL⟩

theorem fullS_rat (L : ℕ) : (fullS L : ℚ) = 2^(16+ell L) := by simp [fullS]
theorem fullW_rat (L : ℕ) : (fullW L : ℚ) = 2^(8*ell L) := by simp [fullW]
theorem fullQ2_rat (L : ℕ) : (fullQ₂ L : ℚ) = 2^(L+32+2*ell L) := by
  simp only [fullQ₂, fullS, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [← pow_mul, ← pow_add]
  congr 1
  omega
theorem fullEta_rat (c : ℚ) (L : ℕ) : fullEta c L = c / 2^(32+ell L) := by
  simp only [fullEta, fullS_rat, ← pow_add]
  congr 2
  omega

theorem full_eta_lower (c0 c : ℚ) (L : ℕ) (h0 : 0 < c0) (hc : c0 ≤ c) :
    1 / (2 : ℚ)^(inverseExponent c0 + 32 + ell L) ≤ fullEta c L := by
  rw [fullEta_rat, pow_add, pow_add]
  have hi := (inverse_bound c0 h0).trans hc
  have h := div_le_div_of_nonneg_right hi (by positivity : (0:ℚ) ≤ 2^32*2^ell L)
  convert h using 1 <;> field_simp <;> ring

theorem full_owner_bound (c0 c : ℚ) (L : ℕ) (h0 : 0 < c0) (hc : c0 ≤ c) :
    Eexc (fullQlog L) (fullEta c L) ≤
      2^(33 + ownerCoefficient c0 + 2*ell L + (72+16*ell L)/64) := by
  let k := ell L
  let t := (72+16*k)/64
  let K := ownerCoefficient c0
  have hcpos : 0 < c := h0.trans_le hc
  have hspos : (0:ℚ) < fullS L := by rw [fullS_rat]; positivity
  have hK : (2^124:ℚ)/c0^2 ≤ K := Nat.le_ceil _
  have hsq : c0^2 ≤ c^2 := by nlinarith
  have hcoef : (2^124:ℚ)/c^2 ≤ K := by
    exact (div_le_div_of_nonneg_left (by positivity) (by positivity) hsq).trans hK
  have harg : fullEta c L / 2 = c / (2^17 * fullS L) := by unfold fullEta; ring
  have heq : (2^90:ℚ) / (c / (2^17 * fullS L))^2 =
      (2^124:ℚ)/c^2 * (fullS L : ℚ)^2 := by field_simp
  have heb : ebar (9+fullQlog L) (fullEta c L / 2) ≤ K * fullS L^2 * 2^t := by
    rw [harg]
    unfold ebar
    apply (Nat.ceil_le).2
    rw [heq]
    have hh := mul_le_mul_of_nonneg_right hcoef (show (0:ℚ) ≤ (fullS L : ℚ)^2 * 2^t by positivity)
    convert hh using 1 <;> simp only [fullQlog, t, k] <;> push_cast <;> ring
  have hKpow := coefficient_le_power K
  unfold Eexc e0
  calc
    2 * ebar (9+fullQlog L) (fullEta c L / 2) ≤ 2 * (K * fullS L^2 * 2^t) := Nat.mul_le_mul_left _ heb
    _ ≤ 2 * (2^K * fullS L^2 * 2^t) := by gcongr
    _ = 2^(33+K+2*k+t) := by
      simp only [fullS, k]
      rw [← pow_mul]
      have hx : (16+ell L)*2 = 32+2*ell L := by omega
      rw [hx, pow_add, pow_add, pow_add, pow_add]
      norm_num
      ring

theorem full_smallness (c0 c : ℚ) (L : ℕ)
    (h0 : 0 < c0) (hc : c0 ≤ c)
    (hk : inverseExponent c0 + 300 ≤ ell L) (hL : 512*ell L ≤ L) :
    4*(fullS L : ℚ)^2*fullRho L ≤ 1 ∧
    (fullQ₂ L : ℚ)*fullX L ≤ 1/10000 ∧
    (fullS L : ℚ)*fullX L ≤ 1/10000 ∧
    (fullW L : ℚ)*fullX L ≤ 1/10000 ∧
    2*(fullW L : ℚ)^2*fullX L ≤ fullEta c L/(16*(255/256:ℚ)) ∧
    (fullW L : ℚ)^2*fullQ₂ L*fullX L ≤ 1 ∧
    4*(1/256:ℚ)*fullW L*fullQ₂ L*fullX L ≤ fullEta c L/32 := by
  let k := ell L
  let A := inverseExponent c0
  have hk0 : 300 ≤ k := by dsimp [k, A] at *; omega
  have he1 : 34+2*k ≤ L := by omega
  have he2 : L+32+2*k+14 ≤ 10*L := by omega
  have he3 : 16+k+14 ≤ 10*L := by omega
  have he4 : 8*k+14 ≤ 10*L := by omega
  have he5 : 1+16*k+(A+32+k+4) ≤ 10*L := by dsimp [A,k] at *; omega
  have he6 : L+32+18*k ≤ 10*L := by omega
  have he7 : L+26+10*k+(A+37+k) ≤ 10*L := by dsimp [A,k] at *; omega
  have h1 := two_ratio_le (34+2*k) L 0 0 (by omega)
  have h2 := two_ratio_le (L+32+2*k) (10*L) 0 14 (by omega)
  have h3 := two_ratio_le (16+k) (10*L) 0 14 (by omega)
  have h4 := two_ratio_le (8*k) (10*L) 0 14 (by omega)
  have h5 := two_ratio_le (1+16*k) (10*L) 0 (A+32+k+4) (by omega)
  have h6 := two_ratio_le (L+32+18*k) (10*L) 0 0 (by omega)
  have h7 := two_ratio_le (L+26+10*k) (10*L) 0 (A+37+k) (by omega)
  have heta := full_eta_lower c0 c L h0 hc
  have hrat : (1:ℚ)/2^14 ≤ 1/10000 := by norm_num
  have eq1 : 4*(fullS L : ℚ)^2*fullRho L = 2^(34+2*k)/2^L := by
    rw [fullS_rat, ← pow_mul]
    have he : (16+ell L)*2 = 32+2*k := by omega
    rw [he]
    simp only [fullRho,pow_add]
    norm_num
    ring
  have eq2 : (fullQ₂ L : ℚ)*fullX L = 2^(L+32+2*k)/2^(10*L) := by
    rw [fullQ2_rat]; simp [fullX,k]; ring
  have eq3 : (fullS L : ℚ)*fullX L = 2^(16+k)/2^(10*L) := by
    rw [fullS_rat]; simp [fullX,k]; ring
  have eq4 : (fullW L : ℚ)*fullX L = 2^(8*k)/2^(10*L) := by
    rw [fullW_rat]; simp [fullX,k]; ring
  have eq5 : 2*(fullW L : ℚ)^2*fullX L = 2^(1+16*k)/2^(10*L) := by
    rw [fullW_rat, ← pow_mul]
    have he : (8*ell L)*2 = 16*k := by omega
    rw [he]
    simp only [fullX,pow_add,pow_one]
    ring
  have eq6 : (fullW L : ℚ)^2*fullQ₂ L*fullX L = 2^(L+32+18*k)/2^(10*L) := by
    rw [fullW_rat,fullQ2_rat, ← pow_mul]
    have he : L+32+18*k = (8*ell L)*2+(L+32+2*ell L) := by omega
    rw [he,pow_add]
    unfold fullX
    ring
  have eq7 : 4*(1/256:ℚ)*fullW L*fullQ₂ L*fullX L =
      2^(L+26+10*k)/2^(10*L) := by
    rw [fullW_rat,fullQ2_rat]
    have he : L+26+10*k+6 = 8*ell L+(L+32+2*ell L) := by omega
    have hh : (2:ℚ)^(L+26+10*k) * 2^6 = 2^(8*ell L) * 2^(L+32+2*ell L) := by
      rw [← pow_add,he,pow_add]
    norm_num at hh
    unfold fullX
    linear_combination hh / (64 * (2:ℚ)^(10*L))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eq1]; simpa using h1
  · rw [eq2]; exact h2.trans hrat
  · rw [eq3]; exact h3.trans hrat
  · rw [eq4]; exact h4.trans hrat
  · rw [eq5]
    have heq : (1:ℚ)/2^(A+32+k+4) = (1/2^(A+32+k))/16 := by rw [pow_add]; norm_num; ring
    rw [pow_zero,heq] at h5
    have hh : (1:ℚ)/2^(A+32+k)/16 ≤ fullEta c L/16 :=
      div_le_div_of_nonneg_right heta (by norm_num)
    have hcpos : 0 < c := h0.trans_le hc
    have hη : 0 ≤ fullEta c L := by rw [fullEta_rat]; positivity
    exact h5.trans (hh.trans (div_le_div_of_nonneg_left hη (by norm_num) (by norm_num)))
  · rw [eq6]; simpa using h6
  · rw [eq7]
    have heq : (1:ℚ)/2^(A+37+k) = (1/2^(A+32+k))/32 := by
      have he : A+37+k = A+32+k+5 := by omega
      rw [he,pow_add]; norm_num; ring
    rw [pow_zero,heq] at h7
    exact h7.trans (div_le_div_of_nonneg_right heta (by norm_num))

theorem full_owner_tests (c0 c : ℚ) (L : ℕ)
    (h0 : 0 < c0) (hc : c0 ≤ c)
    (hk : inverseExponent c0 + ownerCoefficient c0 + 300 ≤ ell L) :
    Eexc (fullQlog L) (fullEta c L) ≤ fullW L / 4 ∧
    (Kstar (8*ell L) (fullS L) : ℚ) * Eexc (fullQlog L) (fullEta c L) ≤
      fullEta c L * fullW L / 16 := by
  let k := ell L
  let A := inverseExponent c0
  let K := ownerCoefficient c0
  let t := (72+16*k)/64
  have hk16 : 16 ≤ k := by dsimp [k] at *; omega
  have he := full_owner_bound c0 c L h0 hc
  change Eexc (fullQlog L) (fullEta c L) ≤ 2^(33+K+2*k+t) at he
  have heexp : 35+K+2*k+t ≤ 8*k := by dsimp [A,K,t,k] at *; omega
  have hequarter : 4 * Eexc (fullQlog L) (fullEta c L) ≤ fullW L := by
    calc
      4 * Eexc (fullQlog L) (fullEta c L) ≤ 4 * 2^(33+K+2*k+t) := Nat.mul_le_mul_left 4 he
      _ = 2^(35+K+2*k+t) := by
        have hh : 35+K+2*k+t=2+(33+K+2*k+t) := by omega
        rw [hh]
        simp only [pow_add]
        norm_num
      _ ≤ fullW L := Nat.pow_le_pow_right (by decide) heexp
  have hlin : 8*k+2 ≤ 2^k := by
    have hp := linear_le_exp k hk16
    have he : k-1 ≤ k := by omega
    have hmono := Nat.pow_le_pow_right (by decide : 1≤2) he
    omega
  have hkstar : Kstar (8*ell L) (fullS L) ≤ 2^(17+2*k) := by
    unfold Kstar
    calc
      2*(8*ell L+2)*fullS L ≤ 2*2^k*fullS L := by gcongr
      _ = 2^(17+2*k) := by
        unfold fullS
        have hh : 17+2*k=1+k+(16+ell L) := by omega
        rw [hh]
        simp only [pow_add,pow_one]
  have hprod : (Kstar (8*ell L) (fullS L) : ℚ)*Eexc (fullQlog L) (fullEta c L) ≤
      2^(50+K+4*k+t) := by
    have hmul := Nat.mul_le_mul hkstar he
    have heq : 17+2*k+(33+K+2*k+t)=50+K+4*k+t := by omega
    rw [← pow_add,heq] at hmul
    exact_mod_cast hmul
  have hexp : 50+K+4*k+t+(A+36+k) ≤ 8*k+0 := by dsimp [A,K,t,k] at *; omega
  have hr := two_ratio_le (50+K+4*k+t) 0 (8*k) (A+36+k) hexp
  have heta := full_eta_lower c0 c L h0 hc
  have hmul := mul_le_mul_of_nonneg_right heta (show (0:ℚ) ≤ fullW L/16 by positivity)
  have heq : (1:ℚ)/2^(A+32+k)*(fullW L/16) = 2^(8*k)/2^(A+36+k) := by
    rw [fullW_rat]
    have hh : A+36+k=A+32+k+4 := by omega
    rw [hh,pow_add]
    norm_num
    ring
  rw [heq] at hmul
  refine ⟨by omega, ?_⟩
  apply hprod.trans
  have hr' : (2:ℚ)^(50+K+4*k+t) ≤ 2^(8*k)/2^(A+36+k) := by simpa using hr
  apply hr'.trans
  convert hmul using 1 <;> ring

theorem full_flag_test (L : ℕ) (hk : 2 ≤ ell L) :
    C128/(fullS L : ℚ)^128 ≤ theta (fullQ L)/4 := by
  have hbase : (2^14:ℚ)/((255/256:ℚ)-1/2)^2 ≤ 2^17 := by norm_num
  have hC : C128 ≤ (2:ℚ)^2176 := by
    unfold C128
    have h := pow_le_pow_left₀ (by positivity : (0:ℚ) ≤ (2^14:ℚ)/((255/256:ℚ)-1/2)^2) hbase 128
    rw [← pow_mul] at h
    exact h
  have hden : (fullS L : ℚ)^128 = 2^(2048+128*ell L) := by
    rw [fullS_rat,←pow_mul]
    rw [show (16+ell L)*128=2048+128*ell L by omega]
  rw [hden,full_theta_quarter_exact,fullQlog]
  have hrat := two_ratio_le 2176 (2048+128*ell L) 0 (11+16*ell L) (by omega)
  have h := div_le_div_of_nonneg_right hC (by positivity : (0:ℚ) ≤ 2^(2048+128*ell L))
  exact h.trans (by simpa using hrat)

theorem full_restoration_test (c0 c : ℚ) (L : ℕ)
    (h0 : 0 < c0) (hc : c0 ≤ c) (hk : inverseExponent c0+300 ≤ ell L) :
    (fullQ L : ℚ)*deltaU (fullEta c L) (fullW L) ≥ 80*L := by
  let k := ell L
  let A := inverseExponent c0
  have hL : L ≤ 2^k := by
    have h := Nat.le_pow_clog (by decide : 1<2) (L+1)
    dsimp [k,ell]
    omega
  have hrat := two_ratio_le (k+7) 0 (8*k) (A+36+k) (by dsimp [k,A] at *; omega)
  have h80 : (80:ℚ)*L ≤ 2^(k+7) := by
    have hLQ : (L:ℚ) ≤ 2^k := by exact_mod_cast hL
    rw [pow_add]
    norm_num
    nlinarith
  have heta := full_eta_lower c0 c L h0 hc
  have hmul := mul_le_mul_of_nonneg_right heta (show (0:ℚ) ≤ fullW L/16 by positivity)
  have heq : (1:ℚ)/2^(A+32+k)*(fullW L/16) = 2^(8*k)/2^(A+36+k) := by
    rw [fullW_rat]
    have hh : A+36+k=A+32+k+4 := by omega
    rw [hh,pow_add]
    norm_num
    ring
  rw [heq] at hmul
  have hpos : (fullW L : ℚ) ≠ 0 := by unfold fullW; positivity
  have hfinal : (fullQ L:ℚ)*deltaU (fullEta c L) (fullW L) = fullEta c L*fullW L/16 := by
    simp only [fullQ,Nat.cast_pow,deltaU]
    field_simp
  rw [hfinal]
  have hrat' : (2:ℚ)^(k+7) ≤ 2^(8*k)/2^(A+36+k) := by simpa using hrat
  apply h80.trans (hrat'.trans ?_)
  convert hmul using 1 <;> ring

theorem full_collision_budget (c0 ζ : ℚ) (L : ℕ)
    (h0 : 0 < c0) (hζ : c0 ≤ ζ) (hL : inverseExponent c0+7 ≤ L) :
    8*(fullS L : ℚ)*fullQ₁ L ≤ ζ*fullQ₂ L/16 := by
  have hζpos : 0 < ζ := h0.trans_le hζ
  have hinv := (inverse_bound c0 h0).trans hζ
  have hrat := two_ratio_le 7 0 L (inverseExponent c0) (by omega)
  have hmul := mul_le_mul_of_nonneg_right hinv (show (0:ℚ) ≤ 2^L by positivity)
  have h128 : (128:ℚ) ≤ ζ*2^L := by
    norm_num at hrat
    calc
      (128:ℚ) ≤ 2^L/2^inverseExponent c0 := hrat
      _ = (1/2^inverseExponent c0)*2^L := by ring
      _ ≤ ζ*2^L := hmul
  have hq1 : (fullQ₁ L : ℚ) ≤ fullS L := by
    exact_mod_cast (show fullQ₁ L ≤ fullS L by unfold fullQ₁; omega)
  have hs : (0:ℚ) ≤ fullS L := by positivity
  have hh : 8*(fullS L:ℚ)*fullQ₁ L ≤ 8*(fullS L:ℚ)^2 := by nlinarith
  apply hh.trans
  simp only [fullQ₂,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  have := mul_le_mul_of_nonneg_right h128 (sq_nonneg (fullS L:ℚ))
  nlinarith

/-- A single effective cutoff works for every coefficient in the indicated
interval and every graph satisfying the same fixed degree bound. -/
theorem fullTests_all_large (c0 c δv ζ : ℚ) (Δ L n m : ℕ)
    (h0 : 0 < c0) (hc : c0 ≤ c)
    (hcup : c ≤ min 1 (min δv (ζ/256))) (hζ : c0 ≤ ζ)
    (hn : n ≤ 2^L) (hdeg : 2*m ≤ Δ*n)
    (hL : exponentCutoff c0 Δ ≤ L) : FullTests c L m δv ζ := by
  obtain ⟨hk,hlinear,hΔ⟩ := cutoff_bounds c0 Δ L hL
  have hk0 : inverseExponent c0+300 ≤ ell L := by unfold ellCutoff at hk; omega
  have hk16 : 16 ≤ ell L := by omega
  have hL100 : 100 ≤ L := by omega
  obtain ⟨h1,h2,h3,h4,h5,h6,h7⟩ := full_smallness c0 c L h0 hc hk0 hlinear
  obtain ⟨ho,hi⟩ := full_owner_tests c0 c L h0 hc hk
  have hsource := full_source_width_from_cutoff L n m Δ hn hdeg hΔ
  have hcollision := full_collision_budget c0 ζ L h0 hζ (by omega)
  have hebar := full_theta_ebar_budget L hk16
  have hebar2 := full_theta_quarter_ebar_budget L hL100 hk16
  have hflag := full_flag_test L (by omega)
  have hsourceEta : (fullS L:ℚ)*fullEta c L ≤ min 1 (min δv (ζ/256))/2^16 := by
    rw [full_eta_scaled]
    exact div_le_div_of_nonneg_right hcup (by positivity)
  refine ⟨?_, full_restoration_test c0 c L h0 hc hk0, by omega, by omega, by omega⟩
  unfold CommonTests fullInput
  dsimp only
  exact ⟨fullS_ge_256 L,hsourceEta,hsource,h1,hcollision,h2,h3,h4,h5,h6,h7,
    by omega,hebar2,hflag,ho,hi⟩

/-- Source-size cutoff, depending only on the fixed promise constants. -/
def sourceCutoff (γ : ℚ) (Δ : ℕ) : ℕ :=
  2 ^ exponentCutoff (V39PublicSchedule.publicConstantFloor γ Δ) Δ

theorem fullPublicTests_all_large (γ : ℚ) (Δ n m : ℕ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hn : 0 < n)
    (hnm : n ≤ 2*m) (hdeg : 2*m ≤ Δ*n)
    (hlarge : sourceCutoff γ Δ ≤ n) :
    FullPublicTests γ Δ n m (Nat.clog 2 n) := by
  obtain ⟨h0,hc,hcup,hζpos,hζ⟩ :=
    V39PublicSchedule.fullConstant_interval γ Δ n m hγ hΔ hn hnm
  have hnPow : n ≤ 2^Nat.clog 2 n := Nat.le_pow_clog (by decide) n
  have hL : exponentCutoff (V39PublicSchedule.publicConstantFloor γ Δ) Δ ≤ Nat.clog 2 n := by
    have hp : 2 ^ exponentCutoff (V39PublicSchedule.publicConstantFloor γ Δ) Δ ≤
        2^Nat.clog 2 n := hlarge.trans hnPow
    exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).1 hp
  unfold FullPublicTests
  exact fullTests_all_large _ _ _ _ Δ (Nat.clog 2 n) n m h0 hc hcup hζ hnPow hdeg hL

theorem fullPublicPass_all_large (γ : ℚ) (Δ n m : ℕ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hn : 0 < n)
    (hnm : n ≤ 2*m) (hdeg : 2*m ≤ Δ*n)
    (hlarge : sourceCutoff γ Δ ≤ n) :
    fullPublicPass γ Δ n m (Nat.clog 2 n) = true :=
  (fullPublicPass_iff ..).2 (fullPublicTests_all_large γ Δ n m hγ hΔ hn hnm hdeg hlarge)

#print axioms fullTests_all_large
#print axioms fullPublicTests_all_large
#print axioms fullPublicPass_all_large

end V39FullCutoff
