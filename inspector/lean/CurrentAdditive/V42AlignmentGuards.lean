import CurrentAdditive.V42ExceptionMargins
import CurrentAdditive.V42IncomingGuard

/-! Direct numeric inputs for the actual indexed v42 alignment theorem.
The hypotheses are the two recipe exponent comparisons, and contain no
profile, protocol conclusion, matrix or current constraint record. -/

namespace CurrentAdditive.V42AlignmentGuards

open V42Schedule

abbrev X (b : ℕ) : ℝ := (x b:ℚ)
abbrev Eta (k : ℕ) : ℝ := (eta k:ℚ)
abbrev Theta (k : ℕ) : ℝ := (theta k:ℚ)

structure Guards (k b : ℕ) : Prop where
  r_ge : 2 ≤ 8*k
  w_pow : w k=2^(8*k)
  q_pow : q₂ k b=2^(b+2*k)
  s_pow : s k=2^k
  x_pos : 0 < X b
  theta_pos : 0 < Theta k
  eta_pos : 0 < Eta k
  eta_le_one : Eta k ≤ 1
  cap : V38Moments.exceptionCount (Theta k) (Eta k/2) ≤ ownerBudget k
  exc : 4*(2*ownerBudget k) ≤ w k
  receipt : (2*(s k:ℝ))*(2*ownerBudget k) ≤ Eta k*w k/16
  init : 2*(w k:ℝ)*X b+Eta k/(16*(255/256:ℝ)) ≤ 1
  wx : (w k:ℝ)*X b ≤ 1
  two_x : 2*X b ≤ 1
  loss : 2*(w k:ℝ)^2*X b ≤ Eta k/(16*(255/256:ℝ))
  width : (w k:ℝ)^2*q₂ k b*X b ≤ 1
  foreign : 4*(1/256:ℝ)*w k*q₂ k b*X b ≤ Eta k/32
  floor : 2*(s k:ℝ)*X b ≤ 1-Eta k*s k/(2*(255/256:ℝ))
  pair_margin : 49/64+2*(s k:ℝ)*X b <
    ((99/100:ℝ)+(255/256:ℝ)^2-1)/(255/256:ℝ)^2
  small : 2*(s k:ℝ)*X b ≤ 1/8
  pair_small : 2*(q₂ k b:ℝ)*X b ≤ 1/8
  flag : V42IncomingGuard.flagConstant/(s k:ℝ)^128 ≤ Theta k/4
  exception : V38Moments.exceptionCount (Theta k/4) 1 ≤ s k*q₂ k b
  theta_le_one : Theta k ≤ 1
  profile_exception : V38Moments.exceptionCount (Theta k) 1 ≤ w k/128
  profile_wx : (w k:ℝ)*X b < 1/256

private theorem cast_le {a b:ℚ} (h:a ≤ b) : (a:ℝ) ≤ (b:ℝ) := by exact_mod_cast h

theorem guards (k b : ℕ) (hk : 200 ≤ k) (hb : 4*k ≤ b) : Guards k b := by
  obtain ⟨hs,_,hqx,hsx,hwx,hloss,hwidth,hforeign⟩ := scalar_smallness k b (by omega) hb
  obtain ⟨heQ,heP,hreceipt⟩ := exception_common k b hk hb
  have hsR : (256:ℝ) ≤ s k := by exact_mod_cast hs
  have hwR : (1:ℝ) ≤ w k := by exact_mod_cast w_pos k
  have hη : 0 < Eta k := by unfold Eta eta; positivity
  have hx : 0 < X b := by unfold X x; positivity
  have hθ : 0 < Theta k := by unfold Theta theta; positivity
  have hηsQ : (s k:ℚ)*eta k ≤ 1/65536 := by
    rw [source_eta]
    simpa using reciprocal_le k 16 (by omega)
  have hηs : (s k:ℝ)*Eta k ≤ 1/65536 := by simpa only [X,Eta,Rat.cast_mul,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,Rat.cast_natCast,Rat.cast_pow] using cast_le hηsQ
  have hηsmall : Eta k ≤ 1/65536 := by nlinarith only [hsR,hηs,hη]
  have hη1 : Eta k ≤ 1 := by linarith
  have hwxR : (w k:ℝ)*X b ≤ 1/10000 := by simpa only [X,Eta,Rat.cast_mul,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,Rat.cast_natCast,Rat.cast_pow] using cast_le hwx
  have hxsmall : X b ≤ 1/10000 := by nlinarith only [hwR,hwxR,hx]
  have hqxR : (q₂ k b:ℝ)*X b ≤ 1/10000 := by simpa only [X,Eta,Rat.cast_mul,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,Rat.cast_natCast,Rat.cast_pow] using cast_le hqx
  have hsxR : (s k:ℝ)*X b ≤ 1/10000 := by simpa only [X,Eta,Rat.cast_mul,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,Rat.cast_natCast,Rat.cast_pow] using cast_le hsx
  have hwidthR : (w k:ℝ)^2*q₂ k b*X b ≤ 1 := by dsimp only [X,Eta]; exact_mod_cast hwidth
  have hlossR : (w k:ℝ)^2*X b ≤ Eta k/(32*(255/256:ℝ)) := by simpa only [X,Eta,Rat.cast_mul,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,Rat.cast_natCast,Rat.cast_pow] using cast_le hloss
  have hforeignR : (w k:ℝ)*q₂ k b*X b ≤ Eta k/(128*(1/256:ℝ)) := by simpa only [X,Eta,Rat.cast_mul,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,Rat.cast_natCast,Rat.cast_pow] using cast_le hforeign
  have hreceiptR : (32*(s k:ℝ))*(EexcBudget k:ℝ) ≤ Eta k*w k := by dsimp only [X,Eta]; exact_mod_cast hreceipt
  have he0 : (0:ℝ) ≤ EexcBudget k := Nat.cast_nonneg _
  have hew : (4*(EexcBudget k:ℝ)) ≤ w k := by
    have hmul := mul_nonneg (by linarith : (0:ℝ) ≤ 32*s k-4) he0
    have hηw := mul_le_mul_of_nonneg_right hη1 (Nat.cast_nonneg (w k))
    nlinarith only [hmul,hreceiptR,hηw]
  have hexc : 4*(2*ownerBudget k) ≤ w k := by exact_mod_cast hew
  have hreceiptFinal : (2*(s k:ℝ))*(2*ownerBudget k) ≤ Eta k*w k/16 := by
    have he : (EexcBudget k:ℝ)=2*(ownerBudget k:ℝ) := by simp [EexcBudget]
    rw [he] at hreceiptR
    nlinarith only [hreceiptR]
  have hflagQ := flag_margin k (by omega)
  have hflag : V42IncomingGuard.flagConstant/(s k:ℝ)^128 ≤ Theta k/4 := by
    have hC : (V38Schedule.C128:ℝ)=V42IncomingGuard.flagConstant := by
      unfold V38Schedule.C128 V42IncomingGuard.flagConstant V39IncomingGuard.flagConstant
      push_cast
      rfl
    have hh := cast_le hflagQ
    norm_num only [Rat.cast_div,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat,hC] at hh
    exact hh
  have heProfile : V38Moments.exceptionCount (Theta k) 1 ≤ w k/128 := by change V38Moments.exceptionCount (theta k:ℝ) 1 ≤ w k/128; omega
  have hθ1 : Theta k ≤ 1 := by
    change (theta k:ℝ) ≤ 1
    rw [theta_real]
    exact V39ExceptionBudget.dyadic_le_one _
  refine ⟨by omega,rfl,rfl,rfl,hx,hθ,hη,hη1,owner_count_bound k,hexc,hreceiptFinal,
    ?_,by linarith,by linarith,?_,hwidthR,?_,?_,?_,by linarith,by linarith,
    hflag,heQ,hθ1,heProfile,by linarith⟩
  · norm_num
    nlinarith only [hwxR,hηsmall]
  · norm_num at hlossR ⊢
    linarith only [hlossR]
  · norm_num at hforeignR ⊢
    linarith only [hforeignR]
  · norm_num
    nlinarith only [hsxR,hηs]
  · norm_num
    linarith only [hsxR]

#print axioms guards

end CurrentAdditive.V42AlignmentGuards


