import CurrentAdditive.V39GeneratedProfileGuards
import CurrentAdditive.V39IncomingGuard
import CurrentAdditive.V39GeneralExceptionBudget

/-! Literal passing-test consumer for the common generated interlace.
All bounds use the actual first passing tests; L is never assumed to exceed
the sufficient cutoff. Only the general-tolerance conditioning count is left
for the separately proved budget adapter.
-/

namespace CurrentAdditive.V39GeneratedAlignmentGuards

open V38Schedule
set_option maxHeartbeats 2000000

abbrev X (L : ℕ) : ℝ := ((generatedX L : ℚ) : ℝ)
abbrev Eta (c : ℚ) (L : ℕ) : ℝ := ((generatedEta c L : ℚ) : ℝ)
abbrev Theta (L : ℕ) : ℝ := ((theta (generatedQ L) : ℚ) : ℝ)

private theorem cast_le {a b : ℚ} (h : a ≤ b) : (a:ℝ) ≤ (b:ℝ) := by
  exact_mod_cast h

theorem theta_eq_dyadic (L : ℕ) :
    Theta L = V39ExceptionBudget.dyadic (9+generatedQlog L) := by
  rw [show Theta L = ((1/(2^(9+generatedQlog L):ℚ):ℚ):ℝ) from
    congrArg (fun z : ℚ => (z:ℝ)) (generated_theta_exact L)]
  unfold V39ExceptionBudget.dyadic
  rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]
  push_cast
  simp only [one_div]

theorem theta_quarter_eq_dyadic (L : ℕ) :
    Theta L/4 = V39ExceptionBudget.dyadic (11+generatedQlog L) := by
  have h := congrArg (fun z : ℚ => (z:ℝ)) (generated_theta_quarter_exact L)
  push_cast at h
  rw [h]
  unfold V39ExceptionBudget.dyadic
  rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]
  simp only [one_div]

structure Guards (c : ℚ) (L : ℕ) : Prop where
  r_ge : 2 ≤ 2*L
  w_pow : generatedW L = 2^(2*L)
  q_pow : generatedQ₂ L = 2^(4*L)
  s_pow : generatedS L = 2^quarterCeil L
  x_pos : 0 < X L
  theta_pos : 0 < Theta L
  eta_pos : 0 < Eta c L
  eta_le_one : Eta c L ≤ 1
  exc : 4*(2*e0 (generatedQlog L) (generatedEta c L)) ≤ generatedW L
  receipt : (512*(1/256 : ℝ)*((2*L : ℕ)+2)*generatedS L)*
    (2*e0 (generatedQlog L) (generatedEta c L)) ≤ Eta c L*generatedW L/16
  init : 2*(generatedW L : ℝ)*X L+Eta c L/(16*(255/256 : ℝ)) ≤ 1
  wx : (generatedW L : ℝ)*X L ≤ 1
  two_x : 2*X L ≤ 1
  loss : 2*(generatedW L : ℝ)^2*X L ≤ Eta c L/(16*(255/256 : ℝ))
  width : (generatedW L : ℝ)^2*generatedQ₂ L*X L ≤ 1
  foreign : 4*(1/256 : ℝ)*generatedW L*generatedQ₂ L*X L ≤ Eta c L/32
  floor : 2*(generatedS L : ℝ)*X L ≤ 1-Eta c L*generatedS L/(2*(255/256 : ℝ))
  pair_margin : 49/64+2*(generatedS L : ℝ)*X L <
    ((99/100 : ℝ)+(255/256 : ℝ)^2-1)/(255/256 : ℝ)^2
  small : 2*(generatedS L : ℝ)*X L ≤ 1/8
  pair_small : 2*(generatedQ₂ L : ℝ)*X L ≤ 1/8
  flag : V39IncomingGuard.flagConstant/(generatedS L : ℝ)^128 ≤ Theta L/4
  exception : V38Moments.exceptionCount (Theta L/4) 1 ≤ generatedS L*generatedQ₂ L
  theta_le_one : Theta L ≤ 1
  profile_exception : V38Moments.exceptionCount (Theta L) 1 ≤ generatedW L/128
  profile_wx : (generatedW L : ℝ)*X L < 1/256
  cap : V38Moments.exceptionCount (Theta L) (Eta c L/2) ≤
    e0 (generatedQlog L) (generatedEta c L)

theorem guards_of_tests (c δv ζ : ℚ) (L m : ℕ) (hc : 0 < c)
    (htests : GeneratedTests c L m δv ζ) : Guards c L := by
  obtain ⟨hb,_,_,hx,hx1,_,hqx,hsx,_⟩ :=
    V39GeneratedProfileGuards.scalar_parameters c δv ζ L m htests
  rcases htests.1 with ⟨hs,hη,_,_,_,_,_,hwx,hloss,hwidth,hforeign,
    heunit,hequarter,hflag,hexc,hreceipt⟩
  dsimp only [generatedInput] at hη hwx hloss hwidth hforeign heunit hequarter hflag hexc hreceipt
  change 256 ≤ generatedS L at hs
  have hL : 1 ≤ L := by unfold quarterCeil at hb; omega
  have hsR : (1 : ℝ) ≤ generatedS L := by exact_mod_cast (by omega : 1 ≤ generatedS L)
  have hwR : (1 : ℝ) ≤ generatedW L := by
    have h : 1 ≤ generatedW L := by
      have hp : 0 < generatedW L := by unfold generatedW generatedN; positivity
      omega
    exact_mod_cast h
  have hηpos : 0 < Eta c L := by
    have hq : (0:ℚ) < generatedEta c L := div_pos hc (by exact_mod_cast (by unfold generatedS; positivity : 0 < generatedS L))
    exact_mod_cast hq
  have hηsQ : (generatedS L : ℚ)*generatedEta c L ≤ 1/2^16 :=
    hη.trans (div_le_div_of_nonneg_right (min_le_left _ _) (by positivity))
  norm_num at hηsQ
  have hηs : (generatedS L : ℝ)*Eta c L ≤ 1/65536 := by
    have h := cast_le hηsQ
    norm_num only [Rat.cast_mul,Rat.cast_natCast,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at h
    exact h
  have hηsmall : Eta c L ≤ 1/65536 := by nlinarith
  have hη1 : Eta c L ≤ 1 := by linarith
  have hwxR : (generatedW L : ℝ)*X L ≤ 1/10000 := by
    have h := cast_le hwx
    norm_num only [Rat.cast_mul,Rat.cast_natCast,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at h
    exact h
  have hxsmall : X L ≤ 1/10000 := by nlinarith
  have hlossR : 2*(generatedW L : ℝ)^2*X L ≤ Eta c L/(16*(255/256 : ℝ)) := by
    have h := cast_le hloss
    norm_num only [Rat.cast_mul,Rat.cast_natCast,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,Rat.cast_pow] at h
    simpa only [X,Eta,show (16*(255/256:ℝ))=255/16 by norm_num] using h
  have hwidthR : (generatedW L : ℝ)^2*generatedQ₂ L*X L ≤ 1 := by
    dsimp only [X]
    exact_mod_cast hwidth
  have hforeignR : 4*(1/256 : ℝ)*generatedW L*generatedQ₂ L*X L ≤ Eta c L/32 := by
    have h := cast_le hforeign
    norm_num only [Rat.cast_mul,Rat.cast_natCast,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at h
    simpa only [X,Eta,show (4*(1/256:ℝ))=1/64 by norm_num] using h
  have hexcN : 2*e0 (generatedQlog L) (generatedEta c L) ≤ generatedW L/4 := hexc
  have hreceiptR : (512*(1/256 : ℝ)*((2*L : ℕ)+2)*generatedS L)*
      (2*e0 (generatedQlog L) (generatedEta c L)) ≤ Eta c L*generatedW L/16 := by
    change (Kstar (2*L) (generatedS L):ℚ)*Eexc (generatedQlog L) (generatedEta c L) ≤
      generatedEta c L*generatedW L/16 at hreceipt
    have hr : (((Kstar (2*L) (generatedS L):ℚ)*Eexc (generatedQlog L) (generatedEta c L):ℚ):ℝ) ≤
      ((generatedEta c L*generatedW L/16:ℚ):ℝ) := by exact_mod_cast hreceipt
    push_cast at hr
    convert hr using 1 <;> norm_num [Kstar,Eexc,Eta] <;> ring
  have hflagR : V39IncomingGuard.flagConstant/(generatedS L:ℝ)^128 ≤ Theta L/4 := by
    have hC : ((C128:ℚ):ℝ)=V39IncomingGuard.flagConstant := by
      unfold C128 V39IncomingGuard.flagConstant
      push_cast
      rfl
    have hcast := cast_le hflag
    simp only [Rat.cast_div,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat,hC] at hcast
    exact hcast
  have heQ : V38Moments.exceptionCount (Theta L/4) 1 ≤ generatedS L*generatedQ₂ L := by
    rw [theta_quarter_eq_dyadic]
    exact (V39ExceptionBudget.exception_le_ebar _).trans hequarter
  have heP : V38Moments.exceptionCount (Theta L) 1 ≤ generatedW L/128 := by
    rw [theta_eq_dyadic]
    exact (V39ExceptionBudget.exception_le_ebar _).trans heunit
  have hθpos : 0 < Theta L := by rw [theta_eq_dyadic]; exact V39ExceptionBudget.dyadic_pos _
  have hθ1 : Theta L ≤ 1 := by rw [theta_eq_dyadic]; exact V39ExceptionBudget.dyadic_le_one _
  have hcap : V38Moments.exceptionCount (Theta L) (Eta c L/2) ≤
      e0 (generatedQlog L) (generatedEta c L) := by
    rw [theta_eq_dyadic]
    have hp : (0:ℚ) < generatedEta c L :=
      div_pos hc (by exact_mod_cast (by unfold generatedS; positivity : 0 < generatedS L))
    have h1 : generatedEta c L ≤ 1 := by exact_mod_cast hη1
    have h := V39GeneralExceptionBudget.exception_le_ebar (9+generatedQlog L)
      (generatedEta c L/2) (by positivity) (by linarith)
    simpa only [e0,Eta,Rat.cast_div,Rat.cast_ofNat] using h
  refine ⟨by omega, ?_, ?_, rfl, hx, hθpos, hηpos, hη1, by omega,
    hreceiptR, ?_, by linarith, by linarith, hlossR, hwidthR, hforeignR,
    ?_, ?_, by linarith, by linarith, hflagR, heQ, hθ1, heP, by linarith, hcap⟩
  · unfold generatedW generatedN
    rw [← pow_mul]
    congr 1
    omega
  · unfold generatedQ₂ generatedN
    rw [← pow_mul]
    congr 1
    omega
  · norm_num
    linarith
  · norm_num
    nlinarith
  · norm_num
    linarith

end CurrentAdditive.V39GeneratedAlignmentGuards

#print axioms CurrentAdditive.V39GeneratedAlignmentGuards.guards_of_tests
