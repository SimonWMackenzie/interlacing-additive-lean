import CurrentAdditive.V39FullScheduleGuards
import CurrentAdditive.V39IncomingGuard
import CurrentAdditive.V39GeneralExceptionBudget

/-! Literal passing-test consumer for the common full-product interlace.
All bounds follow from the literal full schedule tests. The public cutoff
supplies those tests separately. Exact rational-tolerance conditioning is
charged through the general exception-budget theorem.
-/

namespace CurrentAdditive.V39FullAlignmentGuards

open V38Schedule
set_option maxHeartbeats 2000000

abbrev X (L : ℕ) : ℝ := ((fullX L : ℚ) : ℝ)
abbrev Eta (c : ℚ) (L : ℕ) : ℝ := ((fullEta c L : ℚ) : ℝ)
abbrev Theta (L : ℕ) : ℝ := ((theta (fullQ L) : ℚ) : ℝ)

private theorem cast_le {a b : ℚ} (h : a ≤ b) : (a:ℝ) ≤ (b:ℝ) := by
  exact_mod_cast h

theorem theta_eq_dyadic (L : ℕ) :
    Theta L = V39ExceptionBudget.dyadic (9+fullQlog L) := by
  rw [show Theta L = ((1/(2^(9+fullQlog L):ℚ):ℚ):ℝ) from
    congrArg (fun z : ℚ => (z:ℝ)) (full_theta_exact L)]
  unfold V39ExceptionBudget.dyadic
  rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]
  push_cast
  simp only [one_div]

theorem theta_quarter_eq_dyadic (L : ℕ) :
    Theta L/4 = V39ExceptionBudget.dyadic (11+fullQlog L) := by
  have h := congrArg (fun z : ℚ => (z:ℝ)) (full_theta_quarter_exact L)
  push_cast at h
  rw [h]
  unfold V39ExceptionBudget.dyadic
  rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]
  simp only [one_div]

structure Guards (c : ℚ) (L : ℕ) : Prop where
  r_ge : 2 ≤ 8*ell L
  w_pow : fullW L = 2^(8*ell L)
  q_pow : fullQ₂ L = 2^(L+2*(16+ell L))
  s_pow : fullS L = 2^(16+ell L)
  x_pos : 0 < X L
  theta_pos : 0 < Theta L
  eta_pos : 0 < Eta c L
  eta_le_one : Eta c L ≤ 1
  exc : 4*(2*e0 (fullQlog L) (fullEta c L)) ≤ fullW L
  receipt : (512*(1/256 : ℝ)*((8*ell L : ℕ)+2)*fullS L)*
    (2*e0 (fullQlog L) (fullEta c L)) ≤ Eta c L*fullW L/16
  init : 2*(fullW L : ℝ)*X L+Eta c L/(16*(255/256 : ℝ)) ≤ 1
  wx : (fullW L : ℝ)*X L ≤ 1
  two_x : 2*X L ≤ 1
  loss : 2*(fullW L : ℝ)^2*X L ≤ Eta c L/(16*(255/256 : ℝ))
  width : (fullW L : ℝ)^2*fullQ₂ L*X L ≤ 1
  foreign : 4*(1/256 : ℝ)*fullW L*fullQ₂ L*X L ≤ Eta c L/32
  floor : 2*(fullS L : ℝ)*X L ≤ 1-Eta c L*fullS L/(2*(255/256 : ℝ))
  pair_margin : 49/64+2*(fullS L : ℝ)*X L <
    ((99/100 : ℝ)+(255/256 : ℝ)^2-1)/(255/256 : ℝ)^2
  small : 2*(fullS L : ℝ)*X L ≤ 1/8
  pair_small : 2*(fullQ₂ L : ℝ)*X L ≤ 1/8
  flag : V39IncomingGuard.flagConstant/(fullS L : ℝ)^128 ≤ Theta L/4
  exception : V38Moments.exceptionCount (Theta L/4) 1 ≤ fullS L*fullQ₂ L
  theta_le_one : Theta L ≤ 1
  profile_exception : V38Moments.exceptionCount (Theta L) 1 ≤ fullW L/128
  profile_wx : (fullW L : ℝ)*X L < 1/256
  cap : V38Moments.exceptionCount (Theta L) (Eta c L/2) ≤
    e0 (fullQlog L) (fullEta c L)

theorem guards_of_tests (c δv ζ : ℚ) (L m : ℕ) (hc : 0 < c)
    (htests : FullTests c L m δv ζ) : Guards c L := by
  rcases htests.1 with ⟨hs,hη,_,_,_,hqx,hsx,hwx,hloss,hwidth,hforeign,
    heunit,hequarter,hflag,hexc,hreceipt⟩
  dsimp only [fullInput] at hη hqx hsx hwx hloss hwidth hforeign heunit hequarter hflag hexc hreceipt
  change 256 ≤ fullS L at hs
  have hL16 : 16 ≤ L := htests.2.2.1
  have hell : 1 ≤ ell L := by
    have hp := Nat.le_pow_clog (by decide : 1 < 2) (L+1)
    change L+1 ≤ 2^ell L at hp
    by_contra hn
    have he : ell L=0 := by omega
    rw [he] at hp
    norm_num at hp
    omega
  have hx : 0 < X L := by
    have hq : (0 : ℚ) < fullX L := by unfold fullX; positivity
    exact_mod_cast hq
  have hsR : (1 : ℝ) ≤ fullS L := by exact_mod_cast (by omega : 1 ≤ fullS L)
  have hwR : (1 : ℝ) ≤ fullW L := by
    have h : 1 ≤ fullW L := by
      have hp : 0 < fullW L := by unfold fullW; positivity
      omega
    exact_mod_cast h
  have hηpos : 0 < Eta c L := by
    have hq : (0 : ℚ) < fullEta c L := by unfold fullEta; positivity
    exact_mod_cast hq
  have hηsQ : (fullS L : ℚ)*fullEta c L ≤ 1/2^16 :=
    hη.trans (div_le_div_of_nonneg_right (min_le_left _ _) (by positivity))
  norm_num at hηsQ
  have hηs : (fullS L : ℝ)*Eta c L ≤ 1/65536 := by
    have h := cast_le hηsQ
    norm_num only [Rat.cast_mul,Rat.cast_natCast,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at h
    exact h
  have hηsmall : Eta c L ≤ 1/65536 := by nlinarith
  have hη1 : Eta c L ≤ 1 := by linarith
  have hwxR : (fullW L : ℝ)*X L ≤ 1/10000 := by
    have h := cast_le hwx
    norm_num only [Rat.cast_mul,Rat.cast_natCast,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at h
    exact h
  have hqxR : (fullQ₂ L : ℝ)*X L ≤ 1/10000 := by
    have h := cast_le hqx
    norm_num only [Rat.cast_mul,Rat.cast_natCast,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at h
    exact h
  have hsxR : (fullS L : ℝ)*X L ≤ 1/10000 := by
    have h := cast_le hsx
    norm_num only [Rat.cast_mul,Rat.cast_natCast,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at h
    exact h
  have hxsmall : X L ≤ 1/10000 := by nlinarith
  have hlossR : 2*(fullW L : ℝ)^2*X L ≤ Eta c L/(16*(255/256 : ℝ)) := by
    have h := cast_le hloss
    norm_num only [Rat.cast_mul,Rat.cast_natCast,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,Rat.cast_pow] at h
    simpa only [X,Eta,show (16*(255/256:ℝ))=255/16 by norm_num] using h
  have hwidthR : (fullW L : ℝ)^2*fullQ₂ L*X L ≤ 1 := by
    dsimp only [X]
    exact_mod_cast hwidth
  have hforeignR : 4*(1/256 : ℝ)*fullW L*fullQ₂ L*X L ≤ Eta c L/32 := by
    have h := cast_le hforeign
    norm_num only [Rat.cast_mul,Rat.cast_natCast,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at h
    simpa only [X,Eta,show (4*(1/256:ℝ))=1/64 by norm_num] using h
  have hexcN : 2*e0 (fullQlog L) (fullEta c L) ≤ fullW L/4 := hexc
  have hreceiptR : (512*(1/256 : ℝ)*((8*ell L : ℕ)+2)*fullS L)*
      (2*e0 (fullQlog L) (fullEta c L)) ≤ Eta c L*fullW L/16 := by
    change (Kstar (8*ell L) (fullS L):ℚ)*Eexc (fullQlog L) (fullEta c L) ≤
      fullEta c L*fullW L/16 at hreceipt
    have hr : (((Kstar (8*ell L) (fullS L):ℚ)*Eexc (fullQlog L) (fullEta c L):ℚ):ℝ) ≤
      ((fullEta c L*fullW L/16:ℚ):ℝ) := by exact_mod_cast hreceipt
    push_cast at hr
    convert hr using 1 <;> norm_num [Kstar,Eexc,Eta] <;> ring
  have hflagR : V39IncomingGuard.flagConstant/(fullS L:ℝ)^128 ≤ Theta L/4 := by
    have hC : ((C128:ℚ):ℝ)=V39IncomingGuard.flagConstant := by
      unfold C128 V39IncomingGuard.flagConstant
      push_cast
      rfl
    have hcast := cast_le hflag
    simp only [Rat.cast_div,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat,hC] at hcast
    exact hcast
  have heQ : V38Moments.exceptionCount (Theta L/4) 1 ≤ fullS L*fullQ₂ L := by
    rw [theta_quarter_eq_dyadic]
    exact (V39ExceptionBudget.exception_le_ebar _).trans hequarter
  have heP : V38Moments.exceptionCount (Theta L) 1 ≤ fullW L/128 := by
    rw [theta_eq_dyadic]
    exact (V39ExceptionBudget.exception_le_ebar _).trans heunit
  have hθpos : 0 < Theta L := by rw [theta_eq_dyadic]; exact V39ExceptionBudget.dyadic_pos _
  have hθ1 : Theta L ≤ 1 := by rw [theta_eq_dyadic]; exact V39ExceptionBudget.dyadic_le_one _
  have hcap : V38Moments.exceptionCount (Theta L) (Eta c L/2) ≤
      e0 (fullQlog L) (fullEta c L) := by
    rw [theta_eq_dyadic]
    have hp : (0:ℚ) < fullEta c L := by unfold fullEta; positivity
    have h1 : fullEta c L ≤ 1 := by exact_mod_cast hη1
    have h := V39GeneralExceptionBudget.exception_le_ebar (9+fullQlog L)
      (fullEta c L/2) (by positivity) (by linarith)
    simpa only [e0,Eta,Rat.cast_div,Rat.cast_ofNat] using h
  refine ⟨by omega, ?_, ?_, rfl, hx, hθpos, hηpos, hη1, by omega,
    hreceiptR, ?_, by linarith, by linarith, hlossR, hwidthR, hforeignR,
    ?_, ?_, by linarith, by linarith, hflagR, heQ, hθ1, heP, by linarith, hcap⟩
  · rfl
  · unfold fullQ₂ fullS
    rw [← pow_mul,← pow_add]
    congr 1
    omega
  · norm_num
    linarith
  · norm_num
    nlinarith
  · norm_num
    linarith

end CurrentAdditive.V39FullAlignmentGuards

#print axioms CurrentAdditive.V39FullAlignmentGuards.guards_of_tests
