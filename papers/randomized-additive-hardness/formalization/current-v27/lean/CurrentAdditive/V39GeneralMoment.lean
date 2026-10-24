import CurrentAdditive.GeneralCross
import CurrentAdditive.V38GeneralMomentRecovery

/-! The complete bounded-real-variable moment inequality in selected v39,
Appendix `moments.tex`, lemma `lem:conditioning-moment`. -/

namespace V39GeneralMoment

open Paper2 Paper2.FiniteLaw CurrentAdditive.EvenMoment
open CurrentAdditive.FourthMoment
open V38GeneralMoment
open scoped BigOperators

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

variable {Ω : Type*} [Fintype Ω]

/-- Direct low-order calculations for arbitrary bounded centered coordinates
of the true finite independent comparison distribution. -/
theorem iid_second_and_fourth (ν : FiniteLaw Ω) (m : ℕ)
    (X : Fin m → Ω → ℝ)
    (hcenter : ∀ i, ex ν (X i) = 0)
    (hbound : ∀ i ω, |X i ω| ≤ 1) :
    ex (ν.iid m) (fun ws => (∑ i, X i (ws i))^2) ≤ (m : ℝ) ∧
    ex (ν.iid m) (fun ws => (∑ i, X i (ws i))^4) ≤
      4*(m : ℝ)+3*(m : ℝ)^2 := by
  classical
  let μ : Fin m → FiniteLaw Ω := fun _ => ν
  let F : Fin m → Ω → ℝ := fun i ω => X i ω / 2
  let Y : Fin m → (Fin m → Ω) → ℝ := fun i ws => F i (ws i)
  have hcenterF (i : Fin m) : expect (μ i) (F i) = 0 := by
    have hh := expect_mul_const ν (X i) (1/2)
    have hc : expect ν (X i) = 0 := hcenter i
    simpa only [F, μ, div_eq_mul_inv, mul_comm, hc, mul_zero, zero_mul, one_mul] using hh
  have hsecond (i : Fin m) :
      expect (FiniteLaw.pi μ) (fun ws => (Y i ws)^2) ≤ 1/4 := by
    change expect (FiniteLaw.pi μ) (fun ws => (F i (ws i))^2) ≤ _
    rw [GeneralCross.expect_pi_coordinate μ i (fun a => (F i a)^2)]
    calc
      _ ≤ expect (μ i) (fun _ => 1/4) := by
        apply expect_le
        intro ω
        have hb := abs_le.mp (hbound i ω)
        dsimp [F]
        nlinarith
      _ = 1/4 := by
        have hh := expect_mul_const (μ i) (fun _ => 1) (1/4)
        simpa [expect_one] using hh
  have hfourth (i : Fin m) :
      expect (FiniteLaw.pi μ) (fun ws => (Y i ws)^4) ≤ 1/4 := by
    change expect (FiniteLaw.pi μ) (fun ws => (F i (ws i))^4) ≤ _
    rw [GeneralCross.expect_pi_coordinate μ i (fun a => (F i a)^4)]
    calc
      _ ≤ expect (μ i) (fun _ => 1/4) := by
        apply expect_le
        intro ω
        have hb := abs_le.mp (hbound i ω)
        have hs : (X i ω / 2)^2 ≤ 1/4 := by nlinarith
        dsimp [F]
        nlinarith [mul_nonneg (sq_nonneg (X i ω / 2)) (sub_nonneg.mpr hs)]
      _ = 1/4 := by
        have hh := expect_mul_const (μ i) (fun _ => 1) (1/4)
        simpa [expect_one] using hh
  have hcross := GeneralCross.pairCrossMoments_product μ F hcenterF
  have hh := fourth_bound_of_cross_moments (FiniteLaw.pi μ) Y hsecond hfourth
    hcross.cross1 hcross.cross31 hcross.cross13 hcross.cross22 Finset.univ
  have hs (ws : Fin m → Ω) :
      sumCentered Y Finset.univ ws = (∑ i, X i (ws i))/2 := by
    simp only [sumCentered, Y, F, Finset.sum_div]
  have hs2 : (fun ws => (sumCentered Y Finset.univ ws)^2) =
      (fun ws => (1/4)*(∑ i, X i (ws i))^2) := by
    funext ws
    rw [hs]
    ring
  have hs4 : (fun ws => (sumCentered Y Finset.univ ws)^4) =
      (fun ws => (1/16)*(∑ i, X i (ws i))^4) := by
    funext ws
    rw [hs]
    ring
  rcases hh with ⟨hh2,hh4⟩
  rw [hs2, expect_mul_const] at hh2
  rw [hs4, expect_mul_const] at hh4
  simp only [Finset.card_univ, Fintype.card_fin] at hh2 hh4
  have hiid : ν.iid m = FiniteLaw.pi μ := by rfl
  change expect (ν.iid m) (fun ws => (∑ i, X i (ws i))^2) ≤ (m : ℝ) ∧
    expect (ν.iid m) (fun ws => (∑ i, X i (ws i))^4) ≤ _
  rw [hiid]
  constructor <;> nlinarith

/-- The true independent law satisfies the manuscript's constant for every
positive natural half-order, including the empty family of variables. -/
theorem iid_bounded_centered_even_moment
    (ν : FiniteLaw Ω) (m r : ℕ) (hr : 1 ≤ r)
    (X : Fin m → Ω → ℝ)
    (hcenter : ∀ i, ex ν (X i) = 0)
    (hbound : ∀ i ω, |X i ω| ≤ 1) :
    ex (ν.iid m) (fun ws => |∑ i, X i (ws i)|^(2*r)) ≤
      (((r : ℝ)^2)*m)^r := by
  by_cases hr3 : 3 ≤ r
  · exact iid_bounded_centered_even_moment_ge_three ν m r hr3 X hcenter hbound
  have hh := iid_second_and_fourth ν m X hcenter hbound
  have habs2 (x : ℝ) : |x|^2 = x^2 := sq_abs x
  have habs4 (x : ℝ) : |x|^4 = x^4 := (show Even 4 by decide).pow_abs x
  have hrcases : r = 1 ∨ r = 2 := by omega
  rcases hrcases with rfl | rfl
  · simpa only [Nat.cast_one, one_pow, one_mul, pow_one, habs2] using hh.1
  · by_cases hm : m = 0
    · subst m
      simp [ex]
    · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Nat.pos_of_ne_zero hm)
      have htarget : 4*(m : ℝ)+3*(m : ℝ)^2 ≤ ((2 : ℝ)^2*m)^2 := by
        nlinarith [mul_nonneg (show 0 ≤ (m : ℝ) by positivity)
          (show 0 ≤ (m : ℝ)-1 by linarith)]
      simpa only [Nat.cast_ofNat, habs4] using hh.2.trans htarget

/-- Selected v39's full arbitrary-variable moment theorem. The hypothesis is
equality of every joint event law on at most `2r` variables; centering and
boundedness are imposed on the original distribution. -/
theorem bounded_wise_even_moment
    (ν : FiniteLaw Ω) (m r : ℕ) (hr : 1 ≤ r)
    (X : Fin m → Ω → ℝ)
    (hcenter : ∀ i, ex ν (X i) = 0)
    (hbound : ∀ i ω, |X i ω| ≤ 1)
    (hjoint : JointLawAgreement ν X (2*r)) :
    ex ν (fun ω => |∑ i, X i ω|^(2*r)) ≤
      (((r : ℝ)^2)*m)^r := by
  have hraw := bounded_wise_raw_moment_eq_iid ν X hjoint
  have habs (x : ℝ) : |x|^(2*r) = x^(2*r) :=
    (show Even (2*r) by simp).pow_abs x
  calc
    _ = ex ν (fun ω => (∑ i, X i ω)^(2*r)) := by simp_rw [habs]
    _ = ex (ν.iid m) (fun ws => (∑ i, X i (ws i))^(2*r)) := hraw
    _ = ex (ν.iid m) (fun ws => |∑ i, X i (ws i)|^(2*r)) := by simp_rw [habs]
    _ ≤ _ := iid_bounded_centered_even_moment ν m r hr X hcenter hbound

theorem bounded_wise_moment_1024
    (ν : FiniteLaw Ω) (m : ℕ) (X : Fin m → Ω → ℝ)
    (hcenter : ∀ i, ex ν (X i) = 0)
    (hbound : ∀ i ω, |X i ω| ≤ 1)
    (hjoint : JointLawAgreement ν X 1024) :
    ex ν (fun ω => |∑ i, X i ω|^1024) ≤ ((2 : ℝ)^18*m)^512 := by
  simpa only [show 2*512 = 1024 by rfl,
    show ((512 : ℕ) : ℝ)^2 = (2 : ℝ)^18 by norm_num] using
      bounded_wise_even_moment ν m 512 (by omega) X hcenter hbound hjoint

theorem bounded_wise_moment_256
    (ν : FiniteLaw Ω) (m : ℕ) (X : Fin m → Ω → ℝ)
    (hcenter : ∀ i, ex ν (X i) = 0)
    (hbound : ∀ i ω, |X i ω| ≤ 1)
    (hjoint : JointLawAgreement ν X 256) :
    ex ν (fun ω => |∑ i, X i ω|^256) ≤ ((2 : ℝ)^14*m)^128 := by
  simpa only [show 2*128 = 256 by rfl,
    show ((128 : ℕ) : ℝ)^2 = (2 : ℝ)^14 by norm_num] using
      bounded_wise_even_moment ν m 128 (by omega) X hcenter hbound hjoint

#print axioms iid_second_and_fourth
#print axioms iid_bounded_centered_even_moment
#print axioms bounded_wise_even_moment
#print axioms bounded_wise_moment_1024
#print axioms bounded_wise_moment_256

end V39GeneralMoment
