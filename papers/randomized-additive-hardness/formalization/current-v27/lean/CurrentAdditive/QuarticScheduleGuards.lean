import CurrentAdditive.QuarticCanonicalGuarantees
import CurrentAdditive.RandomizedQuarticSchedule

namespace Paper2.CurrentAdditive.QuarticScheduleGuards

open SourceProfileParameters SourceSurvivingCollisions
  CurrentAdditive.RandomizedSchedule

private theorem cast_le {a b : ℚ} (h : a ≤ b) : (a : ℝ) ≤ (b : ℝ) := by
  exact_mod_cast h

private theorem cast_lt {a b : ℚ} (h : a < b) : (a : ℝ) < (b : ℝ) := by
  exact_mod_cast h

structure Guards (n m L Δ : ℕ) [NeZero n] (γ : ℚ) : Prop where
  hL : 16 ≤ L
  hinner : (width L : ℝ) * rho L ≤ 1 / 1000
  houter : (outerWidth L : ℝ) * x L ≤ 1 / 10000
  hwide : (10 * L : ℝ) ≤ (outerWidth L : ℝ) / 4096
  href : (width L : ℝ) * x L ≤ 1 / 10000
  hscale : 4 * (width L : ℝ) ^ 2 * rho L ≤ 1
  hcountSource : 8 * (width L : ℝ) * (width L - 2 : ℕ) ≤
    witnessDensity (γ : ℝ) * outerWidth L / 16
  hw : width27 L = 2 ^ (4 * RestorationWidthScheduleScratch.ell L)
  hw2 : 2 ≤ width27 L
  hQ : Q27 (V := Fin n) (E := Fin m) L γ Δ =
    2 ^ q27 (V := Fin n) (E := Fin m) L γ Δ
  hsize : 2 * (n + width L - 3) ≤ outerWidth L
  hηq : ((SourceRationalScheduleScratch.eta (V := Fin n) (E := Fin m) L γ Δ : ℚ) : ℝ) =
    deletionAllowance (V := Fin n) (E := Fin m) (γ : ℝ) Δ (width L)
  hquarter : CurrentAdditive.QuarticSchedule.quarterCheck27Prop
    (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ)
    (SourceRationalScheduleScratch.eta (V := Fin n) (E := Fin m) L γ Δ)
  hsmall : 2 * (width27 L : ℝ) ^ 2 * x L ≤
    deletionAllowance (V := Fin n) (E := Fin m) (γ : ℝ) Δ (width L) /
      (16 * (127 / 128 : ℝ))
  hfirst : 4 * (1 / 256 : ℝ) * width27 L * outerWidth L * x L ≤
    deletionAllowance (V := Fin n) (E := Fin m) (γ : ℝ) Δ (width L) / 32
  hlast : 4 * (1 / 256 : ℝ) * width27 L / outerWidth L ≤
    deletionAllowance (V := Fin n) (E := Fin m) (γ : ℝ) Δ (width L) / 32
  hKcheck :
    (1024 * (1 / 256 : ℝ) * RestorationCoverParameters.B2
      (Q27 (V := Fin n) (E := Fin m) L γ Δ) *
      (4 * RestorationWidthScheduleScratch.ell L + 2) * width L) *
    CurrentAdditive.QuarticSchedule.E27
      (Q27 (V := Fin n) (E := Fin m) L γ Δ)
      (SourceRationalScheduleScratch.eta (V := Fin n) (E := Fin m) L γ Δ) ≤
    deletionAllowance (V := Fin n) (E := Fin m) (γ : ℝ) Δ (width L) *
      width27 L / 16
  hxsmall : ((width27 L : ℝ) ^ 2 * (outerWidth L : ℝ)) * x L ≤ 1
  hstar : 4 * RestorationCoverParameters.tStar
    (Q27 (V := Fin n) (E := Fin m) L γ Δ) ≤ width27 L
  hsmallwx : (width27 L : ℝ) * x L ≤ 1 / 10000
  hmargin : 2 * width27 L * x L +
    deletionAllowance (V := Fin n) (E := Fin m) (γ : ℝ) Δ (width L) /
      (16 * (127 / 128 : ℝ)) < 1
  hbridge : 80 * (L : ℝ) ≤
    (Q27 (V := Fin n) (E := Fin m) L γ Δ : ℝ) *
      (deletionAllowance (V := Fin n) (E := Fin m) (γ : ℝ) Δ (width L) /
        (16 * (width27 L : ℝ)))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
theorem guards_of_checks27 {n m : ℕ} [NeZero n]
    (L Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ) (hE : 0 < m)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) L Δ γ) :
    Guards n m L Δ γ := by
  rcases hc with ⟨_, hsize, hscaleQ, hinnerQ, houterQ,
    hrefQ, hsmallwxQ, hwideQ, hcountQ, _, _, hstar,
    hmarginQ, hsmallQ, hxsmallQ, hfirstQ, hlastQ,
    hquarterQ, hKcheckQ, _, hL, _⟩
  let w := width27 L
  let r := 4 * RestorationWidthScheduleScratch.ell L
  let Q := Q27 (V := Fin n) (E := Fin m) L γ Δ
  let η := SourceRationalScheduleScratch.eta (V := Fin n) (E := Fin m) L γ Δ
  have hw : w = 2 ^ r := rfl
  have hQ : Q = 2 ^ q27 (V := Fin n) (E := Fin m) L γ Δ :=
    Q27_dyadic L γ Δ
  have hw2 : 2 ≤ w := by
    have hell : 1 ≤ RestorationWidthScheduleScratch.ell L := by
      unfold RestorationWidthScheduleScratch.ell
      have h := Nat.clog_mono_right 2 (show 2 ≤ L + 1 by omega)
      norm_num at h ⊢
      exact h
    have hr : 1 ≤ r := by dsimp [r]; omega
    have hpow : 2 ^ 1 ≤ 2 ^ r := pow_le_pow_right₀ (by omega) hr
    simpa only [hw, pow_one] using hpow
  have hscale : 4 * (width L : ℝ) ^ 2 * rho L ≤ 1 := by
    simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast,
      Rat.cast_ofNat, Rat.cast_one, CompletePublicScheduleScratch.rhoQ_cast]
      using cast_le hscaleQ
  have hinner : (width L : ℝ) * rho L ≤ 1 / 1000 := by
    simpa only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_div,
      Rat.cast_ofNat, Rat.cast_one, CompletePublicScheduleScratch.rhoQ_cast]
      using cast_le hinnerQ
  have houter : (outerWidth L : ℝ) * x L ≤ 1 / 10000 := by
    simpa only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_div,
      Rat.cast_ofNat, Rat.cast_one, CompletePublicScheduleScratch.xQ_cast]
      using cast_le houterQ
  have href : (width L : ℝ) * x L ≤ 1 / 10000 := by
    simpa only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_div,
      Rat.cast_ofNat, Rat.cast_one, CompletePublicScheduleScratch.xQ_cast]
      using cast_le hrefQ
  have hsmallwx : (w : ℝ) * x L ≤ 1 / 10000 := by
    simpa only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_div,
      Rat.cast_ofNat, Rat.cast_one, CompletePublicScheduleScratch.xQ_cast,
      w] using cast_le hsmallwxQ
  have hwide : (10 * L : ℝ) ≤ (outerWidth L : ℝ) / 4096 := by
    simpa only [Rat.cast_le, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast,
      Rat.cast_ofNat, Nat.cast_mul] using cast_le hwideQ
  have hcount : 8 * (width L : ℝ) * (width L - 2 : ℕ) ≤
      witnessDensity (γ : ℝ) * outerWidth L / 16 := by
    rw [← SourceRationalScheduleScratch.witnessDensity_cast]
    exact_mod_cast hcountQ
  have hηq : (η : ℝ) =
      deletionAllowance (V := Fin n) (E := Fin m) (γ : ℝ) Δ (width L) :=
    SourceRationalScheduleScratch.eta_cast L γ Δ
  have hmargin : 2 * w * x L +
      deletionAllowance (V := Fin n) (E := Fin m) (γ : ℝ) Δ (width L) /
        (16 * (127 / 128 : ℝ)) < 1 := by
    simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div,
      Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one,
      CompletePublicScheduleScratch.xQ_cast,
      SourceRationalScheduleScratch.eta_cast,
      CompletePublicScheduleScratch.gQ, w,
      Nat.cast_mul] using cast_lt hmarginQ
  have hsmall : 2 * (w : ℝ) ^ 2 * x L ≤
      deletionAllowance (V := Fin n) (E := Fin m) (γ : ℝ) Δ (width L) /
        (16 * (127 / 128 : ℝ)) := by
    simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
      Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one,
      CompletePublicScheduleScratch.xQ_cast,
      SourceRationalScheduleScratch.eta_cast,
      CompletePublicScheduleScratch.gQ, w,
      Nat.cast_mul] using cast_le hsmallQ
  have hxsmall : ((w : ℝ) ^ 2 * (outerWidth L : ℝ)) * x L ≤ 1 := by
    rw [← CompletePublicScheduleScratch.xQ_cast]
    exact_mod_cast hxsmallQ
  have hfirst : 4 * (1 / 256 : ℝ) * w * outerWidth L * x L ≤
      deletionAllowance (V := Fin n) (E := Fin m) (γ : ℝ) Δ (width L) / 32 := by
    simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_natCast,
      Rat.cast_ofNat, Rat.cast_one,
      CompletePublicScheduleScratch.xQ_cast,
      SourceRationalScheduleScratch.eta_cast,
      CompletePublicScheduleScratch.muQ, w] using cast_le hfirstQ
  have hlast : 4 * (1 / 256 : ℝ) * w / outerWidth L ≤
      deletionAllowance (V := Fin n) (E := Fin m) (γ : ℝ) Δ (width L) / 32 := by
    simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_natCast,
      Rat.cast_ofNat, Rat.cast_one,
      CompletePublicScheduleScratch.muQ,
      SourceRationalScheduleScratch.eta_cast, w] using cast_le hlastQ
  have hKcheck :
      (1024 * (1 / 256 : ℝ) * RestorationCoverParameters.B2 Q *
        (r + 2) * width L) * CurrentAdditive.QuarticSchedule.E27 Q η ≤
      deletionAllowance (V := Fin n) (E := Fin m) (γ : ℝ) Δ (width L) *
        w / 16 := by
    change RationalCoverSchedule.Kstar L r Q *
      CurrentAdditive.QuarticSchedule.E27 Q η ≤ η * w / 16 at hKcheckQ
    have hh : (RationalCoverSchedule.Kstar L r Q : ℝ) *
        CurrentAdditive.QuarticSchedule.E27 Q η ≤
        (η : ℝ) * w / 16 := by
      simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_natCast,
        Rat.cast_ofNat] using cast_le hKcheckQ
    simpa only [RationalCoverSchedule.Kstar_real, hηq] using hh
  have hEcard : 0 < Fintype.card (Fin m) := by simpa using hE
  have hbridge : 80 * (L : ℝ) ≤ (Q : ℝ) *
      (deletionAllowance (V := Fin n) (E := Fin m) (γ : ℝ) Δ (width L) /
        (16 * (w : ℝ))) := by
    have hη : 0 < η := SourceRationalScheduleScratch.eta_pos
      (V := Fin n) (E := Fin m) L γ Δ hγ hΔ hEcard
    have hwpos : 0 < w := by dsimp [w, width27]; positivity
    have hδ : 0 < deltaU27 (V := Fin n) (E := Fin m) L γ Δ := by
      unfold deltaU27
      have hd : (0 : ℚ) < 16 * w :=
        mul_pos (by norm_num) (by exact_mod_cast hwpos)
      exact div_pos hη hd
    have hh := RestorationPublicQScratch.publicQ_meets L
      (deltaU27 (V := Fin n) (E := Fin m) L γ Δ) hδ
    have hhR := cast_le hh
    rw [← hηq]
    simpa only [RestorationPublicQScratch.threshold,
      deltaU27, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast,
      Rat.cast_ofNat, Q, Q27, w, Nat.cast_mul] using hhR
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hL
  · exact hinner
  · exact houter
  · exact hwide
  · exact href
  · exact hscale
  · exact hcount
  · exact hw
  · exact hw2
  · exact hQ
  · simpa only [Fintype.card_fin] using hsize
  · exact hηq
  · exact hquarterQ
  · exact hsmall
  · exact hfirst
  · exact hlast
  · simpa only [r, Q, w, η, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
      using hKcheck
  · exact hxsmall
  · exact hstar
  · exact hsmallwx
  · exact hmargin
  · exact hbridge

#print axioms guards_of_checks27

end Paper2.CurrentAdditive.QuarticScheduleGuards
