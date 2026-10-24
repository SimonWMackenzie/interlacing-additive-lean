import Paper2.SourceSurvivingCollisionsItems
import Paper2.SourceProfileParameters
import Paper2.RestorationPublicQ

/-!
Rational form of the literal v12 Appendix C source parameters.  The
input gamma is rational; no claim is made that an arbitrary real gap is.
-/

namespace Paper2.SourceRationalScheduleScratch

open SourceProfileParameters SourceSurvivingCollisions RestorationPublicQScratch

variable {V E : Type*} [Fintype V] [Nonempty V] [Fintype E]

def vertexTolerance (gamma : ℚ) (Delta : ℕ) : ℚ :=
  gamma * Fintype.card E / (2 * Delta * Fintype.card V)

def witnessDensity (gamma : ℚ) : ℚ := gamma / 24

def eta (L : ℕ) (gamma : ℚ) (Delta : ℕ) : ℚ :=
  min (min 1 (vertexTolerance (V := V) (E := E) gamma Delta))
    ((1 / 256) * witnessDensity gamma) / (65536 * width L)

def restorationWidth (L : ℕ) : ℕ :=
  2 ^ ((Nat.clog 2 (L + 1)) ^ 2)

def deltaU (L : ℕ) (gamma : ℚ) (Delta : ℕ) : ℚ :=
  eta (V := V) (E := E) L gamma Delta / (16 * restorationWidth L)

def publicQ (L : ℕ) (gamma : ℚ) (Delta : ℕ) : ℕ :=
  RestorationPublicQScratch.publicQ L (deltaU (V := V) (E := E) L gamma Delta)

theorem vertexTolerance_cast (gamma : ℚ) (Delta : ℕ) :
    ((vertexTolerance (V := V) (E := E) gamma Delta : ℚ) : ℝ) =
      SourceSurvivingCollisions.vertexTolerance (V := V) (E := E)
        (gamma : ℝ) Delta := by
  simp [vertexTolerance, SourceSurvivingCollisions.vertexTolerance]

theorem witnessDensity_cast (gamma : ℚ) :
    ((witnessDensity gamma : ℚ) : ℝ) =
      SourceSurvivingCollisions.witnessDensity (gamma : ℝ) := by
  simp [witnessDensity, SourceSurvivingCollisions.witnessDensity]

theorem eta_cast (L : ℕ) (gamma : ℚ) (Delta : ℕ) :
    ((eta (V := V) (E := E) L gamma Delta : ℚ) : ℝ) =
      SourceSurvivingCollisions.deletionAllowance (V := V) (E := E)
        (gamma : ℝ) Delta (width L) := by
  simp only [eta, SourceSurvivingCollisions.deletionAllowance,
    SourceDeletionParameters.eta, Rat.cast_div, Rat.cast_min,
    Rat.cast_mul, Rat.cast_one, Rat.cast_ofNat, Rat.cast_natCast,
    vertexTolerance_cast, witnessDensity_cast]

theorem deltaU_cast (L : ℕ) (gamma : ℚ) (Delta : ℕ) :
    ((deltaU (V := V) (E := E) L gamma Delta : ℚ) : ℝ) =
      SourceSurvivingCollisions.deletionAllowance (V := V) (E := E)
        (gamma : ℝ) Delta (width L) / (16 * restorationWidth L) := by
  simp [deltaU, eta_cast]

theorem vertexTolerance_pos (gamma : ℚ) (Delta : ℕ)
    (hgamma : 0 < gamma) (hDelta : 0 < Delta)
    (hE : 0 < Fintype.card E) :
    0 < vertexTolerance (V := V) (E := E) gamma Delta := by
  unfold vertexTolerance
  have hV : 0 < Fintype.card V := Fintype.card_pos
  positivity

theorem witnessDensity_pos (gamma : ℚ) (hgamma : 0 < gamma) :
    0 < witnessDensity gamma := by
  unfold witnessDensity
  positivity

theorem eta_pos (L : ℕ) (gamma : ℚ) (Delta : ℕ)
    (hgamma : 0 < gamma) (hDelta : 0 < Delta)
    (hE : 0 < Fintype.card E) :
    0 < eta (V := V) (E := E) L gamma Delta := by
  unfold eta
  have hvt := vertexTolerance_pos (V := V) (E := E)
    gamma Delta hgamma hDelta hE
  have hwd := witnessDensity_pos gamma hgamma
  have hw : 0 < width L := by unfold width; positivity
  apply div_pos
  · exact lt_min (lt_min (by norm_num) hvt) (by positivity)
  · exact mul_pos (by norm_num : (0 : ℚ) < 65536)
      (by exact_mod_cast hw)

theorem deltaU_pos (L : ℕ) (gamma : ℚ) (Delta : ℕ)
    (hgamma : 0 < gamma) (hDelta : 0 < Delta)
    (hE : 0 < Fintype.card E) :
    0 < deltaU (V := V) (E := E) L gamma Delta := by
  unfold deltaU
  have he := eta_pos (V := V) (E := E) L gamma Delta hgamma hDelta hE
  have hw : 0 < restorationWidth L := by unfold restorationWidth; positivity
  positivity

theorem eta_le_inverse_65536 (L : ℕ) (gamma : ℚ) (Delta : ℕ) :
    eta (V := V) (E := E) L gamma Delta ≤ 1 / 65536 := by
  unfold eta
  have hs : (1 : ℚ) ≤ (width L : ℚ) := by
    exact_mod_cast (show 0 < width L by unfold width; positivity)
  have hm : min (min (1 : ℚ) (vertexTolerance (V := V) (E := E) gamma Delta))
      ((1 / 256) * witnessDensity gamma) ≤ 1 :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hd : (0 : ℚ) < 65536 * width L := by positivity
  apply (div_le_iff₀ hd).2
  nlinarith

theorem deltaU_le_one (L : ℕ) (gamma : ℚ) (Delta : ℕ) :
    deltaU (V := V) (E := E) L gamma Delta ≤ 1 := by
  unfold deltaU
  have he := eta_le_inverse_65536 (V := V) (E := E) L gamma Delta
  have hw : (1 : ℚ) ≤ restorationWidth L := by
    exact_mod_cast (show 0 < restorationWidth L by unfold restorationWidth; positivity)
  have hd : (0 : ℚ) < 16 * restorationWidth L := by positivity
  apply (div_le_iff₀ hd).2
  nlinarith

theorem manuscript_powTwo_domain (L : ℕ) (hL : 1 ≤ L)
    (gamma : ℚ) (Delta : ℕ)
    (hgamma : 0 < gamma) (hDelta : 0 < Delta)
    (hE : 0 < Fintype.card E) :
    1 ≤ RestorationPublicQScratch.threshold L
      (deltaU (V := V) (E := E) L gamma Delta) := by
  have hd := deltaU_pos (V := V) (E := E) L gamma Delta hgamma hDelta hE
  have hu := deltaU_le_one (V := V) (E := E) L gamma Delta
  unfold RestorationPublicQScratch.threshold
  apply (le_div_iff₀ hd).2
  have h80 : (1 : ℚ) ≤ (80 * L : ℕ) := by
    exact_mod_cast (show 1 ≤ 80 * L by omega)
  simpa using hu.trans h80

theorem publicQ_real_schedule (L : ℕ) (gamma : ℚ) (Delta : ℕ) :
    publicQ (V := V) (E := E) L gamma Delta =
      SourcePadding.powTwoCeil (Nat.ceil
        ((80 * (L : ℝ)) /
          (SourceSurvivingCollisions.deletionAllowance (V := V) (E := E)
            (gamma : ℝ) Delta (width L) / (16 * restorationWidth L)))) := by
  unfold publicQ
  rw [RestorationPublicQScratch.publicQ_real_schedule]
  rw [deltaU_cast]

theorem publicQ_meets_real (L : ℕ) (gamma : ℚ) (Delta : ℕ)
    (hgamma : 0 < gamma) (hDelta : 0 < Delta)
    (hE : 0 < Fintype.card E) :
    (80 * L : ℕ) ≤ (publicQ (V := V) (E := E) L gamma Delta : ℝ) *
      (SourceSurvivingCollisions.deletionAllowance (V := V) (E := E)
        (gamma : ℝ) Delta (width L) / (16 * restorationWidth L)) := by
  have hd := deltaU_pos (V := V) (E := E) L gamma Delta hgamma hDelta hE
  have h := RestorationPublicQScratch.publicQ_meets L
    (deltaU (V := V) (E := E) L gamma Delta) hd
  have hr : ((80 * L : ℕ) : ℝ) ≤
      ((RestorationPublicQScratch.publicQ L
        (deltaU (V := V) (E := E) L gamma Delta) : ℕ) : ℝ) *
        ((deltaU (V := V) (E := E) L gamma Delta : ℚ) : ℝ) := by
    exact_mod_cast h
  simpa only [publicQ, deltaU_cast] using hr

#print axioms vertexTolerance_cast
#print axioms eta_cast
#print axioms deltaU_cast
#print axioms deltaU_pos
#print axioms eta_le_inverse_65536
#print axioms manuscript_powTwo_domain
#print axioms publicQ_real_schedule
#print axioms publicQ_meets_real

end Paper2.SourceRationalScheduleScratch
