import Paper2.PublicScheduleChecks
import Paper2.WidthCoversTStar
import Paper2.SourceSizeCutoff
import Paper2.KstarCutoff
import Paper2.AllowanceSmallness

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

/-! Assembly of the literal public arithmetic checks, with no assumed check. -/

namespace Paper2.CompletePublicScheduleScratch

open SourceProfileParameters

variable {V E : Type*} [Fintype V] [Nonempty V] [Fintype E]

/-- Maximum of separately proved effective thresholds. -/
def cutoff (Δ : ℕ) (γ : ℚ) : ℕ :=
  max Paper2.SourceSmallnessSchedule.cutoff
    (max (SourceSizeCutoffScratch.sourceCutoff Δ γ)
      (max (WidthCoversTStar.cutoff Δ γ)
        (max (ExceptionalCutoffScratch.cutoff Δ γ)
          (max (ExceptionalCutoffScratch.kCutoff Δ γ)
            (max (ParameterCutoff.overheadCutoff Δ γ)
              (AllowanceSmallnessScratch.cutoff Δ γ))))))

private theorem smallness_cutoff_le (L Δ : ℕ) (γ : ℚ)
    (hL : cutoff Δ γ ≤ L) : SourceSmallnessSchedule.cutoff ≤ L :=
  (le_max_left _ _).trans hL

private theorem source_cutoff_le (L Δ : ℕ) (γ : ℚ)
    (hL : cutoff Δ γ ≤ L) :
    SourceSizeCutoffScratch.sourceCutoff Δ γ ≤ L := by
  simp only [cutoff, max_le_iff] at hL
  exact hL.2.1

private theorem tstar_cutoff_le (L Δ : ℕ) (γ : ℚ)
    (hL : cutoff Δ γ ≤ L) : WidthCoversTStar.cutoff Δ γ ≤ L := by
  simp only [cutoff, max_le_iff] at hL
  exact hL.2.2.1

private theorem exception_cutoff_le (L Δ : ℕ) (γ : ℚ)
    (hL : cutoff Δ γ ≤ L) : ExceptionalCutoffScratch.cutoff Δ γ ≤ L := by
  simp only [cutoff, max_le_iff] at hL
  exact hL.2.2.2.1

private theorem k_cutoff_le (L Δ : ℕ) (γ : ℚ)
    (hL : cutoff Δ γ ≤ L) : ExceptionalCutoffScratch.kCutoff Δ γ ≤ L := by
  simp only [cutoff, max_le_iff] at hL
  exact hL.2.2.2.2.1

private theorem overhead_cutoff_le (L Δ : ℕ) (γ : ℚ)
    (hL : cutoff Δ γ ≤ L) : ParameterCutoff.overheadCutoff Δ γ ≤ L := by
  simp only [cutoff, max_le_iff] at hL
  exact hL.2.2.2.2.2.1

private theorem allowance_cutoff_le (L Δ : ℕ) (γ : ℚ)
    (hL : cutoff Δ γ ≤ L) : AllowanceSmallnessScratch.cutoff Δ γ ≤ L := by
  simp only [cutoff, max_le_iff] at hL
  exact hL.2.2.2.2.2.2

theorem all_large_checks (edge : E → Bool → V)
    (L Δ : ℕ) (γ : ℚ)
    (hL : cutoff Δ γ ≤ L)
    (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hsize : Fintype.card V ≤ 2 ^ L) :
    Checks (V := V) (E := E) L Δ γ := by
  let s := width L
  let q₂ := outerWidth L
  let w := RestorationWidthScheduleScratch.width L
  let Q := SourceOverheadBounds.actualQ (V := V) (E := E) L γ Δ
  let η := SourceRationalScheduleScratch.eta (V := V) (E := E) L γ Δ
  have hS := smallness_cutoff_le L Δ γ hL
  have hsource := source_cutoff_le L Δ γ hL
  have h16 := SourceSmallnessSchedule.sixteen_le L hS
  have hwidth := (SourceSizeCutoffScratch.both_source_size_guards L Δ γ hγ hsource).1
  have hwitness := (SourceSizeCutoffScratch.both_source_size_guards L Δ γ hγ hsource).2
  have hallow := AllowanceSmallnessScratch.allowance_checks (V := V) (E := E)
    edge L Δ γ hγ hΔ hincident hdegree (allowance_cutoff_le L Δ γ hL)
  dsimp [Checks]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact SourceCoordinateScheduleScratch.coordinate_admissible edge L Δ
      hdegree hsize hwidth
  · exact SourceCoordinateScheduleScratch.item_size_admissible L h16
      (Fintype.card V) hsize
  · have h := SourceSmallnessSchedule.source_scale L hS
    apply (Rat.cast_le (K := ℝ)).mp
    norm_num only [Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat,
      rhoQ_cast]
    exact h
  · have h := SourceSmallnessSchedule.inner_small L hS
    apply (Rat.cast_le (K := ℝ)).mp
    norm_num only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_div,
      Rat.cast_ofNat, rhoQ_cast]
    exact h
  · have h := SourceSmallnessSchedule.outer_small L hS
    apply (Rat.cast_le (K := ℝ)).mp
    norm_num only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_div,
      Rat.cast_ofNat, xQ_cast]
    exact h
  · have h := SourceSmallnessSchedule.reference_small L hS
    apply (Rat.cast_le (K := ℝ)).mp
    norm_num only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_div,
      Rat.cast_ofNat, xQ_cast]
    exact h
  · have h := SourceSmallnessSchedule.restoration_small L hS
    apply (Rat.cast_le (K := ℝ)).mp
    norm_num only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_div,
      Rat.cast_ofNat, xQ_cast]
    exact h
  · have h := SourceSmallnessSchedule.outer_density L
    apply (Rat.cast_le (K := ℝ)).mp
    norm_num only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_div,
      Rat.cast_ofNat]
    exact h
  · exact hwitness
  · have h := SourceSmallnessSchedule.two_outer_small L hS
    apply (Rat.cast_le (K := ℝ)).mp
    norm_num only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_div,
      Rat.cast_ofNat, xQ_cast]
    exact h
  · have h := SourceSmallnessSchedule.two_reference_small L hS
    apply (Rat.cast_le (K := ℝ)).mp
    norm_num only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_div,
      Rat.cast_ofNat, xQ_cast]
    exact h
  · exact WidthCoversTStar.four_tStar_le_width edge L Δ γ
      (tstar_cutoff_le L Δ γ hL) hγ hΔ hincident hdegree
  · have h := hallow.1
    apply (Rat.cast_lt (K := ℝ)).mp
    norm_num only [Rat.cast_add, Rat.cast_mul, Rat.cast_natCast,
      Rat.cast_div, Rat.cast_ofNat, xQ_cast, gQ]
    simpa only [show (16 : ℝ) * (127 / 128) = 127 / 8 by norm_num] using h
  · have h := hallow.2.1
    apply (Rat.cast_le (K := ℝ)).mp
    norm_num only [Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast,
      Rat.cast_div, Rat.cast_ofNat, xQ_cast, gQ]
    simpa only [show (16 : ℝ) * (127 / 128) = 127 / 8 by norm_num] using h
  · have h := RestorationWidthScheduleScratch.restoration_scale_guard L h16
    apply (Rat.cast_le (K := ℝ)).mp
    norm_num only [Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast,
      Rat.cast_div, Rat.cast_ofNat, xQ_cast]
    exact h
  · have h := hallow.2.2.1
    apply (Rat.cast_le (K := ℝ)).mp
    norm_num only [Rat.cast_mul, Rat.cast_natCast,
      Rat.cast_div, Rat.cast_ofNat, xQ_cast, muQ]
    simpa only [show (4 : ℝ) * (1 / 256) = 1 / 64 by norm_num] using h
  · have h := hallow.2.2.2
    apply (Rat.cast_le (K := ℝ)).mp
    norm_num only [Rat.cast_mul, Rat.cast_natCast,
      Rat.cast_div, Rat.cast_ofNat, muQ]
    simpa only [show (4 : ℝ) * (1 / 256) = 1 / 64 by norm_num] using h
  · exact ExceptionalCutoffScratch.actual_exceptional_quarter_check edge L Δ γ
      (exception_cutoff_le L Δ γ hL) hγ hΔ hincident hdegree
  · exact ExceptionalCutoffScratch.actual_kCheck edge L Δ γ
      (k_cutoff_le L Δ γ hL) hγ hΔ hincident hdegree
  · exact ParameterCutoff.actual_overhead_le_seven_L edge L Δ γ
      (overhead_cutoff_le L Δ γ hL) hγ hΔ hincident hdegree
  · exact h16
  · exact SourceSmallnessSchedule.seed_depth L hS


end Paper2.CompletePublicScheduleScratch

