import CurrentAdditive.QuarticScheduleGuards
import CurrentAdditive.QuarticConstructor

namespace Paper2.CurrentAdditive.QuarticConstructor

open SourceProfileParameters SourceSurvivingCollisions SourceRecursiveNoSampling
  Workspace.Types.CommComplexity CurrentAdditive.RandomizedSchedule

local instance (L : ℕ) : NeZero (width L) := ⟨by unfold width; positivity⟩
local instance (L : ℕ) : NeZero (outerWidth L) := ⟨by unfold outerWidth; positivity⟩
local instance (L : ℕ) : NeZero (width L - 2) := ⟨by
  have := width_admissible L
  omega⟩
local instance (L : ℕ) : NeZero (width27 L) := ⟨by unfold width27; positivity⟩
local instance (n m L Δ : ℕ) (γ : ℚ) :
    NeZero (Q27 (V := Fin n) (E := Fin m) L γ Δ) :=
  ⟨Nat.ne_of_gt (RestorationPublicQScratch.publicQ_pos _ _)⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
/-- The literal quartic scheduled table, on its canonical fair-bit tape,
has the v27 finite YES/NO success bounds at every recursive level. -/
theorem scheduled_table_finite_guarantees27
    {n m : ℕ} [NeZero n]
    (L Δ : ℕ) (γ : ℚ)
    (edge : Fin m → Bool → Fin n)
    (loopless : ∀ e, edge e false ≠ edge e true)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hE : 0 < m)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) L Δ γ)
    (k : ℕ) :
    let output := scheduledTable27 (NeZero.pos n) edge L Δ γ k hc
    (∀ bits, D (output bits).matrix ≤
      sourceCost L (4 * RestorationWidthScheduleScratch.ell L)
        (q27 (V := Fin n) (E := Fin m) L γ Δ) k) ∧
    (∀ colour : Fin n → Fin 3,
      (∀ e, colour (edge e false) ≠ colour (edge e true)) →
      ∀ bits, D (output bits).matrix ≤
        sourceBudget L (4 * RestorationWidthScheduleScratch.ell L)
          (q27 (V := Fin n) (E := Fin m) L γ Δ) k) ∧
    ((∀ colour : Fin n → Fin 3, (γ : ℝ) * m ≤
      ((Finset.univ.filter (fun e => colour (edge e false) =
        colour (edge e true))).card : ℝ)) →
      1 - (1 / 2 : ℝ) ^ 12 - (1 / 2 : ℝ) ^ 13 ≤
        (RecursiveSamplingMaterialization.tapeListLaw (Fin n) (width L)
          (width L - 2) (outerWidth L)
          (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ)
          (LookupSeed.width L) k
          (rows27 n m L Δ γ k) (cols27 n m L Δ γ k)).prob
          (fun bits => D (output bits).matrix =
            sourceCost L (4 * RestorationWidthScheduleScratch.ell L)
              (q27 (V := Fin n) (E := Fin m) L γ Δ) k) ∧
      1 - (1 / 2 : ℝ) ^ 11 ≤
        (RecursiveSamplingMaterialization.tapeListLaw (Fin n) (width L)
          (width L - 2) (outerWidth L)
          (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ)
          (LookupSeed.width L) k
          (rows27 n m L Δ γ k) (cols27 n m L Δ γ k)).prob
          (fun bits => D (output bits).matrix =
            sourceCost L (4 * RestorationWidthScheduleScratch.ell L)
              (q27 (V := Fin n) (E := Fin m) L γ Δ) k)) ∧
    (∀ bits, (output bits).bits.length =
      rows27 n m L Δ γ k * cols27 n m L Δ γ k) := by
  let η := SourceRationalScheduleScratch.eta (V := Fin n) (E := Fin m)
    L γ Δ
  have g := QuarticScheduleGuards.guards_of_checks27
    L Δ γ hγ hΔ hE hc
  have hq := SourceRepetitionScratch.outerWidth_eq_sourceQ0_mul_rep
    L (Fin m) hc.1
  have hγR : (0 : ℝ) < γ := by exact_mod_cast hγ
  have hKcheck :
      (1024 * (1 / 256 : ℝ) * RestorationCoverParameters.B2
        (Q27 (V := Fin n) (E := Fin m) L γ Δ) *
        ((4 * RestorationWidthScheduleScratch.ell L : ℕ) + 2) * width L) *
      CurrentAdditive.QuarticSchedule.E27
        (Q27 (V := Fin n) (E := Fin m) L γ Δ) η ≤
      deletionAllowance (V := Fin n) (E := Fin m) (γ : ℝ) Δ (width L) *
        width27 L / 16 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using g.hKcheck
  have h := CanonicalDefaultSource.selected_canonical_default_finite_guarantees27
    L g.hL edge loopless (SourceRepetitionScratch.sourceRep L (Fin m))
    Δ hΔ hq hdegree (γ : ℝ) hγR hE
    g.hinner g.houter g.hwide g.href g.hscale g.hcountSource
    (width27 L) (4 * RestorationWidthScheduleScratch.ell L)
    (Q27 (V := Fin n) (E := Fin m) L γ Δ)
    (q27 (V := Fin n) (E := Fin m) L γ Δ)
    g.hw g.hw2 g.hQ η g.hηq g.hquarter
    g.hsmall g.hfirst g.hlast hKcheck g.hxsmall g.hstar
    g.hsmallwx g.hmargin g.hbridge g.hsize k
  simpa only [scheduledTable27, rows27, cols27] using h

#print axioms scheduled_table_finite_guarantees27

end Paper2.CurrentAdditive.QuarticConstructor
