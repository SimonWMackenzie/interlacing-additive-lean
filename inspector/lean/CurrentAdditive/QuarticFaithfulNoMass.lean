import CurrentAdditive.QuarticFaithfulUpper
import CurrentAdditive.QuarticSourceNoSuccess

/-! NO success for the corrected first-member fallback sampler, at the
scheduled v27 graph source and on its actual selected fair-bit tape. -/

namespace Paper2.GenericQuarticFaithful

open Paper2 SourceMatrix SourceProfileParameters SourceRecursiveNoSampling
  SourceDeficiency SourceSurvivingCollisions
  Workspace.Types.CommComplexity CurrentAdditive.RandomizedSchedule
  Paper2.CurrentAdditive.QuarticConstructor
  Paper2.CurrentAdditive.QuarticScheduleGuards

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
set_option synthInstance.maxSize 65536

local instance (L : ℕ) : NeZero (width L) :=
  ⟨by unfold width; positivity⟩
local instance (L : ℕ) : NeZero (outerWidth L) :=
  ⟨by unfold outerWidth; positivity⟩
local instance (L : ℕ) : NeZero (width L - 2) :=
  ⟨by have := width_admissible L; omega⟩
local instance (L : ℕ) : NeZero (width27 L) :=
  ⟨by unfold width27; positivity⟩
local instance (n m L Δ : ℕ) (γ : ℚ) :
    NeZero (Q27 (V := Fin n) (E := Fin m) L γ Δ) :=
  ⟨Nat.ne_of_gt (RestorationPublicQScratch.publicQ_pos _ _)⟩

theorem scheduled_faithful_no_mass {n m : ℕ} [NeZero n]
    (Δ : ℕ) (γ : ℚ) (edge : Fin m → Bool → Fin n)
    (loopless : ∀ e, edge e false ≠ edge e true)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hm : 0 < m)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ)
    (k : ℕ)
    (gap : ∀ colour : Fin n → Fin 3, (γ : ℝ) * m ≤
      ((Finset.univ.filter (fun e => colour (edge e false) =
        colour (edge e true))).card : ℝ)) :
    let L := Nat.clog 2 n
    let exp := Paper2.CurrentAdditive.QuarticClassEndpoint.scheduledExperiment27Faithful
      (NeZero.pos n) edge Δ γ k hc
    letI : Fintype exp.output.Tape := exp.tapeFintype
    1 - (1 / 2 : ℝ) ^ 11 ≤ exp.tapeLaw.prob (fun bits =>
      D (table27Faithful (NeZero.pos n) edge L Δ γ k hc bits).matrix =
        sourceCost L (4 * RestorationWidthScheduleScratch.ell L)
          (q27 (V := Fin n) (E := Fin m) L γ Δ) k) := by
  intro L exp
  letI : Fintype exp.output.Tape := exp.tapeFintype
  let r := 4 * RestorationWidthScheduleScratch.ell L
  let q := q27 (V := Fin n) (E := Fin m) L γ Δ
  let rep := SourceRepetitionScratch.sourceRep L (Fin m)
  let hq := SourceRepetitionScratch.outerWidth_eq_sourceQ0_mul_rep
    L (Fin m) hc.1
  let ξ := CanonicalDefaultSource.canonicalDefaultTails L n
    (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ)
    (NeZero.pos n) (by unfold width27; positivity)
    (RestorationPublicQScratch.publicQ_pos _ _)
  let ξold := ExecutableSourceCoordinateTransport.oldTails hq ξ
  let H := sourceCost L r q k
  let hs := SourceProfiles.width_ge_four L
  let p := LookupSeed.width L
  let hp : 0 < p := by dsimp [p, LookupSeed.width]; positivity
  let mX := rows27 n m L Δ γ k
  let mY := cols27 n m L Δ γ k
  let τ := exp.tapeLaw
  let idealLaw := RecursiveSampling.sampleLaw (V := Fin n)
    (q₁ := width L - 2) (q₂ := outerWidth L)
    (w := width27 L) (Q := Q27 (V := Fin n) (E := Fin m) L γ Δ)
    hs (LookupSeed.rowLaw p) (LookupSeed.columnLaw p hp) k mX mY
  let old := RecursiveEntries.matrix (LookupSeed.matrix p)
    (SourceConstruction.activity (CanonicalSourceLabels.itemOrder (width L) n)
      edge (by have := hs; omega) rep hq) ξold k
  let scan := RecursiveEntries.matrix (LookupSeed.matrix p)
    (SourceActiveRank.scanAtCanonical edge (by have := hs; omega) hq) ξ k
  let print := fun bits : exp.output.Tape =>
    sourceRun27Faithful (NeZero.pos n) edge L Δ γ k hc bits
  let ideal (z :
      (Fin mY → RecursiveEntries.Column (Fin p → Bool) (Fin p)
        (SourceConstruction.Items (width L) (Fin n)) (width L)
        (width L - 2) (outerWidth L) (width27 L)
        (Q27 (V := Fin n) (E := Fin m) L γ Δ) k) ×
      (Fin mX → RecursiveEntries.Row (Fin p → Bool) (Fin p)
        (SourceConstruction.Items (width L) (Fin n)) (width L)
        (width L - 2) (outerWidth L) (width27 L)
        (Q27 (V := Fin n) (E := Fin m) L γ Δ) k)) :=
    sampleMatrix scan z.2 z.1
  have g := guards_of_checks27 L Δ γ hγ hΔ hm hc
  let η := SourceRationalScheduleScratch.eta (V := Fin n) (E := Fin m) L γ Δ
  have hγR : (0 : ℝ) < γ := by exact_mod_cast hγ
  have hm' : 0 < Fintype.card (Fin m) := by
    simpa only [Fintype.card_fin] using hm
  have gap' : ∀ colour : Fin n → Fin 3,
      (γ : ℝ) * Fintype.card (Fin m) ≤
      ((Finset.univ.filter (fun e => colour (edge e false) =
        colour (edge e true))).card : ℝ) := by
    simpa only [Fintype.card_fin] using gap
  have hsize' : 2 * (Fintype.card (Fin n) + width L - 3) ≤ outerWidth L := by
    simpa only [Fintype.card_fin] using g.hsize
  have hKcheck :
      (1024 * (1 / 256 : ℝ) * RestorationCoverParameters.B2
        (Q27 (V := Fin n) (E := Fin m) L γ Δ) *
        (r + 2) * width L) *
      CurrentAdditive.QuarticSchedule.E27
        (Q27 (V := Fin n) (E := Fin m) L γ Δ) η ≤
      deletionAllowance (V := Fin n) (E := Fin m) (γ : ℝ) Δ (width L) *
        width27 L / 16 := by
    simpa only [r, η, Nat.cast_mul, Nat.cast_ofNat] using g.hKcheck
  have hbadOld : idealLaw.toFiniteLaw.prob
      (fun z => D (sampleMatrix old z.2 z.1) < H) ≤ (1 / 2 : ℝ) ^ 12 := by
    exact SourceRecursiveNoSampling.selected_ideal_bad_le27 L g.hL
      (CanonicalSourceLabels.itemOrder (width L) n)
      edge loopless rep Δ hΔ hq hdegree (γ : ℝ) hγR hm' gap'
      g.hinner g.houter g.hwide g.href g.hscale g.hcountSource
      (width27 L) r (Q27 (V := Fin n) (E := Fin m) L γ Δ) q
      g.hw g.hw2 g.hQ η g.hηq g.hquarter
      g.hsmall g.hfirst g.hlast hKcheck g.hxsmall g.hstar
      g.hsmallwx g.hmargin g.hbridge hsize' ξold k
  have hbadScan : idealLaw.toFiniteLaw.prob
      (fun z => D (ideal z) < H) ≤ (1 / 2 : ℝ) ^ 12 := by
    have hid := CanonicalScannedSampler.scanned_ideal_table_event edge hs hq
      p hp ξ k mX mY {M | D M < H}
    change idealLaw.toFiniteLaw.prob
      (fun z => D (sampleMatrix old z.2 z.1) < H) =
      idealLaw.toFiniteLaw.prob (fun z => D (ideal z) < H) at hid
    rw [← hid]
    exact hbadOld
  have hcouple : |τ.prob (fun bits => D (print bits) < H) -
      idealLaw.toFiniteLaw.prob (fun z => D (ideal z) < H)| ≤
      (1 / 2 : ℝ) ^ 13 := by
    simpa only [τ, idealLaw, print, ideal, hs, p, mX, mY, H] using
      scheduled_selected_matrix_event_error (NeZero.pos n) edge Δ γ k hc
        {M | D M < H}
  have hupper : ∀ bits, D (print bits) ≤ H := by
    intro bits
    have hmatrix : (table27Faithful (NeZero.pos n) edge L Δ γ k hc bits).matrix =
        print bits := by
      funext i j
      exact table27Faithful_entry (NeZero.pos n) edge L Δ γ k hc bits i j
    rw [← hmatrix]
    exact scheduled_faithful_all_cost L Δ γ edge hγ hΔ hm hc k bits
  have hstrong := SourceRecursiveNoSampling.exact_cost_of_bad_event_bound
    τ idealLaw.toFiniteLaw print ideal D H
    ((1 / 2 : ℝ) ^ 12) ((1 / 2 : ℝ) ^ 13)
    hupper hbadScan hcouple
  have hmatrix : ∀ bits,
      (table27Faithful (NeZero.pos n) edge L Δ γ k hc bits).matrix =
        print bits := by
    intro bits
    funext i j
    exact table27Faithful_entry (NeZero.pos n) edge L Δ γ k hc bits i j
  have hevent : τ.prob (fun bits => D (print bits) = H) =
      τ.prob (fun bits => D (table27Faithful
        (NeZero.pos n) edge L Δ γ k hc bits).matrix = H) := by
    apply congrArg
    funext bits
    rw [hmatrix]
  rw [← hevent]
  norm_num at hstrong ⊢
  linarith

#print axioms scheduled_faithful_no_mass

end Paper2.GenericQuarticFaithful
