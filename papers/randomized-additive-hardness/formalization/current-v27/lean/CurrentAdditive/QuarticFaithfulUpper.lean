import CurrentAdditive.QuarticFaithfulSelectedEvent
import CurrentAdditive.QuarticScheduleGuards
import CurrentAdditive.QuarticSelectedUpper

/-! Every fixed tape of the repaired sampler is a restriction of the same
canonical recursive source. This file derives the unrestricted cost upper
bounds without using the old selector's zero-abort table. -/

namespace Paper2.GenericQuarticFaithful

open Paper2 SourceProfileParameters SourceRecursiveNoSampling
  Workspace.Types.CommComplexity CurrentAdditive.RandomizedSchedule
  Paper2.CurrentAdditive.QuarticConstructor
  Paper2.CurrentAdditive.QuarticScheduleGuards

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

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

theorem scheduled_faithful_all_cost {n m : ℕ} [NeZero n]
    (L Δ : ℕ) (γ : ℚ) (edge : Fin m → Bool → Fin n)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hm : 0 < m)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) L Δ γ)
    (k : ℕ) (bits : RecursiveSamplingMaterialization.TapeList (Fin n)
      (width L) (width L - 2) (outerWidth L)
      (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ)
      (LookupSeed.width L) k
      (rows27 n m L Δ γ k) (cols27 n m L Δ γ k)) :
    D (table27Faithful (NeZero.pos n) edge L Δ γ k hc bits).matrix ≤
      sourceCost L (4 * RestorationWidthScheduleScratch.ell L)
        (q27 (V := Fin n) (E := Fin m) L γ Δ) k := by
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
  let old := SourceConstruction.activity (CanonicalSourceLabels.itemOrder (width L) n)
    edge (by have := SourceProfiles.width_ge_four L; omega) rep hq
  let scan := SourceActiveRank.scanAtCanonical edge
    (by have := SourceProfiles.width_ge_four L; omega) hq
  have g := guards_of_checks27 L Δ γ hγ hΔ hm hc
  have hsize' : 2 * (Fintype.card (Fin n) + width L - 3) ≤ outerWidth L := by
    simpa only [Fintype.card_fin] using g.hsize
  have hbound := SourceIteration.selected_iteration_bounds
    (s := width L) (q₁ := width L - 2) (q₂ := outerWidth L)
    (w := width27 L) (Q := Q27 (V := Fin n) (E := Fin m) L γ Δ) L
    (CanonicalSourceLabels.itemOrder (width L) n) edge
    (by have := SourceProfiles.width_ge_four L; omega)
    rep hq ξold
    (exponent L) (outerExponent L) r q
    (by have := SourceProfiles.width_ge_four L; omega)
    rfl rfl g.hw g.hQ hsize' k
  have hC : LookupSeed.exponent L + 1 +
      k * (exponent L + exponent L + outerExponent L + r + q) + k =
      sourceCost L r q k := by
    dsimp [sourceCost]
    ring
  have hOldUpper : D (RecursiveEntries.matrix (LookupSeed.matrix (LookupSeed.width L))
      old ξold k) ≤ sourceCost L r q k := by
    change D (SourceIteration.matrix (q₁ := width L - 2)
      L (CanonicalSourceLabels.itemOrder (width L) n) edge
      (by have := SourceProfiles.width_ge_four L; omega) rep hq ξold k) ≤ _
    exact hbound.1.trans_eq hC
  have hScan : D (RecursiveEntries.matrix (LookupSeed.matrix (LookupSeed.width L))
      scan ξ k) ≤ sourceCost L r q k := by
    rw [CanonicalScannedSampler.scanned_matrix_D edge
      (by have := SourceProfiles.width_ge_four L; omega) hq
      (LookupSeed.matrix (LookupSeed.width L)) ξ k]
    exact hOldUpper
  obtain ⟨rows,cols,htab⟩ := table27Faithful_sampled
    (NeZero.pos n) edge L Δ γ k hc bits
  change D (table27Faithful (NeZero.pos n) edge L Δ γ k hc bits).matrix ≤ _
  rw [htab]
  rw [RecursiveEntries.table_eq_sampleMatrix]
  exact sample_D_le_of_le _ rows cols hScan

/-- Restriction bound for the repaired table, with no successful-tape
condition. The source-coordinate inverse appears only in this proof. -/
theorem scheduled_faithful_restriction {n m : ℕ} [NeZero n]
    (L Δ : ℕ) (γ : ℚ) (edge : Fin m → Bool → Fin n)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) L Δ γ)
    (k : ℕ) (bits : RecursiveSamplingMaterialization.TapeList (Fin n)
      (width L) (width L - 2) (outerWidth L)
      (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ)
      (LookupSeed.width L) k
      (rows27 n m L Δ γ k) (cols27 n m L Δ γ k)) :
    let rep := SourceRepetitionScratch.sourceRep L (Fin m)
    let hq := SourceRepetitionScratch.outerWidth_eq_sourceQ0_mul_rep
      L (Fin m) hc.1
    let ξ := CanonicalDefaultSource.canonicalDefaultTails L n
      (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ)
      (NeZero.pos n) (by unfold width27; positivity)
      (RestorationPublicQScratch.publicQ_pos _ _)
    D (table27Faithful (NeZero.pos n) edge L Δ γ k hc bits).matrix ≤
      D (RecursiveEntries.matrix (LookupSeed.matrix (LookupSeed.width L))
        (SourceConstruction.activity (CanonicalSourceLabels.itemOrder (width L) n)
          edge (by have := SourceProfiles.width_ge_four L; omega) rep hq)
        (ExecutableSourceCoordinateTransport.oldTails hq ξ) k) := by
  intro rep hq ξ
  let scan := SourceActiveRank.scanAtCanonical edge
    (by have := SourceProfiles.width_ge_four L; omega) hq
  obtain ⟨rows,cols,htab⟩ := table27Faithful_sampled
    (NeZero.pos n) edge L Δ γ k hc bits
  rw [htab, RecursiveEntries.table_eq_sampleMatrix]
  apply (sample_D_le _ rows cols).trans
  exact (CanonicalScannedSampler.scanned_matrix_D edge
    (by have := SourceProfiles.width_ge_four L; omega) hq
    (LookupSeed.matrix (LookupSeed.width L)) ξ k).le

theorem scheduled_faithful_yes_cost {n m : ℕ} [NeZero n]
    (L Δ : ℕ) (γ : ℚ) (edge : Fin m → Bool → Fin n)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hm : 0 < m)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) L Δ γ)
    (k : ℕ) (bits : RecursiveSamplingMaterialization.TapeList (Fin n)
      (width L) (width L - 2) (outerWidth L)
      (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ)
      (LookupSeed.width L) k
      (rows27 n m L Δ γ k) (cols27 n m L Δ γ k))
    (colour : Fin n → Fin 3)
    (proper : ∀ e, colour (edge e false) ≠ colour (edge e true)) :
    D (table27Faithful (NeZero.pos n) edge L Δ γ k hc bits).matrix ≤
      sourceBudget L (4 * RestorationWidthScheduleScratch.ell L)
        (q27 (V := Fin n) (E := Fin m) L γ Δ) k := by
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
  have g := guards_of_checks27 L Δ γ hγ hΔ hm hc
  have hsize' : 2 * (Fintype.card (Fin n) + width L - 3) ≤ outerWidth L := by
    simpa only [Fintype.card_fin] using g.hsize
  have hbound := SourceIteration.selected_iteration_bounds
    (s := width L) (q₁ := width L - 2) (q₂ := outerWidth L)
    (w := width27 L) (Q := Q27 (V := Fin n) (E := Fin m) L γ Δ) L
    (CanonicalSourceLabels.itemOrder (width L) n) edge
    (by have := SourceProfiles.width_ge_four L; omega)
    rep hq ξold
    (exponent L) (outerExponent L) r q
    (by have := SourceProfiles.width_ge_four L; omega)
    rfl rfl g.hw g.hQ hsize' k
  have hB : LookupSeed.exponent L + 1 +
      k * (exponent L + exponent L + outerExponent L + r + q) =
      sourceBudget L r q k := by
    dsimp [sourceBudget]
    ring
  have hOldYes : D (RecursiveEntries.matrix (LookupSeed.matrix (LookupSeed.width L))
      (SourceConstruction.activity (CanonicalSourceLabels.itemOrder (width L) n)
        edge (by have := SourceProfiles.width_ge_four L; omega) rep hq)
      ξold k) ≤ sourceBudget L r q k := by
    change D (SourceIteration.matrix (q₁ := width L - 2)
      L (CanonicalSourceLabels.itemOrder (width L) n) edge
      (by have := SourceProfiles.width_ge_four L; omega) rep hq ξold k) ≤ _
    exact (hbound.2.1 colour proper).trans_eq hB
  exact (scheduled_faithful_restriction L Δ γ edge hc k bits).trans hOldYes

#print axioms scheduled_faithful_all_cost
#print axioms scheduled_faithful_restriction
#print axioms scheduled_faithful_yes_cost

end Paper2.GenericQuarticFaithful
