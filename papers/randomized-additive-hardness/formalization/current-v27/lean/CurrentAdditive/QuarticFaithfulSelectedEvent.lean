import CurrentAdditive.QuarticFaithfulLaw
import CurrentAdditive.GenericSamplerFallbackTapeList

/-! The all-tape coupling estimate for the new selected v27 table. This is
about the selected output itself, including every exhausted-draw tape. -/

namespace Paper2.GenericQuarticFaithful

open Paper2
open Paper2.SourceProfileParameters
open Paper2.CurrentAdditive.QuarticConstructor
open CurrentAdditive.RandomizedSchedule

set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

local instance (L : ℕ) : NeZero (width L) :=
  ⟨by unfold width; positivity⟩
local instance (L : ℕ) : NeZero (width L - 2) :=
  ⟨by have := width_admissible L; omega⟩
local instance (L : ℕ) : NeZero (outerWidth L) :=
  ⟨by unfold outerWidth; positivity⟩
local instance (L : ℕ) : NeZero (width27 L) :=
  ⟨by unfold width27; positivity⟩
local instance {n m : ℕ} (L Δ : ℕ) (γ : ℚ) :
    NeZero (Q27 (V := Fin n) (E := Fin m) L γ Δ) :=
  ⟨Nat.ne_of_gt (RestorationPublicQScratch.publicQ_pos _ _)⟩

private def activity27 {n m : ℕ} (edge : Fin m → Bool → Fin n)
    (L Δ : ℕ) (γ : ℚ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) L Δ γ) :=
  SourceActiveRank.scanAtCanonical edge
    (by have := SourceProfiles.width_ge_four L; omega)
    (SourceRepetitionScratch.outerWidth_eq_sourceQ0_mul_rep
      L (Fin m) hc.1)

private def tails27 {n m : ℕ} (hn : 0 < n)
    (L Δ : ℕ) (γ : ℚ) :=
  CanonicalDefaultSource.canonicalDefaultTails L n
    (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ)
    hn (by unfold width27; positivity)
    (by exact RestorationPublicQScratch.publicQ_pos _ _)

/-- On the actual good-branch selected tape, the event probability for the
new table bytes differs from independent ideal sampling by at most `2^-13`.
The table is the new per-draw fallback table, not the old zero-abort one. -/
theorem scheduled_selected_bits_event_error {n m : ℕ} [NeZero n] (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ)
    (E : Set (List Bool)) :
    let L := Nat.clog 2 n
    let exp := Paper2.CurrentAdditive.QuarticClassEndpoint.scheduledExperiment27Faithful
        hn edge Δ γ k hc
    letI : Fintype exp.output.Tape := exp.tapeFintype
    |exp.tapeLaw.prob
      (fun t => ((scheduledOutput27Faithful hn edge Δ γ k hc).table t).bits ∈ E) -
      (RecursiveSampling.sampleLaw (V := Fin n)
        (q₁ := width L - 2) (q₂ := outerWidth L)
        (w := width27 L)
        (Q := Q27 (V := Fin n) (E := Fin m) L γ Δ)
        (SourceProfiles.width_ge_four L)
        (LookupSeed.rowLaw (LookupSeed.width L))
        (LookupSeed.columnLaw (LookupSeed.width L)
          (by unfold LookupSeed.width; positivity))
        k (rows27 n m L Δ γ k) (cols27 n m L Δ γ k)).toFiniteLaw.prob
      (fun z => (YaoMaterialization.tabulate
        (sampleMatrix
          (RecursiveEntries.matrix (LookupSeed.matrix (LookupSeed.width L))
            (activity27 edge L Δ γ hc) (tails27 (m := m) hn L Δ γ) k)
          z.2 z.1)).bits ∈ E)| ≤ (1 / 2 : ℝ) ^ 13 := by
  intro L exp
  letI : Fintype exp.output.Tape := exp.tapeFintype
  have h := Paper2.GenericSamplerFallbackTapeList.materializeTapeList_bits_event_error
    (finCongr (Fintype.card_fin n))
    (SourceProfiles.width_ge_four L) (LookupSeed.width L)
    (by unfold LookupSeed.width; positivity)
    (activity27 edge L Δ γ hc) (tails27 (m := m) hn L Δ γ)
    k (rows27 n m L Δ γ k) (cols27 n m L Δ γ k) E
  simpa only [Paper2.CurrentAdditive.QuarticClassEndpoint.scheduledExperiment27Faithful,
    scheduledOutput27Faithful, table27Faithful,
    GenericSamplerFallbackTapeList.materializeTapeList,
    sourceRun27Faithful, activity27, tails27,
    RecursiveSamplingMaterialization.tapeListLaw] using h

/-- The corresponding comparison for matrix events is used by the NO gap.
It is stated on the actual recursively evaluated matrix before row-major
serialization, so communication cost is measured on the same object. -/
theorem scheduled_selected_matrix_event_error {n m : ℕ} [NeZero n] (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ)
    (E : Set (Fin (rows27 n m (Nat.clog 2 n) Δ γ k) →
      Fin (cols27 n m (Nat.clog 2 n) Δ γ k) → Bool)) :
    let L := Nat.clog 2 n
    let exp := Paper2.CurrentAdditive.QuarticClassEndpoint.scheduledExperiment27Faithful
      hn edge Δ γ k hc
    letI : Fintype exp.output.Tape := exp.tapeFintype
    |exp.tapeLaw.prob
      (fun bits => sourceRun27Faithful hn edge L Δ γ k hc bits ∈ E) -
      (RecursiveSampling.sampleLaw (V := Fin n)
        (q₁ := width L - 2) (q₂ := outerWidth L)
        (w := width27 L)
        (Q := Q27 (V := Fin n) (E := Fin m) L γ Δ)
        (SourceProfiles.width_ge_four L)
        (LookupSeed.rowLaw (LookupSeed.width L))
        (LookupSeed.columnLaw (LookupSeed.width L)
          (by unfold LookupSeed.width; positivity))
        k (rows27 n m L Δ γ k) (cols27 n m L Δ γ k)).toFiniteLaw.prob
      (fun z => sampleMatrix
        (RecursiveEntries.matrix (LookupSeed.matrix (LookupSeed.width L))
          (activity27 edge L Δ γ hc) (tails27 (m := m) hn L Δ γ) k)
        z.2 z.1 ∈ E)| ≤ (1 / 2 : ℝ) ^ 13 := by
  intro L exp
  letI : Fintype exp.output.Tape := exp.tapeFintype
  have h := Paper2.GenericSamplerFallbackEvent.run_event_error
    (finCongr (Fintype.card_fin n))
    (SourceProfiles.width_ge_four L) (LookupSeed.width L)
    (by unfold LookupSeed.width; positivity)
    (activity27 edge L Δ γ hc) (tails27 (m := m) hn L Δ γ)
    k (rows27 n m L Δ γ k) (cols27 n m L Δ γ k) E
  dsimp only [Paper2.RecursiveSamplingExecution.tapeLaw] at h
  rw [← RecursiveSamplingTape.serializedTapeLaw_prob _ _ _
    (fun t => GenericSamplerFallbackTable.run
      (finCongr (Fintype.card_fin n))
      (SourceProfiles.width_ge_four L) (LookupSeed.width L)
      (by unfold LookupSeed.width; positivity)
      (activity27 edge L Δ γ hc) (tails27 (m := m) hn L Δ γ)
      k (rows27 n m L Δ γ k) (cols27 n m L Δ γ k) t ∈ E)] at h
  simpa only [Paper2.CurrentAdditive.QuarticClassEndpoint.scheduledExperiment27Faithful,
    scheduledOutput27Faithful, sourceRun27Faithful,
    RecursiveSamplingMaterialization.tapeListLaw,
    activity27, tails27] using h

#print axioms scheduled_selected_bits_event_error
#print axioms scheduled_selected_matrix_event_error

end Paper2.GenericQuarticFaithful
