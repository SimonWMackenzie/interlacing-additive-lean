import CurrentAdditive.RandomizedQuarticSchedule
import Paper2.TotalFiniteConstructor
import Paper2.AModelEstimator

/-! Literal v27 constructor transfer. The scheduled branch prints the
canonical capped source with the quartic width and the new public cover;
the old v12 selector is not reinterpreted. Probability and complexity
claims are deliberately separate from this output identity. -/

namespace Paper2.CurrentAdditive.QuarticConstructor

open SourceProfileParameters SourceRecursiveNoSampling
  Workspace.Types.CommComplexity YaoMaterialization
open CurrentAdditive.RandomizedSchedule

instance checks27_decidable (n m L Δ : ℕ) (γ : ℚ) :
    Decidable (CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) L Δ γ) := by
  unfold CurrentAdditive.QuarticSchedule.Checks27
    CompletePublicScheduleScratch.rhoQ CompletePublicScheduleScratch.xQ
    CompletePublicScheduleScratch.gQ CompletePublicScheduleScratch.muQ
    CurrentAdditive.QuarticSchedule.quarterCheck27Prop
    CurrentAdditive.QuarticSchedule.kCheck27Prop
  dsimp only
  letI : Decidable (SourceRepetitionScratch.coordinateAdmissible L (Fin m)) := by
    unfold SourceRepetitionScratch.coordinateAdmissible
    infer_instance
  infer_instance

private theorem width27_pos (L : ℕ) : 0 < width27 L := by
  unfold width27
  positivity

private theorem Q27_pos (n m L Δ : ℕ) (γ : ℚ) :
    0 < Q27 (V := Fin n) (E := Fin m) L γ Δ := by
  unfold Q27
  exact RestorationPublicQScratch.publicQ_pos _ _

/-- The new public dimensions. -/
def rows27 (n m L Δ : ℕ) (γ : ℚ) (k : ℕ) : ℕ :=
  sourceRows L (4 * RestorationWidthScheduleScratch.ell L)
    (q27 (V := Fin n) (E := Fin m) L γ Δ) k

def cols27 (n m L Δ : ℕ) (γ : ℚ) (k : ℕ) : ℕ :=
  sourceCols L (4 * RestorationWidthScheduleScratch.ell L)
    (q27 (V := Fin n) (E := Fin m) L γ Δ) k

/-- The actual v27 scheduled row-major table for a literal fair-bit tape. -/
def scheduledTable27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (L Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) L Δ γ)
    (bits : RecursiveSamplingMaterialization.TapeList (Fin n)
      (width L) (width L - 2) (outerWidth L)
      (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ)
      (LookupSeed.width L) k
      (rows27 n m L Δ γ k) (cols27 n m L Δ γ k)) :
    SerializedTable (rows27 n m L Δ γ k) (cols27 n m L Δ γ k) :=
  CanonicalDefaultSource.canonicalSourceOutput L edge
    (SourceRepetitionScratch.sourceRep L (Fin m))
    (SourceRepetitionScratch.outerWidth_eq_sourceQ0_mul_rep
      L (Fin m) hc.1)
    (width27 L) (4 * RestorationWidthScheduleScratch.ell L)
    (Q27 (V := Fin n) (E := Fin m) L γ Δ)
    (q27 (V := Fin n) (E := Fin m) L γ Δ)
    hn (width27_pos L) (Q27_pos n m L Δ γ) k bits

/-- The actual capped matrix whose entries are written by `scheduledTable27`.
It includes the same canonical scan, default tails and parsed fair-bit tape. -/
def sourceRun27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (L Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) L Δ γ)
    (bits : RecursiveSamplingMaterialization.TapeList (Fin n)
      (width L) (width L - 2) (outerWidth L)
      (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ)
      (LookupSeed.width L) k
      (rows27 n m L Δ γ k) (cols27 n m L Δ γ k)) :
    Fin (rows27 n m L Δ γ k) → Fin (cols27 n m L Δ γ k) → Bool := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  letI : NeZero (width L) := ⟨by unfold width; positivity⟩
  letI : NeZero (outerWidth L) := ⟨by unfold outerWidth; positivity⟩
  letI : NeZero (width L - 2) := ⟨by
    have := width_admissible L
    omega⟩
  letI : NeZero (width27 L) := ⟨Nat.ne_of_gt (width27_pos L)⟩
  letI : NeZero (Q27 (V := Fin n) (E := Fin m) L γ Δ) :=
    ⟨Nat.ne_of_gt (Q27_pos n m L Δ γ)⟩
  exact RecursiveSamplingExecution.run
    (finCongr (Fintype.card_fin n))
    (SourceProfiles.width_ge_four L) (LookupSeed.width L)
    (by unfold LookupSeed.width; positivity)
    (SourceActiveRank.scanAtCanonical edge (by
      have := SourceProfiles.width_ge_four L
      omega)
      (SourceRepetitionScratch.outerWidth_eq_sourceQ0_mul_rep
        L (Fin m) hc.1))
    (CanonicalDefaultSource.canonicalDefaultTails L n
      (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ)
      hn (width27_pos L) (Q27_pos n m L Δ γ))
    k (rows27 n m L Δ γ k) (cols27 n m L Δ γ k)
    (RecursiveSamplingTape.readTape _ _ _ bits)

theorem scheduled27_entry {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (L Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) L Δ γ)
    (bits : RecursiveSamplingMaterialization.TapeList (Fin n)
      (width L) (width L - 2) (outerWidth L)
      (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ)
      (LookupSeed.width L) k
      (rows27 n m L Δ γ k) (cols27 n m L Δ γ k))
    (i : Fin (rows27 n m L Δ γ k))
    (j : Fin (cols27 n m L Δ γ k)) :
    (scheduledTable27 hn edge L Δ γ k hc bits).matrix i j =
      sourceRun27 hn edge L Δ γ k hc bits i j := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  letI : NeZero (width L) := ⟨by unfold width; positivity⟩
  letI : NeZero (outerWidth L) := ⟨by unfold outerWidth; positivity⟩
  letI : NeZero (width L - 2) := ⟨by
    have := width_admissible L
    omega⟩
  letI : NeZero (width27 L) := ⟨Nat.ne_of_gt (width27_pos L)⟩
  letI : NeZero (Q27 (V := Fin n) (E := Fin m) L γ Δ) :=
    ⟨Nat.ne_of_gt (Q27_pos n m L Δ γ)⟩
  unfold scheduledTable27 CanonicalDefaultSource.canonicalSourceOutput
    RecursiveSamplingMaterialization.materializeTapeList
  exact RecursiveSamplingMaterialization.materialize_entry _ _ _ _ _ _ _ _ _ _ i j

theorem scheduled27_eq_tabulate {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (L Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) L Δ γ)
    (bits : RecursiveSamplingMaterialization.TapeList (Fin n)
      (width L) (width L - 2) (outerWidth L)
      (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ)
      (LookupSeed.width L) k
      (rows27 n m L Δ γ k) (cols27 n m L Δ γ k)) :
    scheduledTable27 hn edge L Δ γ k hc bits =
      YaoMaterialization.tabulate (sourceRun27 hn edge L Δ γ k hc bits) := by
  rfl

def countedPrint27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (L Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) L Δ γ)
    (bits : RecursiveSamplingMaterialization.TapeList (Fin n)
      (width L) (width L - 2) (outerWidth L)
      (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ)
      (LookupSeed.width L) k
      (rows27 n m L Δ γ k) (cols27 n m L Δ γ k)) :
    YaoMaterialization.CountedOutput :=
  YaoMaterialization.countedTabulate (sourceRun27 hn edge L Δ γ k hc bits)

theorem countedPrint27_exact {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (L Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) L Δ γ)
    (bits : RecursiveSamplingMaterialization.TapeList (Fin n)
      (width L) (width L - 2) (outerWidth L)
      (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ)
      (LookupSeed.width L) k
      (rows27 n m L Δ γ k) (cols27 n m L Δ γ k)) :
    (countedPrint27 hn edge L Δ γ k hc bits).bits =
      (scheduledTable27 hn edge L Δ γ k hc bits).bits ∧
    (countedPrint27 hn edge L Δ γ k hc bits).entryCalls =
      rows27 n m L Δ γ k * cols27 n m L Δ γ k ∧
    (countedPrint27 hn edge L Δ γ k hc bits).consCells =
      rows27 n m L Δ γ k * cols27 n m L Δ γ k := by
  rw [scheduled27_eq_tabulate]
  exact ⟨YaoMaterialization.countedTabulate_bits _,
    YaoMaterialization.countedTabulate_entryCalls _,
    YaoMaterialization.countedTabulate_consCells _⟩

/-- The executable scheduled branch, including the tape's exact length. -/
def scheduledOutput27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ) :
    TotalFiniteConstructorScratch.SelectedOutput :=
  let L := Nat.clog 2 n
  let w := width27 L
  let Q := Q27 (V := Fin n) (E := Fin m) L γ Δ
  let mX := rows27 n m L Δ γ k
  let mY := cols27 n m L Δ γ k
  {
    rows := mX
    cols := mY
    budget := sourceBudget L (4 * RestorationWidthScheduleScratch.ell L)
      (q27 (V := Fin n) (E := Fin m) L γ Δ) k
    inputBits := RecursiveSamplingMaterialization.inputBitCount
      (Fin n) (width L) (width L - 2) (outerWidth L)
      w Q (LookupSeed.width L) k mX mY
    Tape := RecursiveSamplingMaterialization.TapeList
      (Fin n) (width L) (width L - 2) (outerWidth L)
      w Q (LookupSeed.width L) k mX mY
    tapeBits := Subtype.val
    table := scheduledTable27 hn edge L Δ γ k hc
  }

/-- The public choice uses all 22 current checks. -/
def select27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ) :
    TotalFiniteConstructorScratch.SelectedOutput :=
  if hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ then
    scheduledOutput27 hn edge Δ γ k hc
  else TotalFiniteConstructorScratch.fallbackOutput edge k

theorem select27_good {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ) :
    select27 hn edge Δ γ k = scheduledOutput27 hn edge Δ γ k hc := by
  simp [select27, hc]

theorem select27_bad {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : ¬ CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ) :
    select27 hn edge Δ γ k =
      TotalFiniteConstructorScratch.fallbackOutput edge k := by
  simp [select27, hc]

theorem scheduled27_lengths {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (L Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) L Δ γ)
    (bits : RecursiveSamplingMaterialization.TapeList (Fin n)
      (width L) (width L - 2) (outerWidth L)
      (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ)
      (LookupSeed.width L) k
      (rows27 n m L Δ γ k) (cols27 n m L Δ γ k)) :
    (scheduledTable27 hn edge L Δ γ k hc bits).bits.length =
      rows27 n m L Δ γ k * cols27 n m L Δ γ k := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  letI : NeZero (width L) := ⟨by unfold width; positivity⟩
  letI : NeZero (outerWidth L) := ⟨by unfold outerWidth; positivity⟩
  letI : NeZero (width L - 2) := ⟨by
    have := width_admissible L
    omega⟩
  letI : NeZero (width27 L) := ⟨Nat.ne_of_gt (width27_pos L)⟩
  letI : NeZero (Q27 (V := Fin n) (E := Fin m) L γ Δ) :=
    ⟨Nat.ne_of_gt (Q27_pos n m L Δ γ)⟩
  unfold scheduledTable27 CanonicalDefaultSource.canonicalSourceOutput
  exact RecursiveSamplingMaterialization.materializeTapeList_length _ _ _ _ _ _ _ _ _ _

/-- A separately fixed fair-bit analysis law on the actual scheduled tape. -/
noncomputable def scheduledExperiment27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ) :
    TotalFiniteConstructorScratch.SelectedExperiment :=
  let L := Nat.clog 2 n
  let mX := rows27 n m L Δ γ k
  let mY := cols27 n m L Δ γ k
  {
    output := scheduledOutput27 hn edge Δ γ k hc
    tapeFintype := by dsimp only [scheduledOutput27]; infer_instance
    tapeLaw := by
      dsimp only [scheduledOutput27]
      exact RecursiveSamplingMaterialization.tapeListLaw
        (Fin n) (width L) (width L - 2) (outerWidth L)
        (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ)
        (LookupSeed.width L) k mX mY
  }

noncomputable def experiment27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ) :
    TotalFiniteConstructorScratch.SelectedExperiment :=
  if hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ then
    scheduledExperiment27 hn edge Δ γ k hc
  else TotalFiniteConstructorScratch.fallbackExperiment edge k

theorem experiment27_output_eq_select27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ) :
    (experiment27 hn edge Δ γ k).output = select27 hn edge Δ γ k := by
  by_cases hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ
  · simp [experiment27, select27, hc, scheduledExperiment27]
  · simp [experiment27, select27, hc,
      TotalFiniteConstructorScratch.fallbackExperiment]

theorem select27_exact_lengths {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ) :
    let o := select27 hn edge Δ γ k
    ∀ t : o.Tape,
      (o.table t).bits.length = o.rows * o.cols ∧
      (o.tapeBits t).length = o.inputBits := by
  dsimp only
  by_cases hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ
  · rw [select27_good hn edge Δ γ k hc]
    intro t
    exact ⟨scheduled27_lengths hn edge (Nat.clog 2 n) Δ γ k hc t,
      t.property⟩
  · rw [select27_bad hn edge Δ γ k hc]
    intro t
    constructor
    · simpa only [TotalFiniteConstructorScratch.fallbackOutput] using
        FiniteFallbackOutput.fallbackTable_bits_length edge k
    · rfl

theorem scheduled27_valid {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ)
    (t : (scheduledOutput27 hn edge Δ γ k hc).Tape) :
    AModel.MatrixValid
      (scheduledOutput27 hn edge Δ γ k hc).rows
      (scheduledOutput27 hn edge Δ γ k hc).cols
      ((scheduledOutput27 hn edge Δ γ k hc).table t).bits := by
  have hL : 1 ≤ Nat.clog 2 n := by
    have h := hc
    dsimp only [CurrentAdditive.QuarticSchedule.Checks27] at h
    omega
  refine ⟨?_, ?_, ?_⟩
  · change 0 < rows27 n m (Nat.clog 2 n) Δ γ k
    unfold rows27 sourceRows
    exact compressionRowDraws_pos _ _ hL
  · change 0 < cols27 n m (Nat.clog 2 n) Δ γ k
    unfold cols27 sourceCols compressionColumnDraws
    omega
  · exact (scheduled27_lengths hn edge (Nat.clog 2 n) Δ γ k hc t)

theorem scheduled27_word_decodes {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ)
    (t : (scheduledOutput27 hn edge Δ γ k hc).Tape) :
    AModel.decodeMatrix (AModel.matrixWord
      (scheduledOutput27 hn edge Δ γ k hc).rows
      (scheduledOutput27 hn edge Δ γ k hc).cols
      ((scheduledOutput27 hn edge Δ γ k hc).table t).bits) =
      some ((scheduledOutput27 hn edge Δ γ k hc).rows,
        (scheduledOutput27 hn edge Δ γ k hc).cols,
        ((scheduledOutput27 hn edge Δ γ k hc).table t).bits) :=
  AModel.decodeMatrix_matrixWord (scheduled27_valid hn edge Δ γ k hc t)

#print axioms select27_good
#print axioms scheduled27_entry
#print axioms countedPrint27_exact
#print axioms scheduled27_lengths
#print axioms experiment27_output_eq_select27
#print axioms select27_exact_lengths
#print axioms scheduled27_word_decodes

end Paper2.CurrentAdditive.QuarticConstructor
