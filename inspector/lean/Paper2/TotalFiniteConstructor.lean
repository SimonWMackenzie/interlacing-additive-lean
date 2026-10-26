import Paper2.ParameterizedCanonicalSource
import Paper2.FiniteFallbackOutput
import Paper2.FiniteFallbackSourceGap

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-!
Finite, computable public-schedule branch selection for the pinned v12
Appendix D. The output record has no proof or promise field. Probability is
assigned separately to the chosen finite tape; it is not part of the
computable output data.
-/

namespace Paper2.TotalFiniteConstructorScratch

open SourceProfileParameters SourceRecursiveNoSampling
  Workspace.Types.CommComplexity YaoMaterialization

/-- The dimensions, budget, literal input bits, and row-major matrix table
of one finite selected output. `Tape` varies with the selected branch. -/
structure SelectedOutput where
  rows : ℕ
  cols : ℕ
  budget : ℕ
  inputBits : ℕ
  Tape : Type
  tapeBits : Tape → List Bool
  table : Tape → SerializedTable rows cols

/-- The fully specified scheduled record on exact-length fair-bit lists. -/
def scheduledOutput {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) (Nat.clog 2 n) Δ γ) : SelectedOutput :=
  let L := Nat.clog 2 n
  let r := ParameterizedCanonicalSource.restorationDepth L
  let q := ParameterizedCanonicalSource.coverDepth n m L Δ γ
  let w := ParameterizedCanonicalSource.restorationWidth L
  let Q := ParameterizedCanonicalSource.coverWidth n m L Δ γ
  let mX := sourceRows L r q k
  let mY := sourceCols L r q k
  {
      rows := mX
      cols := mY
      budget := sourceBudget L r q k
      inputBits := RecursiveSamplingMaterialization.inputBitCount
        (Fin n) (width L) (width L - 2) (outerWidth L)
        w Q (LookupSeed.width L) k mX mY
      Tape := RecursiveSamplingMaterialization.TapeList
        (Fin n) (width L) (width L - 2) (outerWidth L)
        w Q (LookupSeed.width L) k mX mY
      tapeBits := Subtype.val
      table := ParameterizedCanonicalSource.output L Δ γ edge hc hn k
  }

/-- The finite search table with deterministic singleton tape. -/
def fallbackOutput {n m : ℕ} (edge : Fin m → Bool → Fin n) (k : ℕ) :
    SelectedOutput :=
  {
      rows := FiniteFallbackOutput.rows k
      cols := FiniteFallbackOutput.cols k
      budget := 0
      inputBits := 0
      Tape := Unit
      tapeBits := fun _ => []
      table := fun _ => FiniteFallbackOutput.fallbackTable edge k
  }

/-- The frozen source constructor when the public checks pass, and the
exhaustive finite fallback otherwise. The test only reads public arithmetic;
the fallback itself decides three-colourability by finite search. -/
def select {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ) :
    SelectedOutput :=
  if hc : CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) (Nat.clog 2 n) Δ γ then
    scheduledOutput hn edge Δ γ k hc
  else fallbackOutput edge k

theorem select_good {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) (Nat.clog 2 n) Δ γ) :
    select hn edge Δ γ k = scheduledOutput hn edge Δ γ k hc := by
  simp [select, hc, scheduledOutput]

theorem select_bad {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : ¬ CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) (Nat.clog 2 n) Δ γ) :
    select hn edge Δ γ k = fallbackOutput edge k := by
  simp [select, hc]

/-- Probability analysis of the concrete selected output. The law is not a
caller-supplied certificate: `experiment` below fixes it to the actual fair
exact-length list law or the singleton fallback law. -/
structure SelectedExperiment where
  output : SelectedOutput
  tapeFintype : Fintype output.Tape
  tapeLaw : @FiniteLaw output.Tape tapeFintype

private def singletonLaw : FiniteLaw Unit where
  weight _ := 1
  nonneg _ := by norm_num
  total := by simp

/-- Fair-bit analysis record for the scheduled output. -/
noncomputable def scheduledExperiment {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) (Nat.clog 2 n) Δ γ) :
    SelectedExperiment :=
  let L := Nat.clog 2 n
  let w := ParameterizedCanonicalSource.restorationWidth L
  let Q := ParameterizedCanonicalSource.coverWidth n m L Δ γ
  let r := ParameterizedCanonicalSource.restorationDepth L
  let q := ParameterizedCanonicalSource.coverDepth n m L Δ γ
  let mX := sourceRows L r q k
  let mY := sourceCols L r q k
  {
      output := scheduledOutput hn edge Δ γ k hc
      tapeFintype := by dsimp only [scheduledOutput]; infer_instance
      tapeLaw := by
        dsimp only [scheduledOutput]
        exact RecursiveSamplingMaterialization.tapeListLaw
          (Fin n) (width L) (width L - 2) (outerWidth L)
          w Q (LookupSeed.width L) k mX mY
  }

/-- Deterministic singleton analysis record for fallback. -/
def fallbackExperiment {n m : ℕ} (edge : Fin m → Bool → Fin n)
    (k : ℕ) : SelectedExperiment :=
  {
      output := fallbackOutput edge k
      tapeFintype := by dsimp only [fallbackOutput]; infer_instance
      tapeLaw := by dsimp only [fallbackOutput]; exact singletonLaw
  }

/-- The only two tape laws, assigned after the computable output is chosen. -/
noncomputable def experiment {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ) :
    SelectedExperiment :=
  if hc : CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) (Nat.clog 2 n) Δ γ then
    scheduledExperiment hn edge Δ γ k hc
  else fallbackExperiment edge k

theorem experiment_good {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) (Nat.clog 2 n) Δ γ) :
    experiment hn edge Δ γ k = scheduledExperiment hn edge Δ γ k hc := by
  simp [experiment, hc]

theorem experiment_bad {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : ¬ CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) (Nat.clog 2 n) Δ γ) :
    experiment hn edge Δ γ k = fallbackExperiment edge k := by
  simp [experiment, hc]

theorem experiment_output_eq_select {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ) :
    (experiment hn edge Δ γ k).output = select hn edge Δ γ k := by
  by_cases hc : CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) (Nat.clog 2 n) Δ γ
  · simp [experiment, select, hc, scheduledExperiment]
  · simp [experiment, select, hc, fallbackExperiment]

/-- Every tape in the selected branch has positive mass under its actual
branch law; no tape is discarded by conditioning on sampler success. -/
theorem experiment_full_support {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ) :
    let e := experiment hn edge Δ γ k
    letI := e.tapeFintype
    ∀ t : e.output.Tape, 0 < e.tapeLaw.weight t := by
  dsimp only
  by_cases hc : CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) (Nat.clog 2 n) Δ γ
  · rw [experiment_good hn edge Δ γ k hc]
    intro t
    change 0 < (1 / 2 : ℝ) ^
      RecursiveSamplingMaterialization.inputBitCount (Fin n)
        (width (Nat.clog 2 n)) (width (Nat.clog 2 n) - 2)
        (outerWidth (Nat.clog 2 n))
        (ParameterizedCanonicalSource.restorationWidth (Nat.clog 2 n))
        (ParameterizedCanonicalSource.coverWidth n m (Nat.clog 2 n) Δ γ)
        (LookupSeed.width (Nat.clog 2 n)) k
        (sourceRows (Nat.clog 2 n)
          (ParameterizedCanonicalSource.restorationDepth (Nat.clog 2 n))
          (ParameterizedCanonicalSource.coverDepth n m (Nat.clog 2 n) Δ γ) k)
        (sourceCols (Nat.clog 2 n)
          (ParameterizedCanonicalSource.restorationDepth (Nat.clog 2 n))
          (ParameterizedCanonicalSource.coverDepth n m (Nat.clog 2 n) Δ γ) k)
    positivity
  · rw [experiment_bad hn edge Δ γ k hc]
    intro t
    change (0 : ℝ) < 1
    norm_num

private theorem sourceCost_eq_budget_add (L r q k : ℕ) :
    sourceCost L r q k = sourceBudget L r q k + k := by
  simp only [sourceCost, sourceBudget]
  ring

private theorem select_good_tape {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) (Nat.clog 2 n) Δ γ) :
    (select hn edge Δ γ k).Tape =
      RecursiveSamplingMaterialization.TapeList
        (Fin n) (width (Nat.clog 2 n)) (width (Nat.clog 2 n) - 2)
        (outerWidth (Nat.clog 2 n))
        (ParameterizedCanonicalSource.restorationWidth (Nat.clog 2 n))
        (ParameterizedCanonicalSource.coverWidth n m (Nat.clog 2 n) Δ γ)
        (LookupSeed.width (Nat.clog 2 n)) k
        (sourceRows (Nat.clog 2 n)
          (ParameterizedCanonicalSource.restorationDepth (Nat.clog 2 n))
          (ParameterizedCanonicalSource.coverDepth n m (Nat.clog 2 n) Δ γ) k)
        (sourceCols (Nat.clog 2 n)
          (ParameterizedCanonicalSource.restorationDepth (Nat.clog 2 n))
          (ParameterizedCanonicalSource.coverDepth n m (Nat.clog 2 n) Δ γ) k) := by
  simp [select, hc, scheduledOutput]

private theorem fallback_cost_le {n m : ℕ}
    (edge : Fin m → Bool → Fin n) (k : ℕ) (hk : 1 ≤ k) :
    D (FiniteFallbackOutput.fallbackTable edge k).matrix ≤ k := by
  by_cases hcolour : FiniteFallbackOutput.ThreeColourable edge
  · rw [FiniteFallbackOutput.fallback_yes_D edge k hcolour]
    omega
  · by_cases h1 : k = 1
    · subst k
      rw [FiniteFallbackOutput.fallback_no_one_D edge hcolour]
    · rw [FiniteFallbackOutput.fallback_no_D edge k (by omega) hcolour]

/-- Every tape, including a capped-rejection abort, has cost at most the
announced budget plus `k`. -/
theorem selected_all_cost_le {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hk : 1 ≤ k)
    (loopless : ∀ e, edge e false ≠ edge e true)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hm : 0 < m) :
    let o := select hn edge Δ γ k
    ∀ t : o.Tape, D (o.table t).matrix ≤ o.budget + k := by
  dsimp only
  by_cases hc : CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) (Nat.clog 2 n) Δ γ
  · letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    rw [select_good hn edge Δ γ k hc]
    have hG := ParameterizedCanonicalSource.checked_finite_guarantees
      (Nat.clog 2 n) Δ γ edge loopless hdegree hγ hΔ hm hc k
    simpa only [scheduledOutput, sourceCost_eq_budget_add] using hG.1
  · rw [select_bad hn edge Δ γ k hc]
    simpa [fallbackOutput] using
      (fun (_ : Unit) => fallback_cost_le edge k hk)

/-- A proper three-colouring gives the announced YES budget on every tape. -/
theorem selected_yes_cost_le {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (loopless : ∀ e, edge e false ≠ edge e true)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hm : 0 < m)
    (hcolour : FiniteFallbackOutput.ThreeColourable edge) :
    let o := select hn edge Δ γ k
    ∀ t : o.Tape, D (o.table t).matrix ≤ o.budget := by
  dsimp only
  by_cases hc : CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) (Nat.clog 2 n) Δ γ
  · letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    rw [select_good hn edge Δ γ k hc]
    have hG := ParameterizedCanonicalSource.checked_finite_guarantees
      (Nat.clog 2 n) Δ γ edge loopless hdegree hγ hΔ hm hc k
    obtain ⟨colour, proper⟩ := hcolour
    simpa only [scheduledOutput] using hG.2.1 colour proper
  · rw [select_bad hn edge Δ γ k hc]
    simpa [fallbackOutput, FiniteFallbackOutput.budget] using
      (fun (_ : Unit) => Nat.le_of_eq
        (FiniteFallbackOutput.fallback_yes_D edge k hcolour))

/-- Both the supplied fair-bit list and the printed row-major table have
their exact announced lengths, including a scheduled abort. -/
theorem selected_exact_lengths {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (loopless : ∀ e, edge e false ≠ edge e true)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hm : 0 < m) :
    let o := select hn edge Δ γ k
    ∀ t : o.Tape,
      (o.table t).bits.length = o.rows * o.cols ∧
      (o.tapeBits t).length = o.inputBits := by
  dsimp only
  by_cases hc : CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) (Nat.clog 2 n) Δ γ
  · letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    rw [select_good hn edge Δ γ k hc]
    have hG := ParameterizedCanonicalSource.checked_finite_guarantees
      (Nat.clog 2 n) Δ γ edge loopless hdegree hγ hΔ hm hc k
    intro t
    constructor
    · simpa only [scheduledOutput] using hG.2.2.2 t
    · exact t.property
  · rw [select_bad hn edge Δ γ k hc]
    intro t
    constructor
    · simpa only [fallbackOutput] using
        FiniteFallbackOutput.fallbackTable_bits_length edge k
    · rfl

/-- A failed public check can only send a graph below the explicit finite
source-size threshold to exhaustive fallback. -/
theorem failed_check_below_threshold {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ)
    (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hc : ¬ CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) (Nat.clog 2 n) Δ γ) :
    n < CompletePublicScheduleScratch.sizeThreshold Δ γ := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have h := CompletePublicScheduleScratch.failure_below_size_threshold
    (V := Fin n) (E := Fin m) edge Δ γ hγ hΔ hincident hdegree
    (by simpa only [Fintype.card_fin] using hc)
  simpa only [Fintype.card_fin] using h

/-- Probability under the selected finite tape law of attaining the declared
NO-side cost. The actual law is uniform on the scheduled exact-length bit
lists, and a point mass on the fallback singleton. -/
noncomputable def successProbability {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ) : ℝ := by
  let e := experiment hn edge Δ γ k
  letI := e.tapeFintype
  exact e.tapeLaw.prob
    (fun t => D (e.output.table t).matrix = e.output.budget + k)

private theorem successProbability_good {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) (Nat.clog 2 n) Δ γ) :
    successProbability hn edge Δ γ k =
      (RecursiveSamplingMaterialization.tapeListLaw
        (Fin n) (width (Nat.clog 2 n)) (width (Nat.clog 2 n) - 2)
        (outerWidth (Nat.clog 2 n))
        (ParameterizedCanonicalSource.restorationWidth (Nat.clog 2 n))
        (ParameterizedCanonicalSource.coverWidth n m (Nat.clog 2 n) Δ γ)
        (LookupSeed.width (Nat.clog 2 n)) k
        (sourceRows (Nat.clog 2 n)
          (ParameterizedCanonicalSource.restorationDepth (Nat.clog 2 n))
          (ParameterizedCanonicalSource.coverDepth n m (Nat.clog 2 n) Δ γ) k)
        (sourceCols (Nat.clog 2 n)
          (ParameterizedCanonicalSource.restorationDepth (Nat.clog 2 n))
          (ParameterizedCanonicalSource.coverDepth n m (Nat.clog 2 n) Δ γ) k)).prob
        (fun bits => D (ParameterizedCanonicalSource.output
          (Nat.clog 2 n) Δ γ edge hc hn k bits).matrix =
          sourceBudget (Nat.clog 2 n)
            (ParameterizedCanonicalSource.restorationDepth (Nat.clog 2 n))
            (ParameterizedCanonicalSource.coverDepth n m (Nat.clog 2 n) Δ γ) k + k) := by
  unfold successProbability
  dsimp only
  rw [experiment_good hn edge Δ γ k hc]
  rfl

private theorem successProbability_bad_of_gap {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hγ : 0 < γ) (hm : 0 < m) (hk : 1 ≤ k)
    (hc : ¬ CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) (Nat.clog 2 n) Δ γ)
    (gap : ∀ colour : Fin n → Fin 3, (γ : ℝ) * m ≤
      ((Finset.univ.filter (fun e => colour (edge e false) =
        colour (edge e true))).card : ℝ)) :
    successProbability hn edge Δ γ k = 1 := by
  have hγR : (0 : ℝ) < γ := by exact_mod_cast hγ
  have hD := FiniteFallbackSourceGap.fallback_source_no_D
    edge (γ : ℝ) hγR hm gap k hk
  have hD' : D (FiniteFallbackOutput.fallbackTable edge k).matrix = k := by
    simpa [FiniteFallbackOutput.budget] using hD
  unfold successProbability
  dsimp only
  rw [experiment_bad hn edge Δ γ k hc]
  dsimp only [fallbackExperiment, fallbackOutput]
  simp only [id_eq, zero_add]
  change (singletonLaw.prob
    (fun _ : Unit => D (FiniteFallbackOutput.fallbackTable edge k).matrix = k)) = 1
  simp [hD']

/-- On a positive-gap source, the selected branch attains the announced
`B+k` cost with the frozen lower probability. -/
theorem selected_no_success {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hk : 1 ≤ k)
    (loopless : ∀ e, edge e false ≠ edge e true)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hm : 0 < m)
    (gap : ∀ colour : Fin n → Fin 3, (γ : ℝ) * m ≤
      ((Finset.univ.filter (fun e => colour (edge e false) =
        colour (edge e true))).card : ℝ)) :
    1 - (1 / 2 : ℝ) ^ 11 ≤ successProbability hn edge Δ γ k := by
  by_cases hc : CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) (Nat.clog 2 n) Δ γ
  · letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    have hG := ParameterizedCanonicalSource.checked_finite_guarantees
      (Nat.clog 2 n) Δ γ edge loopless hdegree hγ hΔ hm hc k
    rw [successProbability_good hn edge Δ γ k hc]
    simpa only [sourceCost_eq_budget_add] using (hG.2.2.1 gap).2
  · rw [successProbability_bad_of_gap hn edge Δ γ k hγ hm hk hc gap]
    norm_num

/-- The four finite output guarantees and effective fallback bound for the
single public selector. The probability is under `experiment`'s exact branch
law, whose output is proved equal to `select`. -/
def Guarantees {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ) : Prop :=
  let o := select hn edge Δ γ k
  (∀ t : o.Tape, D (o.table t).matrix ≤ o.budget + k) ∧
  (FiniteFallbackOutput.ThreeColourable edge →
    ∀ t : o.Tape, D (o.table t).matrix ≤ o.budget) ∧
  ((∀ colour : Fin n → Fin 3, (γ : ℝ) * m ≤
    ((Finset.univ.filter (fun e => colour (edge e false) =
      colour (edge e true))).card : ℝ)) →
    1 - (1 / 2 : ℝ) ^ 11 ≤ successProbability hn edge Δ γ k) ∧
  (∀ t : o.Tape,
    (o.table t).bits.length = o.rows * o.cols ∧
    (o.tapeBits t).length = o.inputBits) ∧
  ((¬ CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) (Nat.clog 2 n) Δ γ) →
    n < CompletePublicScheduleScratch.sizeThreshold Δ γ) ∧
  (experiment hn edge Δ γ k).output = o

theorem selected_finite_guarantees {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hk : 1 ≤ k)
    (loopless : ∀ e, edge e false ≠ edge e true)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hm : 0 < m) :
    Guarantees hn edge Δ γ k := by
  dsimp only [Guarantees]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact selected_all_cost_le hn edge Δ γ k hk loopless hdegree hγ hΔ hm
  · intro hcolour
    exact selected_yes_cost_le hn edge Δ γ k loopless hdegree hγ hΔ hm hcolour
  · intro gap
    exact selected_no_success hn edge Δ γ k hk loopless hdegree hγ hΔ hm gap
  · exact selected_exact_lengths hn edge Δ γ k loopless hdegree hγ hΔ hm
  · intro hc
    exact failed_check_below_threshold hn edge Δ γ hγ hΔ hincident hdegree hc
  · exact experiment_output_eq_select hn edge Δ γ k


end Paper2.TotalFiniteConstructorScratch
