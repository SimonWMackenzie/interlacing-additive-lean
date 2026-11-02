import CurrentAdditive.QuarticSourceNoSuccess
import Paper2.ScannedSourceGuarantees

namespace Paper2.ScannedSourceGuarantees

open SourceMatrix SourceProfileParameters SourceDeficiency SourceSurvivingCollisions
  SourceRecursiveNoSampling Workspace.Types.CommComplexity

local instance (L : ℕ) : NeZero (width L) := ⟨by unfold width; positivity⟩
local instance (L : ℕ) : NeZero (outerWidth L) := ⟨by unfold outerWidth; positivity⟩
local instance (L : ℕ) : NeZero (width L - 2) := ⟨by
  have := width_admissible L
  omega⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- The executable scanned canonical source has the same finite public
guarantees as the original selected graph source. The graph gap occurs only
inside the NO implication; neither the output nor its canonical tails are
selected using a colouring or a cost certificate. -/
theorem selected_scanned_combined_finite_guarantees27
    {n m : ℕ} [NeZero n]
    (L : ℕ) (hL : 16 ≤ L)
    (edge : Fin m → Bool → Fin n)
    (loopless : ∀ e, edge e false ≠ edge e true)
    (rep Δ : ℕ) (hΔ : 0 < Δ)
    (hq : outerWidth L =
      SourceItems.sourceQ0 (Fin (4 * width L)) (Fin m) * rep)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (γ : ℝ) (hγ : 0 < γ) (hE : 0 < m)
    (hinner : (width L : ℝ) * rho L ≤ 1 / 1000)
    (houter : (outerWidth L : ℝ) * x L ≤ 1 / 10000)
    (hwide : (10 * L : ℝ) ≤ (outerWidth L : ℝ) / 4096)
    (href : (width L : ℝ) * x L ≤ 1 / 10000)
    (hscale : 4 * (width L : ℝ) ^ 2 * rho L ≤ 1)
    (hcountSource : 8 * (width L : ℝ) * (width L - 2 : ℕ) ≤
      witnessDensity γ * outerWidth L / 16)
    (w r Q q : ℕ) [NeZero w] [NeZero Q]
    (hw : w = 2 ^ r) (hw2 : 2 ≤ w) (hQ : Q = 2 ^ q)
    (ηq : ℚ)
    (hηq : (ηq : ℝ) = deletionAllowance (V := Fin n) (E := Fin m) γ Δ (width L))
    (hquarter : CurrentAdditive.QuarticSchedule.quarterCheck27Prop w Q ηq)
    (hsmall : 2 * (w : ℝ) ^ 2 * x L ≤
      deletionAllowance (V := Fin n) (E := Fin m) γ Δ (width L) /
        (16 * (127 / 128 : ℝ)))
    (hfirst : 4 * (1 / 256 : ℝ) * w * outerWidth L * x L ≤
      deletionAllowance (V := Fin n) (E := Fin m) γ Δ (width L) / 32)
    (hlast : 4 * (1 / 256 : ℝ) * w / outerWidth L ≤
      deletionAllowance (V := Fin n) (E := Fin m) γ Δ (width L) / 32)
    (hKcheck :
      (1024 * (1 / 256 : ℝ) * RestorationCoverParameters.B2 Q *
        (r + 2) * width L) *
      CurrentAdditive.QuarticSchedule.E27 Q ηq ≤
      deletionAllowance (V := Fin n) (E := Fin m) γ Δ (width L) * w / 16)
    (hxsmall : ((w : ℝ) ^ 2 * (outerWidth L : ℝ)) * x L ≤ 1)
    (hstar : 4 * RestorationCoverParameters.tStar Q ≤ w)
    (hsmallwx : (w : ℝ) * x L ≤ 1 / 10000)
    (hmargin : 2 * w * x L +
      deletionAllowance (V := Fin n) (E := Fin m) γ Δ (width L) /
        (16 * (127 / 128 : ℝ)) < 1)
    (hbridge : 80 * (L : ℝ) ≤ (Q : ℝ) *
      (deletionAllowance (V := Fin n) (E := Fin m) γ Δ (width L) /
        (16 * (w : ℝ))))
    (hsize : 2 * (n + width L - 3) ≤ outerWidth L)
    (ξ : SourceIteration.FixedTails L (width L) (width L - 2)
      (outerWidth L) w Q (Fin n)) (k : ℕ) :
    let output := fun bits : RecursiveSamplingMaterialization.TapeList (Fin n)
        (width L) (width L - 2) (outerWidth L) w Q
        (LookupSeed.width L) k (sourceRows L r q k) (sourceCols L r q k) =>
      RecursiveSamplingMaterialization.materializeTapeList
        (finCongr (Fintype.card_fin n))
        (SourceProfiles.width_ge_four L) (LookupSeed.width L)
        (by unfold LookupSeed.width; positivity)
        (SourceActiveRank.scanAtCanonical edge (by
          have := SourceProfiles.width_ge_four L; omega) hq)
        ξ k (sourceRows L r q k) (sourceCols L r q k) bits
    (∀ bits, D (output bits).matrix ≤ sourceCost L r q k) ∧
    (∀ colour : Fin n → Fin 3,
      (∀ e, colour (edge e false) ≠ colour (edge e true)) →
      ∀ bits, D (output bits).matrix ≤ sourceBudget L r q k) ∧
    ((∀ colour : Fin n → Fin 3, γ * m ≤
      ((Finset.univ.filter (fun e => colour (edge e false) =
        colour (edge e true))).card : ℝ)) →
      1 - (1 / 2 : ℝ) ^ 12 - (1 / 2 : ℝ) ^ 13 ≤
        (RecursiveSamplingMaterialization.tapeListLaw (Fin n) (width L)
          (width L - 2) (outerWidth L) w Q (LookupSeed.width L) k
          (sourceRows L r q k) (sourceCols L r q k)).prob
          (fun bits => D (output bits).matrix = sourceCost L r q k) ∧
      1 - (1 / 2 : ℝ) ^ 11 ≤
        (RecursiveSamplingMaterialization.tapeListLaw (Fin n) (width L)
          (width L - 2) (outerWidth L) w Q (LookupSeed.width L) k
          (sourceRows L r q k) (sourceCols L r q k)).prob
          (fun bits => D (output bits).matrix = sourceCost L r q k)) ∧
    (∀ bits, (output bits).bits.length =
      sourceRows L r q k * sourceCols L r q k) := by
  classical
  let hs := SourceProfiles.width_ge_four L
  let p := LookupSeed.width L
  let hp : 0 < p := by dsimp [p, LookupSeed.width]; positivity
  let old := SourceConstruction.activity (CanonicalSourceLabels.itemOrder (width L) n)
    edge (by omega : 3 ≤ width L) rep hq
  let scan := SourceActiveRank.scanAtCanonical edge
    (by omega : 3 ≤ width L) hq
  let ξold := ExecutableSourceCoordinateTransport.oldTails hq ξ
  let mX := sourceRows L r q k
  let mY := sourceCols L r q k
  let output := fun bits : RecursiveSamplingMaterialization.TapeList (Fin n)
      (width L) (width L - 2) (outerWidth L) w Q p k mX mY =>
    RecursiveSamplingMaterialization.materializeTapeList
      (finCongr (Fintype.card_fin n)) hs p hp scan ξ k mX mY bits
  change (∀ bits, D (output bits).matrix ≤ sourceCost L r q k) ∧
    (∀ colour : Fin n → Fin 3,
      (∀ e, colour (edge e false) ≠ colour (edge e true)) →
      ∀ bits, D (output bits).matrix ≤ sourceBudget L r q k) ∧
    ((∀ colour : Fin n → Fin 3, γ * m ≤
      ((Finset.univ.filter (fun e => colour (edge e false) =
        colour (edge e true))).card : ℝ)) →
      1 - (1 / 2 : ℝ) ^ 12 - (1 / 2 : ℝ) ^ 13 ≤
        (RecursiveSamplingMaterialization.tapeListLaw (Fin n) (width L)
          (width L - 2) (outerWidth L) w Q p k mX mY).prob
          (fun bits => D (output bits).matrix = sourceCost L r q k) ∧
      1 - (1 / 2 : ℝ) ^ 11 ≤
        (RecursiveSamplingMaterialization.tapeListLaw (Fin n) (width L)
          (width L - 2) (outerWidth L) w Q p k mX mY).prob
          (fun bits => D (output bits).matrix = sourceCost L r q k)) ∧
      (∀ bits, (output bits).bits.length = mX * mY)
  have hsize' : 2 * (Fintype.card (Fin n) + width L - 3) ≤ outerWidth L := by
    simpa only [Fintype.card_fin] using hsize
  have hE' : 0 < Fintype.card (Fin m) := by
    simpa only [Fintype.card_fin] using hE
  have hbound := SourceIteration.selected_iteration_bounds
    (s := width L) (q₁ := width L - 2) (q₂ := outerWidth L)
    (w := w) (Q := Q) L
    (CanonicalSourceLabels.itemOrder (width L) n) edge
    (by omega : 3 ≤ width L) rep hq ξold
    (exponent L) (outerExponent L) r q
    (by have := SourceProfiles.width_ge_four L; omega) rfl rfl hw hQ hsize' k
  have hB : LookupSeed.exponent L + 1 +
      k * (exponent L + exponent L + outerExponent L + r + q) =
      sourceBudget L r q k := by
    dsimp [sourceBudget]
    ring
  have hC : LookupSeed.exponent L + 1 +
      k * (exponent L + exponent L + outerExponent L + r + q) + k =
      sourceCost L r q k := by
    dsimp [sourceCost]
    ring
  have hOldUpper : D (RecursiveEntries.matrix (LookupSeed.matrix p) old ξold k) ≤
      sourceCost L r q k := by
    change D (SourceIteration.matrix (q₁ := width L - 2)
      L (CanonicalSourceLabels.itemOrder (width L) n) edge
      (by omega : 3 ≤ width L) rep hq ξold k) ≤ _
    exact hbound.1.trans_eq hC
  have hOldYes (colour : Fin n → Fin 3)
      (proper : ∀ e, colour (edge e false) ≠ colour (edge e true)) :
      D (RecursiveEntries.matrix (LookupSeed.matrix p) old ξold k) ≤
        sourceBudget L r q k := by
    change D (SourceIteration.matrix (q₁ := width L - 2)
      L (CanonicalSourceLabels.itemOrder (width L) n) edge
      (by omega : 3 ≤ width L) rep hq ξold k) ≤ _
    exact (hbound.2.1 colour proper).trans_eq hB
  constructor
  · intro bits
    exact (CanonicalScannedSampler.scanned_tapeList_D_le edge hs hq p hp ξ
      k mX mY bits).trans hOldUpper
  constructor
  · intro colour proper bits
    exact (CanonicalScannedSampler.scanned_tapeList_D_le edge hs hq p hp ξ
      k mX mY bits).trans (hOldYes colour proper)
  constructor
  · intro gap
    have gap' : ∀ colour : Fin n → Fin 3,
        γ * Fintype.card (Fin m) ≤
          ((Finset.univ.filter (fun e => colour (edge e false) =
            colour (edge e true))).card : ℝ) := by
      simpa only [Fintype.card_fin] using gap
    let τ := RecursiveSamplingMaterialization.tapeListLaw (Fin n) (width L)
      (width L - 2) (outerWidth L) w Q p k mX mY
    let idealLaw := RecursiveSampling.sampleLaw (V := Fin n)
      (q₁ := width L - 2) (q₂ := outerWidth L) (s := width L)
      (w := w) (Q := Q) hs (LookupSeed.rowLaw p)
      (LookupSeed.columnLaw p hp) k mX mY
    let print (bits : RecursiveSamplingMaterialization.TapeList (Fin n)
        (width L) (width L - 2) (outerWidth L) w Q p k mX mY) :=
      (output bits).matrix
    let ideal (z :
        (Fin mY → RecursiveEntries.Column (Fin p → Bool) (Fin p)
          (SourceConstruction.Items (width L) (Fin n)) (width L)
          (width L - 2) (outerWidth L) w Q k) ×
        (Fin mX → RecursiveEntries.Row (Fin p → Bool) (Fin p)
          (SourceConstruction.Items (width L) (Fin n)) (width L)
          (width L - 2) (outerWidth L) w Q k)) :=
      sampleMatrix (RecursiveEntries.matrix (LookupSeed.matrix p) old ξold k)
        z.2 z.1
    have hupper : ∀ bits, D (print bits) ≤ sourceCost L r q k := by
      intro bits
      exact (CanonicalScannedSampler.scanned_tapeList_D_le edge hs hq p hp ξ
        k mX mY bits).trans hOldUpper
    have hbad : idealLaw.toFiniteLaw.prob
        (fun z => D (ideal z) < sourceCost L r q k) ≤
        (1 / 2 : ℝ) ^ 12 := by
      exact SourceRecursiveNoSampling.selected_ideal_bad_le27 L hL
        (CanonicalSourceLabels.itemOrder (width L) n)
        edge loopless rep Δ hΔ hq hdegree γ hγ hE' gap'
        hinner houter hwide href hscale hcountSource
        w r Q q hw hw2 hQ ηq hηq hquarter hsmall hfirst hlast hKcheck
        hxsmall hstar hsmallwx hmargin hbridge hsize' ξold k
    have hcouple : |τ.prob
        (fun bits => D (print bits) < sourceCost L r q k) -
        idealLaw.toFiniteLaw.prob
          (fun z => D (ideal z) < sourceCost L r q k)| ≤
        (1 / 2 : ℝ) ^ 13 := by
      exact scanned_tapeList_matrix_event_error edge hs hq p hp ξ k mX mY
        {M | D M < sourceCost L r q k}
    have hstrong := SourceRecursiveNoSampling.exact_cost_of_bad_event_bound
      τ idealLaw.toFiniteLaw print ideal D (sourceCost L r q k)
      ((1 / 2 : ℝ) ^ 12) ((1 / 2 : ℝ) ^ 13)
      hupper hbad hcouple
    constructor
    · exact hstrong
    · norm_num at hstrong ⊢
      linarith
  · intro bits
    exact RecursiveSamplingMaterialization.materializeTapeList_length
      (finCongr (Fintype.card_fin n)) hs p hp scan ξ k mX mY bits


end Paper2.ScannedSourceGuarantees
#print axioms Paper2.ScannedSourceGuarantees.selected_scanned_combined_finite_guarantees27
