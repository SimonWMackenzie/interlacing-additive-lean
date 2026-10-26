import Paper2.ExecutableSourceCoordinateTransport
import Paper2.ColumnFirstSampleLawBridge
import Paper2.RecursiveSamplingMaterialization

/-! Proof-only transport from the original source-coordinate choice to the
canonical scanned activity, through the actual finite-choice and capped
samplers. The inverse coordinate map and old tails are never computed by the
canonical constructor. -/

namespace Paper2.CanonicalScannedSampler

open SourceMatrix SourceSuccessorConjugacy
open Workspace.Types.CommComplexity

variable {s n m rep q₁ q₂ w Q : ℕ}
variable [NeZero s] [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q]

omit [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q] in
/-- Exact unrestricted communication cost of the full recursive scanned
matrix, compared with the original activity and proof-side inverse tails. -/
theorem scanned_matrix_D {X Y : Type} [Fintype X] [Fintype Y]
    (edge : Fin m → Bool → Fin n) (hs : 3 ≤ s)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin m) * rep)
    (F : X → Y → Bool)
    (ξ : RecursiveEntries.Tails X Y (SourceConstruction.Items s (Fin n))
      s q₁ q₂ w Q) (k : ℕ) :
    D (RecursiveEntries.matrix F
      (SourceActiveRank.scanAtCanonical edge hs hq) ξ k) =
    D (RecursiveEntries.matrix F
      (SourceConstruction.activity (CanonicalSourceLabels.itemOrder s n)
        edge hs rep hq)
      (ExecutableSourceCoordinateTransport.oldTails hq ξ) k) := by
  let π := CanonicalSourceActivityTransport.coordinatePermutation hq
  let eqv := carrierEquivs (s := s) (q₁ := q₁) (w := w) (Q := Q)
    (J := SourceConstruction.Items s (Fin n)) π
    (Equiv.refl X) (Equiv.refl Y) k
  have hD := pullback_D_eq_of_surjective
    (RecursiveEntries.matrix F (SourceActiveRank.scanAtCanonical edge hs hq) ξ k)
    eqv.1 eqv.2 eqv.1.surjective eqv.2.surjective
  have hfun :
      (fun x y => RecursiveEntries.matrix F
        (SourceActiveRank.scanAtCanonical edge hs hq) ξ k
        (eqv.1 x) (eqv.2 y)) =
      RecursiveEntries.matrix F
        (SourceConstruction.activity (CanonicalSourceLabels.itemOrder s n)
          edge hs rep hq)
        (ExecutableSourceCoordinateTransport.oldTails hq ξ) k := by
    funext x y
    exact ExecutableSourceCoordinateTransport.scanned_matrix_map
      edge hs hq F ξ k x y
  exact hD.symm.trans (congrArg D hfun)

/-- Every capped tape, including rejection exhaustion, produces a table
whose unrestricted communication cost is at most the original full source
matrix's cost. -/
theorem scanned_run_D_le [NeZero n] (edge : Fin m → Bool → Fin n) (hs : 4 ≤ s)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin m) * rep)
    (p : ℕ) (hp : 0 < p)
    (ξ : RecursiveEntries.Tails (Fin p → Bool) (Fin p)
      (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q)
    (k mX mY : ℕ)
    (t : RecursiveSamplingExecution.Tape (Fin n) s q₁ q₂ w Q p k mX mY) :
    D (RecursiveSamplingExecution.run (finCongr (Fintype.card_fin n))
      hs p hp (SourceActiveRank.scanAtCanonical edge (by omega) hq)
      ξ k mX mY t) ≤
    D (RecursiveEntries.matrix (LookupSeed.matrix p)
      (SourceConstruction.activity (CanonicalSourceLabels.itemOrder s n)
        edge (by omega) rep hq)
      (ExecutableSourceCoordinateTransport.oldTails hq ξ) k) := by
  exact (RecursiveSamplingExecution.run_D_le
    (finCongr (Fintype.card_fin n)) hs p hp
    (SourceActiveRank.scanAtCanonical edge (by omega) hq)
    ξ k mX mY t).trans
      (le_of_eq (scanned_matrix_D edge (by omega) hq
        (LookupSeed.matrix p) ξ k))

/-- Every ideal sampled-table event has exactly the same mass for the old
activity with proof-side inverse tails and for the executable scanned
activity with the supplied canonical tails. The sample law is literally the
owner's column-first `RecursiveSampling.sampleLaw`. -/
theorem scanned_ideal_table_event [NeZero n]
    (edge : Fin m → Bool → Fin n) (hs : 4 ≤ s)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin m) * rep)
    (p : ℕ) (hp : 0 < p)
    (ξ : RecursiveEntries.Tails (Fin p → Bool) (Fin p)
      (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q)
    (k mX mY : ℕ) (E : Set (Fin mX → Fin mY → Bool)) :
    (RecursiveSampling.sampleLaw (V := Fin n) (q₁ := q₁) (q₂ := q₂)
      (w := w) (Q := Q) hs (LookupSeed.rowLaw p)
      (LookupSeed.columnLaw p hp) k mX mY).toFiniteLaw.prob
        (fun z => sampleMatrix
          (RecursiveEntries.matrix (LookupSeed.matrix p)
            (SourceConstruction.activity (CanonicalSourceLabels.itemOrder s n)
              edge (by omega) rep hq)
            (ExecutableSourceCoordinateTransport.oldTails hq ξ) k)
          z.2 z.1 ∈ E) =
    (RecursiveSampling.sampleLaw (V := Fin n) (q₁ := q₁) (q₂ := q₂)
      (w := w) (Q := Q) hs (LookupSeed.rowLaw p)
      (LookupSeed.columnLaw p hp) k mX mY).toFiniteLaw.prob
        (fun z => sampleMatrix
          (RecursiveEntries.matrix (LookupSeed.matrix p)
            (SourceActiveRank.scanAtCanonical edge (by omega) hq) ξ k)
          z.2 z.1 ∈ E) := by
  let oldActivity := SourceConstruction.activity
    (CanonicalSourceLabels.itemOrder s n) edge (by omega : 3 ≤ s) rep hq
  let π := CanonicalSourceActivityTransport.coordinatePermutation hq
  have hscan : SourceActiveRank.scanAtCanonical edge (by omega : 3 ≤ s) hq =
      SourceCoordinateConjugacy.activityNew π oldActivity := by
    rw [ExecutableSourceCoordinateTransport.scan_eq_canonical,
      CanonicalSourceActivityTransport.canonicalActivity_eq]
  have h := ColumnFirstSampleLawBridge.column_first_table_event_prob
    (V := Fin n) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
    hs (LookupSeed.rowLaw p) (LookupSeed.rowLaw p)
    (LookupSeed.columnLaw p hp) (LookupSeed.columnLaw p hp)
    π (Equiv.refl _) (Equiv.refl _)
    (fun _ => rfl) (fun _ => rfl)
    (LookupSeed.matrix p) (LookupSeed.matrix p) (fun _ _ => rfl)
    oldActivity (ExecutableSourceCoordinateTransport.oldTails hq ξ)
    k mX mY (fun table => table ∈ E)
  rw [← hscan, ExecutableSourceCoordinateTransport.tailsMap_oldTails] at h
  simpa only [RecursiveEntries.table_eq_sampleMatrix] using h

/-- The actual capped scanned run is within the original ideal law by one
sampler error, not twice that error. No coupling of old and new bit tapes is
asserted. -/
theorem scanned_run_event_error [NeZero n]
    (edge : Fin m → Bool → Fin n) (hs : 4 ≤ s)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin m) * rep)
    (p : ℕ) (hp : 0 < p)
    (ξ : RecursiveEntries.Tails (Fin p → Bool) (Fin p)
      (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q)
    (k mX mY : ℕ) (E : Set (Fin mX → Fin mY → Bool)) :
    |(RecursiveSamplingExecution.tapeLaw (Fin n) s q₁ q₂ w Q p k mX mY).prob
        (fun t => RecursiveSamplingExecution.run
          (finCongr (Fintype.card_fin n)) hs p hp
          (SourceActiveRank.scanAtCanonical edge (by omega) hq)
          ξ k mX mY t ∈ E) -
      (RecursiveSampling.sampleLaw (V := Fin n) (q₁ := q₁) (q₂ := q₂)
        (w := w) (Q := Q) hs (LookupSeed.rowLaw p)
        (LookupSeed.columnLaw p hp) k mX mY).toFiniteLaw.prob
          (fun z => sampleMatrix
            (RecursiveEntries.matrix (LookupSeed.matrix p)
              (SourceConstruction.activity (CanonicalSourceLabels.itemOrder s n)
                edge (by omega) rep hq)
              (ExecutableSourceCoordinateTransport.oldTails hq ξ) k)
            z.2 z.1 ∈ E)| ≤ (1 / 2 : ℝ) ^ 13 := by
  have h := RecursiveSamplingExecution.run_event_error
    (finCongr (Fintype.card_fin n)) hs p hp
    (SourceActiveRank.scanAtCanonical edge (by omega) hq)
    ξ k mX mY E
  rw [← scanned_ideal_table_event edge hs hq p hp ξ k mX mY E] at h
  exact h

/-- The literal row-major output list decodes to a matrix of cost no
greater than the original full source matrix, on every fair-bit tape. -/
theorem scanned_materialize_D_le [NeZero n]
    (edge : Fin m → Bool → Fin n) (hs : 4 ≤ s)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin m) * rep)
    (p : ℕ) (hp : 0 < p)
    (ξ : RecursiveEntries.Tails (Fin p → Bool) (Fin p)
      (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q)
    (k mX mY : ℕ)
    (t : RecursiveSamplingExecution.Tape (Fin n) s q₁ q₂ w Q p k mX mY) :
    D (RecursiveSamplingMaterialization.materialize
      (finCongr (Fintype.card_fin n)) hs p hp
      (SourceActiveRank.scanAtCanonical edge (by omega) hq)
      ξ k mX mY t).matrix ≤
    D (RecursiveEntries.matrix (LookupSeed.matrix p)
      (SourceConstruction.activity (CanonicalSourceLabels.itemOrder s n)
        edge (by omega) rep hq)
      (ExecutableSourceCoordinateTransport.oldTails hq ξ) k) := by
  rw [RecursiveSamplingMaterialization.materialize_D]
  exact scanned_run_D_le edge hs hq p hp ξ k mX mY t

/-- The decoded literal table has the same one-error comparison against the
old ideal table law. -/
theorem scanned_materialize_matrix_event_error [NeZero n]
    (edge : Fin m → Bool → Fin n) (hs : 4 ≤ s)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin m) * rep)
    (p : ℕ) (hp : 0 < p)
    (ξ : RecursiveEntries.Tails (Fin p → Bool) (Fin p)
      (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q)
    (k mX mY : ℕ) (E : Set (Fin mX → Fin mY → Bool)) :
    |(RecursiveSamplingExecution.tapeLaw (Fin n) s q₁ q₂ w Q p k mX mY).prob
        (fun t => (RecursiveSamplingMaterialization.materialize
          (finCongr (Fintype.card_fin n)) hs p hp
          (SourceActiveRank.scanAtCanonical edge (by omega) hq)
          ξ k mX mY t).matrix ∈ E) -
      (RecursiveSampling.sampleLaw (V := Fin n) (q₁ := q₁) (q₂ := q₂)
        (w := w) (Q := Q) hs (LookupSeed.rowLaw p)
        (LookupSeed.columnLaw p hp) k mX mY).toFiniteLaw.prob
          (fun z => sampleMatrix
            (RecursiveEntries.matrix (LookupSeed.matrix p)
              (SourceConstruction.activity (CanonicalSourceLabels.itemOrder s n)
                edge (by omega) rep hq)
              (ExecutableSourceCoordinateTransport.oldTails hq ξ) k)
            z.2 z.1 ∈ E)| ≤ (1 / 2 : ℝ) ^ 13 := by
  simp_rw [RecursiveSamplingMaterialization.materialize_matrix]
  exact scanned_run_event_error edge hs hq p hp ξ k mX mY E

/-- Every event of the literal row-major Boolean list is compared to the
original ideal source table, serialized by the same deterministic encoder. -/
theorem scanned_materialize_bits_event_error [NeZero n]
    (edge : Fin m → Bool → Fin n) (hs : 4 ≤ s)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin m) * rep)
    (p : ℕ) (hp : 0 < p)
    (ξ : RecursiveEntries.Tails (Fin p → Bool) (Fin p)
      (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q)
    (k mX mY : ℕ) (E : Set (List Bool)) :
    |(RecursiveSamplingExecution.tapeLaw (Fin n) s q₁ q₂ w Q p k mX mY).prob
        (fun t => (RecursiveSamplingMaterialization.materialize
          (finCongr (Fintype.card_fin n)) hs p hp
          (SourceActiveRank.scanAtCanonical edge (by omega) hq)
          ξ k mX mY t).bits ∈ E) -
      (RecursiveSampling.sampleLaw (V := Fin n) (q₁ := q₁) (q₂ := q₂)
        (w := w) (Q := Q) hs (LookupSeed.rowLaw p)
        (LookupSeed.columnLaw p hp) k mX mY).toFiniteLaw.prob
          (fun z => (YaoMaterialization.tabulate (sampleMatrix
            (RecursiveEntries.matrix (LookupSeed.matrix p)
              (SourceConstruction.activity (CanonicalSourceLabels.itemOrder s n)
                edge (by omega) rep hq)
              (ExecutableSourceCoordinateTransport.oldTails hq ξ) k)
            z.2 z.1)).bits ∈ E)| ≤ (1 / 2 : ℝ) ^ 13 := by
  have h := RecursiveSamplingMaterialization.materialize_bits_event_error
    (finCongr (Fintype.card_fin n)) hs p hp
    (SourceActiveRank.scanAtCanonical edge (by omega) hq)
    ξ k mX mY E
  have hIdeal := scanned_ideal_table_event edge hs hq p hp ξ k mX mY
    {F | (YaoMaterialization.tabulate F).bits ∈ E}
  simp only [Set.mem_setOf_eq] at hIdeal
  rw [← hIdeal] at h
  exact h

/-- A correctly sized literal bit list is parsed into the very same capped
materialization; serialization does not increase communication cost. -/
theorem scanned_tapeList_D_le [NeZero n]
    (edge : Fin m → Bool → Fin n) (hs : 4 ≤ s)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin m) * rep)
    (p : ℕ) (hp : 0 < p)
    (ξ : RecursiveEntries.Tails (Fin p → Bool) (Fin p)
      (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q)
    (k mX mY : ℕ)
    (bits : RecursiveSamplingMaterialization.TapeList
      (Fin n) s q₁ q₂ w Q p k mX mY) :
    D (RecursiveSamplingMaterialization.materializeTapeList
      (finCongr (Fintype.card_fin n)) hs p hp
      (SourceActiveRank.scanAtCanonical edge (by omega) hq)
      ξ k mX mY bits).matrix ≤
    D (RecursiveEntries.matrix (LookupSeed.matrix p)
      (SourceConstruction.activity (CanonicalSourceLabels.itemOrder s n)
        edge (by omega) rep hq)
      (ExecutableSourceCoordinateTransport.oldTails hq ξ) k) := by
  exact (RecursiveSamplingMaterialization.materializeTapeList_D_le
    (finCongr (Fintype.card_fin n)) hs p hp
    (SourceActiveRank.scanAtCanonical edge (by omega) hq)
    ξ k mX mY bits).trans
      (le_of_eq (scanned_matrix_D edge (by omega) hq
        (LookupSeed.matrix p) ξ k))

/-- The same single-error bound holds for uniform correctly sized literal
bit lists, including rejection-exhausted lists. -/
theorem scanned_tapeList_bits_event_error [NeZero n]
    (edge : Fin m → Bool → Fin n) (hs : 4 ≤ s)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin m) * rep)
    (p : ℕ) (hp : 0 < p)
    (ξ : RecursiveEntries.Tails (Fin p → Bool) (Fin p)
      (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q)
    (k mX mY : ℕ) (E : Set (List Bool)) :
    |(RecursiveSamplingMaterialization.tapeListLaw
        (Fin n) s q₁ q₂ w Q p k mX mY).prob
        (fun bits => (RecursiveSamplingMaterialization.materializeTapeList
          (finCongr (Fintype.card_fin n)) hs p hp
          (SourceActiveRank.scanAtCanonical edge (by omega) hq)
          ξ k mX mY bits).bits ∈ E) -
      (RecursiveSampling.sampleLaw (V := Fin n) (q₁ := q₁) (q₂ := q₂)
        (w := w) (Q := Q) hs (LookupSeed.rowLaw p)
        (LookupSeed.columnLaw p hp) k mX mY).toFiniteLaw.prob
          (fun z => (YaoMaterialization.tabulate (sampleMatrix
            (RecursiveEntries.matrix (LookupSeed.matrix p)
              (SourceConstruction.activity (CanonicalSourceLabels.itemOrder s n)
                edge (by omega) rep hq)
              (ExecutableSourceCoordinateTransport.oldTails hq ξ) k)
            z.2 z.1)).bits ∈ E)| ≤ (1 / 2 : ℝ) ^ 13 := by
  have h := RecursiveSamplingMaterialization.materializeTapeList_event_error
    (finCongr (Fintype.card_fin n)) hs p hp
    (SourceActiveRank.scanAtCanonical edge (by omega) hq)
    ξ k mX mY E
  have hIdeal := scanned_ideal_table_event edge hs hq p hp ξ k mX mY
    {F | (YaoMaterialization.tabulate F).bits ∈ E}
  simp only [Set.mem_setOf_eq] at hIdeal
  rw [← hIdeal] at h
  exact h

end Paper2.CanonicalScannedSampler

#print axioms Paper2.CanonicalScannedSampler.scanned_matrix_D
#print axioms Paper2.CanonicalScannedSampler.scanned_run_D_le
#print axioms Paper2.CanonicalScannedSampler.scanned_ideal_table_event
#print axioms Paper2.CanonicalScannedSampler.scanned_run_event_error
#print axioms Paper2.CanonicalScannedSampler.scanned_materialize_D_le
#print axioms Paper2.CanonicalScannedSampler.scanned_materialize_matrix_event_error
#print axioms Paper2.CanonicalScannedSampler.scanned_materialize_bits_event_error
#print axioms Paper2.CanonicalScannedSampler.scanned_tapeList_D_le
#print axioms Paper2.CanonicalScannedSampler.scanned_tapeList_bits_event_error
