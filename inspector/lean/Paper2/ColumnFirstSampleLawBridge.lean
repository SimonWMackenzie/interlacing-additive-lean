import Paper2.SampledTableLawConjugacy
import Paper2.RecursiveSamplingTable

/-! Explicit bridge from a row-first mathematical product to the literal
column-first sampled pair and table program. -/

namespace Paper2.ColumnFirstSampleLawBridge

open SourceMatrix SourceSuccessorConjugacy

variable {X X' Y Y' V : Type} {s q₁ q₂ w Q : ℕ}
variable [Fintype X] [Fintype X'] [Fintype Y] [Fintype Y']
  [Fintype V] [Nonempty V] [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q]

/-- Reorder the two whole sample tuples without changing either set of
labels or the indices within a tuple. -/
def swapEquiv (k mX mY : ℕ) :
    ((Fin mX → RecursiveEntries.Row X Y (SourceConstruction.Items s V) s q₁ q₂ w Q k) ×
      (Fin mY → RecursiveEntries.Column X Y (SourceConstruction.Items s V) s q₁ q₂ w Q k)) ≃
    ((Fin mY → RecursiveEntries.Column X Y (SourceConstruction.Items s V) s q₁ q₂ w Q k) ×
      (Fin mX → RecursiveEntries.Row X Y (SourceConstruction.Items s V) s q₁ q₂ w Q k)) :=
  Equiv.prodComm _ _

/-- The literal `RecursiveSampling.sampleLaw` is column-first, whereas
`SampledTableLawConjugacy.pairedLaw` is row-first. This is their exact
pointwise rational weight relation, not an identification by fiat. -/
theorem swap_weight (hs : 4 ≤ s)
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (k mX mY : ℕ)
    (p : (Fin mX → RecursiveEntries.Row X Y (SourceConstruction.Items s V) s q₁ q₂ w Q k) ×
      (Fin mY → RecursiveEntries.Column X Y (SourceConstruction.Items s V) s q₁ q₂ w Q k)) :
    (RecursiveSampling.sampleLaw (V := V) (q₁ := q₁) (q₂ := q₂)
      (w := w) (Q := Q) hs μ ν k mX mY).weight (swapEquiv k mX mY p) =
    (SampledTableLawConjugacy.pairedLaw (V := V) (q₁ := q₁) (q₂ := q₂)
      (w := w) (Q := Q) hs μ ν k mX mY).weight p := by
  let L := RecursiveSampling.laws (V := V) (q₁ := q₁) (q₂ := q₂)
    (w := w) (Q := Q) hs μ ν k
  change (L.2.iid mY).weight p.2 * (L.1.iid mX).weight p.1 =
    (L.1.iid mX).weight p.1 * (L.2.iid mY).weight p.2
  exact mul_comm _ _

private theorem pushes_of_weight {B C : Type} [Fintype B] [Fintype C]
    (α : PositiveRationalLaw B) (β : PositiveRationalLaw C)
    (e : B ≃ C) (h : ∀ b, β.weight (e b) = α.weight b) :
    α.toFiniteLaw.PushesTo β.toFiniteLaw e := by
  intro E
  classical
  unfold FiniteLaw.prob
  have hs := e.sum_comp (fun c => if E c then (β.weight c : ℝ) else 0)
  simpa only [PositiveRationalLaw.toFiniteLaw, h] using hs

/-- Every event on the actual column-first sample pair has the same mass
as its swapped event on the row-first pair. -/
theorem swap_event_prob (hs : 4 ≤ s)
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (k mX mY : ℕ)
    (E : ((Fin mY → RecursiveEntries.Column X Y (SourceConstruction.Items s V) s q₁ q₂ w Q k) ×
      (Fin mX → RecursiveEntries.Row X Y (SourceConstruction.Items s V) s q₁ q₂ w Q k)) → Prop) :
    (SampledTableLawConjugacy.pairedLaw (V := V) (q₁ := q₁) (q₂ := q₂)
      (w := w) (Q := Q) hs μ ν k mX mY).toFiniteLaw.prob
        (fun p => E (swapEquiv k mX mY p)) =
    (RecursiveSampling.sampleLaw (V := V) (q₁ := q₁) (q₂ := q₂)
      (w := w) (Q := Q) hs μ ν k mX mY).toFiniteLaw.prob E :=
  pushes_of_weight _ _ _ (swap_weight hs μ ν k mX mY) E

/-- Equality of every full-table event under the literal column-first
`RecursiveSampling.sampleLaw` on both sides. The actual table consumes
`p.2` as rows and `p.1` as columns. -/
theorem column_first_table_event_prob [NeZero s] (hs : 4 ≤ s)
    (μ : PositiveRationalLaw X) (μ' : PositiveRationalLaw X')
    (ν : PositiveRationalLaw Y) (ν' : PositiveRationalLaw Y')
    (π : Fin q₂ ≃ Fin q₂) (eX : X ≃ X') (eY : Y ≃ Y')
    (hX : ∀ x, μ'.weight (eX x) = μ.weight x)
    (hY : ∀ y, ν'.weight (eY y) = ν.weight y)
    (F : X → Y → Bool) (F' : X' → Y' → Bool)
    (hF : ∀ x y, F' (eX x) (eY y) = F x y)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : RecursiveEntries.Tails X Y (SourceConstruction.Items s V) s q₁ q₂ w Q)
    (k mX mY : ℕ) (E : (Fin mX → Fin mY → Bool) → Prop) :
    (RecursiveSampling.sampleLaw (V := V) (q₁ := q₁) (q₂ := q₂)
      (w := w) (Q := Q) hs μ ν k mX mY).toFiniteLaw.prob
        (fun p => E (RecursiveEntries.table F activity ξ k p.2 p.1)) =
    (RecursiveSampling.sampleLaw (V := V) (q₁ := q₁) (q₂ := q₂)
      (w := w) (Q := Q) hs μ' ν' k mX mY).toFiniteLaw.prob
        (fun p => E (RecursiveEntries.table F'
          (SourceCoordinateConjugacy.activityNew π activity)
          (tailsMap π eX eY ξ) k p.2 p.1)) := by
  have hOld := swap_event_prob (V := V) (q₁ := q₁) (q₂ := q₂)
    (w := w) (Q := Q) hs μ ν k mX mY
    (fun p => E (RecursiveEntries.table F activity ξ k p.2 p.1))
  have hNew := swap_event_prob (V := V) (q₁ := q₁) (q₂ := q₂)
    (w := w) (Q := Q) hs μ' ν' k mX mY
    (fun p => E (RecursiveEntries.table F'
      (SourceCoordinateConjugacy.activityNew π activity)
      (tailsMap π eX eY ξ) k p.2 p.1))
  have hMiddle := SampledTableLawConjugacy.table_event_prob
    (V := V) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
    hs μ μ' ν ν' π eX eY hX hY F F' hF activity ξ k mX mY E
  exact hOld.symm.trans (hMiddle.trans hNew)

/-- The law identity reaches the existing finite-choice table programs when
each seed program is known to generate its respective base law. The two
programs are not asserted to agree on any particular bit tape. -/
theorem tableProgram_event_conjugacy [NeZero s]
    (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (row₀ : RecursiveSamplingProgram.Program X)
    (col₀ : RecursiveSamplingProgram.Program Y)
    (row₀' : RecursiveSamplingProgram.Program X')
    (col₀' : RecursiveSamplingProgram.Program Y')
    (μ : PositiveRationalLaw X) (μ' : PositiveRationalLaw X')
    (ν : PositiveRationalLaw Y) (ν' : PositiveRationalLaw Y')
    (hr : RecursiveSamplingLaws.Generates row₀ μ.toFiniteLaw)
    (hc : RecursiveSamplingLaws.Generates col₀ ν.toFiniteLaw)
    (hr' : RecursiveSamplingLaws.Generates row₀' μ'.toFiniteLaw)
    (hc' : RecursiveSamplingLaws.Generates col₀' ν'.toFiniteLaw)
    (π : Fin q₂ ≃ Fin q₂) (eX : X ≃ X') (eY : Y ≃ Y')
    (hX : ∀ x, μ'.weight (eX x) = μ.weight x)
    (hY : ∀ y, ν'.weight (eY y) = ν.weight y)
    (F : X → Y → Bool) (F' : X' → Y' → Bool)
    (hF : ∀ x y, F' (eX x) (eY y) = F x y)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : RecursiveEntries.Tails X Y (SourceConstruction.Items s V) s q₁ q₂ w Q)
    (k mX mY : ℕ) (E : Set (Fin mX → Fin mY → Bool)) :
    (RecursiveSampling.tableProgram (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
      order hs row₀ col₀ F activity ξ k mX mY).eventProb E =
    (RecursiveSampling.tableProgram (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
      order hs row₀' col₀' F'
        (SourceCoordinateConjugacy.activityNew π activity)
        (tailsMap π eX eY ξ) k mX mY).eventProb E := by
  have hOld := RecursiveSampling.tableProgram_event
    (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
    order hs row₀ col₀ μ ν hr hc F activity ξ k mX mY E
  have hNew := RecursiveSampling.tableProgram_event
    (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
    order hs row₀' col₀' μ' ν' hr' hc' F'
    (SourceCoordinateConjugacy.activityNew π activity)
    (tailsMap π eX eY ξ) k mX mY E
  have hLaw := column_first_table_event_prob
    (V := V) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
    hs μ μ' ν ν' π eX eY hX hY F F' hF activity ξ k mX mY
    (fun table => table ∈ E)
  calc
    (RecursiveSampling.tableProgram (q₁ := q₁) (q₂ := q₂)
      (w := w) (Q := Q) order hs row₀ col₀ F activity ξ k mX mY).eventProb E =
      (RecursiveSampling.sampleLaw (V := V) (q₁ := q₁) (q₂ := q₂)
        (w := w) (Q := Q) hs μ ν k mX mY).toFiniteLaw.prob
          (fun p => RecursiveEntries.table F activity ξ k p.2 p.1 ∈ E) := by
        simpa only [RecursiveEntries.table_eq_sampleMatrix] using hOld
    _ = (RecursiveSampling.sampleLaw (V := V) (q₁ := q₁) (q₂ := q₂)
        (w := w) (Q := Q) hs μ' ν' k mX mY).toFiniteLaw.prob
          (fun p => RecursiveEntries.table F'
            (SourceCoordinateConjugacy.activityNew π activity)
            (tailsMap π eX eY ξ) k p.2 p.1 ∈ E) := hLaw
    _ = (RecursiveSampling.tableProgram (q₁ := q₁) (q₂ := q₂)
      (w := w) (Q := Q) order hs row₀' col₀' F'
        (SourceCoordinateConjugacy.activityNew π activity)
        (tailsMap π eX eY ξ) k mX mY).eventProb E := by
      simpa only [RecursiveEntries.table_eq_sampleMatrix] using hNew.symm

end Paper2.ColumnFirstSampleLawBridge

#print axioms Paper2.ColumnFirstSampleLawBridge.swap_weight
#print axioms Paper2.ColumnFirstSampleLawBridge.swap_event_prob
#print axioms Paper2.ColumnFirstSampleLawBridge.column_first_table_event_prob
#print axioms Paper2.ColumnFirstSampleLawBridge.tableProgram_event_conjugacy
