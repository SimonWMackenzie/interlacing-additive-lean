import Paper2.RecursiveSampling
import Paper2.RecursiveSamplingCapped

/-!
# Independently sampled labels and their actual printed intersections

Frozen v12 Appendix D, first paragraph and bounded-tape implementation.
Columns are generated first, then independently rows. Their intersections
are evaluated by the same one-entry recursive evaluator. The resulting
finite-choice program has a public request bound, retains duplicate labels,
and has the precise intended joint sampling law. These statements do not
bound the time or storage used to print its table.
-/

namespace Paper2.RecursiveSampling

open SourceMatrix RecursiveEntries RecursiveSamplingProgram RecursiveSamplingLaws

variable {X₀ Y₀ V : Type} [Fintype V] [Nonempty V]
  {s q₁ q₂ w Q : ℕ} [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q]

def samples (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (row₀ : Program X₀) (col₀ : Program Y₀) (k mX mY : ℕ) :=
  let p := programs (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) order hs row₀ col₀ k
  prod (iid p.2 mY) (iid p.1 mX)

noncomputable def sampleLaw [Fintype X₀] [Fintype Y₀] (hs : 4 ≤ s)
    (μ₀ : PositiveRationalLaw X₀) (ν₀ : PositiveRationalLaw Y₀) (k mX mY : ℕ) :=
  let p := laws (V := V) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) hs μ₀ ν₀ k
  (p.2.iid mY).prod (p.1.iid mX)

theorem generates_samples [Fintype X₀] [Fintype Y₀]
    (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (row₀ : Program X₀) (col₀ : Program Y₀)
    (μ₀ : PositiveRationalLaw X₀) (ν₀ : PositiveRationalLaw Y₀)
    (hr : Generates row₀ μ₀.toFiniteLaw) (hc : Generates col₀ ν₀.toFiniteLaw)
    (k mX mY : ℕ) :
    Generates (samples (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
      order hs row₀ col₀ k mX mY) (sampleLaw (V := V) hs μ₀ ν₀ k mX mY).toFiniteLaw := by
  obtain ⟨hrk, hck⟩ := programs_generate (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
    order hs row₀ col₀ μ₀ ν₀ hr hc k
  exact generates_rational_prod (generates_rational_iid hck mY) (generates_rational_iid hrk mX)

def sampleDrawBound (s q₁ q₂ w Q r₀ c₀ k mX mY : ℕ) : ℕ :=
  1 + mY * (drawBounds s q₁ q₂ w Q r₀ c₀ k).2 +
    mX * (drawBounds s q₁ q₂ w Q r₀ c₀ k).1

theorem samples_drawBound
    (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (row₀ : Program X₀) (col₀ : Program Y₀) (r₀ c₀ : ℕ)
    (hr : row₀.maxDraws ≤ r₀) (hc : col₀.maxDraws ≤ c₀) (k mX mY : ℕ) :
    (samples (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
      order hs row₀ col₀ k mX mY).maxDraws ≤ sampleDrawBound s q₁ q₂ w Q r₀ c₀ k mX mY := by
  obtain ⟨hrk, hck⟩ := programs_drawBounds (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
    order hs row₀ col₀ r₀ c₀ hr hc k
  apply (maxDraws_prod_le _ _).trans
  have hrow := (maxDraws_iid_le _ mX).trans (Nat.mul_le_mul_left mX hrk)
  have hcol := (maxDraws_iid_le _ mY).trans (Nat.mul_le_mul_left mY hck)
  unfold sampleDrawBound
  omega

theorem samples_alphabetBound
    (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (row₀ : Program X₀) (col₀ : Program Y₀) (M : ℕ)
    (h512 : 512 ≤ M) (hq₁ : q₁ ≤ M) (hq₂ : q₂ ≤ M) (h4s : 4 * s ≤ M)
    (hw : w ≤ M) (hQ : Q ≤ M) (hV : Fintype.card V ≤ M)
    (hr : row₀.maxAlphabet ≤ M) (hc : col₀.maxAlphabet ≤ M) (k mX mY : ℕ) :
    (samples (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
      order hs row₀ col₀ k mX mY).maxAlphabet ≤ M := by
  obtain ⟨hrk, hck⟩ := programs_alphabetBound (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
    order hs row₀ col₀ M h512 hq₁ hq₂ h4s hw hQ hV hr hc k
  exact (maxAlphabet_prod_le _ _).trans
    (max_le ((maxAlphabet_iid_le _ mY).trans hck) ((maxAlphabet_iid_le _ mX).trans hrk))

/-- The deterministic output phase applies the verified recursive evaluator
to the generated labels; equal labels retain their separate array indices. -/
def tableProgram [NeZero s] (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (row₀ : Program X₀) (col₀ : Program Y₀) (F : X₀ → Y₀ → Bool)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : Tails X₀ Y₀ (SourceConstruction.Items s V) s q₁ q₂ w Q) (k mX mY : ℕ) :
    Program (Fin mX → Fin mY → Bool) :=
  Program.map (fun p => RecursiveEntries.table F activity ξ k p.2 p.1)
    (samples order hs row₀ col₀ k mX mY)

theorem tableProgram_event [Fintype X₀] [Fintype Y₀] [NeZero s]
    (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (row₀ : Program X₀) (col₀ : Program Y₀)
    (μ₀ : PositiveRationalLaw X₀) (ν₀ : PositiveRationalLaw Y₀)
    (hr : Generates row₀ μ₀.toFiniteLaw) (hc : Generates col₀ ν₀.toFiniteLaw)
    (F : X₀ → Y₀ → Bool)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : Tails X₀ Y₀ (SourceConstruction.Items s V) s q₁ q₂ w Q) (k mX mY : ℕ)
    (E : Set (Fin mX → Fin mY → Bool)) :
    (tableProgram order hs row₀ col₀ F activity ξ k mX mY).eventProb E =
      (sampleLaw (V := V) hs μ₀ ν₀ k mX mY).toFiniteLaw.prob
        (fun p => sampleMatrix (RecursiveEntries.matrix F activity ξ k) p.2 p.1 ∈ E) := by
  classical
  have hgen := generates_samples (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
    order hs row₀ col₀ μ₀ ν₀ hr hc k mX mY
  rw [tableProgram, Program.eventProb, Program.expect_map]
  rw [hgen]
  simp only [Set.indicator_apply, FiniteLaw.prob, mul_ite, mul_one, mul_zero,
    RecursiveEntries.table_eq_sampleMatrix]

end Paper2.RecursiveSampling
