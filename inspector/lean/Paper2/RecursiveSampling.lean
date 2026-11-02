import Paper2.RecursiveSamplingGraph
import Paper2.RecursiveSamplingAlphabet
import Paper2.RecursiveDefaults

/-!
# Recursive generators on the same carriers as the entry evaluator

Frozen v12 Appendix D, `eq:recursive-entry` and the input-label paragraphs.
The recursion alternates the preceding column and row generators exactly as
the two-transpose successor requires. Positive rational laws are built on
those very carriers, and the programs generate those laws, not surrogate
labels. The bounds count uniform-choice requests in the actual program.
They do not charge tuple scans, storage or machine-time execution.
-/

namespace Paper2.RecursiveSampling

open SourceMatrix RecursiveSamplingProgram RecursiveSamplingLaws RecursiveEntries

variable {X₀ Y₀ V : Type} [Fintype V] [Nonempty V]
  {s q₁ q₂ w Q : ℕ} [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q]

/-- Generate the actual pair of successor input carriers. The graph's
public vertex encoding is the only item-label enumeration supplied here. -/
def programs (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (row₀ : Program X₀) (col₀ : Program Y₀) :
    (k : ℕ) → Program (Row X₀ Y₀ (SourceConstruction.Items s V) s q₁ q₂ w Q k) ×
      Program (Column X₀ Y₀ (SourceConstruction.Items s V) s q₁ q₂ w Q k)
  | 0 => (row₀, col₀)
  | k + 1 =>
      let previous := programs order hs row₀ col₀ k
      (iid (prod (uniform w) (tagged previous.2)) Q,
        prod (uniform Q) (iid (graphRows order hs previous.1) w))

/-- Exact laws on the same recursive labels, with the protected mixtures
inside each source step and independent outer interlace products. -/
noncomputable def laws [Fintype X₀] [Fintype Y₀] (hs : 4 ≤ s)
    (μ₀ : PositiveRationalLaw X₀) (ν₀ : PositiveRationalLaw Y₀) :
    (k : ℕ) →
      PositiveRationalLaw (Row X₀ Y₀ (SourceConstruction.Items s V) s q₁ q₂ w Q k) ×
      PositiveRationalLaw (Column X₀ Y₀ (SourceConstruction.Items s V) s q₁ q₂ w Q k)
  | 0 => (μ₀, ν₀)
  | k + 1 =>
      let previous := laws hs μ₀ ν₀ k
      (((PositiveRationalLaw.uniform (Fin w)).prod
          (SourceLawBinding.matrixRowLaw previous.2 q₁ q₂ s)).iid Q,
        (PositiveRationalLaw.uniform (Fin Q)).prod
          ((SourceLawBinding.matrixColumnLaw previous.1 q₁ q₂ s hs).iid w))

theorem programs_generate [Fintype X₀] [Fintype Y₀]
    (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (row₀ : Program X₀) (col₀ : Program Y₀)
    (μ₀ : PositiveRationalLaw X₀) (ν₀ : PositiveRationalLaw Y₀)
    (hrow : Generates row₀ μ₀.toFiniteLaw) (hcol : Generates col₀ ν₀.toFiniteLaw) (k : ℕ) :
    Generates (programs (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) order hs row₀ col₀ k).1
        (laws (V := V) hs μ₀ ν₀ k).1.toFiniteLaw ∧
      Generates (programs (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) order hs row₀ col₀ k).2
        (laws (V := V) hs μ₀ ν₀ k).2.toFiniteLaw := by
  induction k with
  | zero => exact ⟨hrow, hcol⟩
  | succ k ih =>
      exact ⟨generates_rational_iid
        (generates_rational_prod (generates_uniform w) (generates_tagged ih.2)) Q,
        generates_rational_prod (generates_uniform Q)
          (generates_rational_iid (generates_graphRows order hs ih.1) w)⟩

/-- A public pair of uniform-request caps, tied by the following theorem
to the generated recursive labels. Each tag and each selector is charged. -/
def drawBounds (s q₁ q₂ w Q row₀ col₀ : ℕ) : ℕ → ℕ × ℕ
  | 0 => (row₀, col₀)
  | k + 1 =>
      let previous := drawBounds s q₁ q₂ w Q row₀ col₀ k
      (Q * (2 + s + ((s + 1) + s * (q₁ + s + 1)) * previous.2),
        1 + w * (3 + q₂ * (1 + previous.1)))

theorem programs_drawBounds
    (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (row₀ : Program X₀) (col₀ : Program Y₀) (r₀ c₀ : ℕ)
    (hr : Program.maxDraws row₀ ≤ r₀) (hc : Program.maxDraws col₀ ≤ c₀) (k : ℕ) :
    Program.maxDraws (programs (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
        order hs row₀ col₀ k).1 ≤ (drawBounds s q₁ q₂ w Q r₀ c₀ k).1 ∧
      Program.maxDraws (programs (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
        order hs row₀ col₀ k).2 ≤ (drawBounds s q₁ q₂ w Q r₀ c₀ k).2 := by
  induction k with
  | zero => exact ⟨hr, hc⟩
  | succ k ih =>
      let previous := programs (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) order hs row₀ col₀ k
      let bounds := drawBounds s q₁ q₂ w Q r₀ c₀ k
      have ihr : Program.maxDraws previous.1 ≤ bounds.1 := ih.1
      have ihc : Program.maxDraws previous.2 ≤ bounds.2 := ih.2
      have htag := maxDraws_tagged_le (q₁ := q₁) (q₂ := q₂) (s := s) (by omega) previous.2
      have hrow := maxDraws_graphRows_le (q₁ := q₁) (q₂ := q₂) order hs previous.1
      constructor
      · change Program.maxDraws (iid (prod (uniform w) (tagged previous.2)) Q) ≤
          Q * (2 + s + ((s + 1) + s * (q₁ + s + 1)) * bounds.2)
        apply (maxDraws_iid_le _ Q).trans
        apply Nat.mul_le_mul_left Q
        apply (maxDraws_prod_le _ _).trans
        simp only [uniform, Program.maxDraws_uniform]
        have hm := Nat.mul_le_mul_left ((s + 1) + s * (q₁ + s + 1)) ihc
        omega
      · change Program.maxDraws (prod (uniform Q) (iid (graphRows order hs previous.1) w)) ≤
          1 + w * (3 + q₂ * (1 + bounds.1))
        apply (maxDraws_prod_le _ _).trans
        simp only [uniform, Program.maxDraws_uniform]
        apply Nat.add_le_add_left
        apply (maxDraws_iid_le _ w).trans
        apply Nat.mul_le_mul_left w
        have hm := Nat.mul_le_mul_left q₂ (Nat.add_le_add_left ihr 1)
        omega

/-- Tuple length increases the number of requests but not their alphabet.
One cap on the public scalar choices works at every recursive level. -/
theorem programs_alphabetBound
    (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (row₀ : Program X₀) (col₀ : Program Y₀) (M : ℕ)
    (h512 : 512 ≤ M) (hq₁ : q₁ ≤ M) (hq₂ : q₂ ≤ M) (h4s : 4 * s ≤ M)
    (hw : w ≤ M) (hQ : Q ≤ M) (hV : Fintype.card V ≤ M)
    (hr : Program.maxAlphabet row₀ ≤ M) (hc : Program.maxAlphabet col₀ ≤ M) (k : ℕ) :
    Program.maxAlphabet (programs (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
        order hs row₀ col₀ k).1 ≤ M ∧
      Program.maxAlphabet (programs (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
        order hs row₀ col₀ k).2 ≤ M := by
  induction k with
  | zero => exact ⟨hr, hc⟩
  | succ k ih =>
      constructor
      · apply (maxAlphabet_iid_le _ Q).trans
        apply (maxAlphabet_prod_le _ _).trans
        refine max_le ?_ (maxAlphabet_tagged_le _ M (by omega) hq₂ ih.2)
        simpa only [uniform, Program.maxAlphabet_uniform] using hw
      · apply (maxAlphabet_prod_le _ _).trans
        apply max_le
        · simpa only [uniform, Program.maxAlphabet_uniform] using hQ
        · exact (maxAlphabet_iid_le _ w).trans
            (maxAlphabet_graphRows_le order hs _ M h512 hq₁ h4s hV ih.1)

theorem base_column_coefficient (hqs : q₁ + 2 = s) :
    (s + 1) + s * (q₁ + s + 1) = 2 * s ^ 2 + 1 := by
  nlinarith

end Paper2.RecursiveSampling
