import CurrentAdditive.DeterministicIndexedTemplates
import CurrentAdditive.CompletePairStreams
import CurrentAdditive.GeneratedSelectorTransfer

/-!
Appendix I `det:paired`: the literal two-index selector carrier of the
generated matrix, before the paired protocol obstruction.  In particular,
equal inner coordinates with different tags are separate coordinates.
The retained pair set is measured in the original pair law.
-/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix
open Workspace.Types.CommComplexity

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

def pairDecode (z : src.inner.Label × src.inner.Label) :
    Paper2.PairedSelectorMatrix.Selector q₂ (Fin q₁ × X) :=
  (src.inner.decode z.1, src.inner.decode z.2)

def taggedDecode (z : src.inner.Label × src.inner.Label)
    (p : Bool × Fin q₂) : Fin q₁ × X :=
  src.inner.decode
    (CurrentAdditive.CompletePairStreams.pairToBool z p.1) p.2

@[simp] theorem pairDecode_coordinate (z : src.inner.Label × src.inner.Label)
    (p : Bool × Fin q₂) :
    Paper2.PairedSelectorMatrix.coordinate (pairDecode src z) p =
      taggedDecode src z p := by
  rcases p with ⟨b, i⟩
  cases b <;> rfl

/-- The two *complete* indexed inner-selector draws have exact joint
product marginals on every selected set of at most D tagged coordinates.
This invokes the actual `src.inner.exactLaw`, not an iid assumption on its
complete decoded word. -/
theorem pair_tagged_exact :
    IsDWise D
      (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw)
      (taggedDecode src)
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw := by
  classical
  exact CurrentAdditive.CompletePairStreams.paired_tagged_flatten_dwise
    D src.inner.law.toFiniteLaw
    ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
    src.inner.decode src.inner.exactLaw

/-- A retained pair set may be arbitrarily correlated. Its *actual* image
on selected tagged coordinates has at least its original pair-law mass. -/
theorem pair_tagged_image_mass
    (C : Finset (Bool × Fin q₂)) (hC : C.card ≤ D)
    (K : Set (src.inner.Label × src.inner.Label)) :
    (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw).prob (· ∈ K) ≤
      (Paper2.FiniteLaw.pi
        (fun _ : C => ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw)).prob
          (· ∈ (fun z (p : C) => taggedDecode src z p.val) '' K) := by
  exact Paper2.FiniteLaw.prob_le_image _ _ _
    (pair_tagged_exact src C hC) K

/-- The generated paired matrix on two indexed `S` labels. Ordinary and
foreign tags share the same `J₂` destination but choose different selectors. -/
def pairedIndexed (R : X → Y → Bool) :
    (src.inner.Label × src.inner.Label) → (Bool × J src) → Bool :=
  fun z c => T src R
    (CurrentAdditive.CompletePairStreams.pairToBool z c.1) c.2

@[simp] theorem pairedIndexed_entry (R : X → Y → Bool)
    (z : src.inner.Label × src.inner.Label) (c : Bool × J src) :
    pairedIndexed src R z c =
      A src R c.2.2 (taggedDecode src z (c.1, c.2.1)) := by
  rfl

/-- The selected interlace of the actual generated `A` is an actual
restriction of the indexed paired matrix. A representative pair is chosen
once per projected word for every selected row, never entry by entry. -/
theorem selected_paired_cost_le (R : X → Y → Bool)
    {n : ℕ} (e : Fin n → Bool × Fin q₂)
    (K : Set (src.inner.Label × src.inner.Label))
    (C : Set ((Bool × Fin q₂) × src.gamma.Label))
    (S : Set (Fin n × src.gamma.Label))
    (hrows : ∀ a ∈ S, (e a.1, a.2) ∈ C) :
    Paper2.Compression.restrictionD (Paper2.fullInterlace (A src R) n) S
      ((fun z i => taggedDecode src z (e i)) '' K) ≤
    Paper2.Compression.restrictionD
      (fun c z => pairedIndexed src R z (c.1.1, (c.1.2, c.2))) C K := by
  classical
  have h := CurrentAdditive.GeneratedSelectorTransfer.selected_indexed_pair_cost_le
    (A src R) (pairDecode src) e K C S hrows
  simpa only [pairDecode_coordinate, pairedIndexed_entry] using h

end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.pair_tagged_exact
#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.pair_tagged_image_mass
#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.selected_paired_cost_le
