import CurrentAdditive.V39StoredGenerated
import CurrentAdditive.GeneratedPairwiseMissedEvents

/-! Exact positive singleton marginals force every original letter to occur.
The lower bounds here concern the actual retained indices of Code D, without
identifying duplicate decoded words. They are used to charge public headers
against the table which is actually printed.
-/

namespace CurrentAdditive.V39GeneratedConstruction

open Paper2
open scoped BigOperators

namespace ExactList

theorem decode_surjective {D q : ℕ} {A : Type} [Fintype A] [DecidableEq A]
    {μ : PositiveRationalLaw A} (src : ExactList D q A μ)
    (hD : 1 ≤ D) (i : Fin q) : Function.Surjective (fun j => src.decode j i) := by
  classical
  intro a
  by_contra hn
  have hne : ∀ j, src.decode j i ≠ a := by simpa using hn
  have h := GeneratedPairwiseMissedEvents.dwise_single_event D
    src.law.toFiniteLaw src.decode μ.toFiniteLaw hD src.exactLaw i (fun x => x = a)
  have hzero : src.law.toFiniteLaw.prob (fun j => src.decode j i = a) = 0 := by
    simp [FiniteLaw.prob, hne]
  rw [hzero, FiniteLaw.prob_singleton] at h
  have hp : 0 < μ.toFiniteLaw.weight a := by
    change (0 : ℝ) < (μ.weight a : ℝ)
    exact_mod_cast μ.positive a
  linarith

theorem card_le_size {D q : ℕ} {A : Type} [Fintype A] [DecidableEq A]
    {μ : PositiveRationalLaw A} (src : ExactList D q A μ)
    (hD : 1 ≤ D) (hq : 0 < q) : Fintype.card A ≤ src.size := by
  have h := Fintype.card_le_of_surjective _
    (src.decode_surjective hD ⟨0,hq⟩)
  simpa only [Fintype.card_fin] using h

theorem size_pos {D q : ℕ} {A : Type} [Fintype A] [DecidableEq A]
    {μ : PositiveRationalLaw A} (src : ExactList D q A μ) : 0 < src.size :=
  law_size_pos src.law

end ExactList

variable {q₁ q₂ s w Q ni : ℕ}
  [NeZero q₁] [NeZero q₂] [NeZero s] [NeZero w] [NeZero Q]

/-- The actual seventh source retains at least one original label for every
origin and tagged source column; the column list retains all base letters. -/
theorem executableStep_dimension_lower (μI : PositiveRationalLaw (Fin ni))
    (activity : Fin ni → Fin q₂ → Option (Fin s)) (R : NumberedMatrix) :
    w*q₂*R.cols ≤
        (executableStep (q₁ := q₁) (s := s) (w := w) (Q := Q) μI activity R).rows ∧
    Q*R.rows ≤
        (executableStep (q₁ := q₁) (s := s) (w := w) (Q := Q) μI activity R).cols := by
  let c := executableCodeD 8192
  let src := sourceData (q₁ := q₁) (q₂ := q₂) (s := s) c R.rowLaw R.colLaw
  let st := SourceData.streams (w := w) c src (μI := μI)
  let out := SourceData.final (w := w) (Q := Q) c src
  have hg : R.cols ≤ src.gamma.size := by
    simpa only [Fintype.card_fin] using src.gamma.card_le_size (by decide) (by omega)
  have ho : w*(src.outer.size*src.gamma.size+q₂*src.gamma.size) ≤ out.size := by
    simpa only [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin]
      using out.card_le_size (by decide) (NeZero.pos Q)
  have hb : R.rows ≤ st.base.size := by
    simpa only [Fintype.card_fin] using st.base.card_le_size (by decide) (NeZero.pos w)
  have hm := st.metadata.size_pos
  have hs := st.selector.size_pos
  constructor
  · change w*q₂*R.cols ≤ out.size
    have h₁ := Nat.mul_le_mul_left q₂ hg
    have h₂ := Nat.mul_le_mul_left w h₁
    calc
      w*q₂*R.cols = w*(q₂*R.cols) := by ring
      _ ≤ w*(q₂*src.gamma.size) := h₂
      _ ≤ w*(src.outer.size*src.gamma.size+q₂*src.gamma.size) :=
        Nat.mul_le_mul_left w (Nat.le_add_left _ _)
      _ ≤ out.size := ho
  · change Q*R.rows ≤ Q*(st.metadata.size*(st.base.size*st.selector.size))
    apply Nat.mul_le_mul_left
    have h₁ : st.base.size ≤ st.base.size*st.selector.size := by nlinarith
    have h₂ : st.base.size*st.selector.size ≤
        st.metadata.size*(st.base.size*st.selector.size) := by nlinarith
    exact hb.trans (h₁.trans h₂)

theorem storedStep_entries_lower (μI : PositiveRationalLaw (Fin ni))
    (activity : Fin ni → Fin q₂ → Option (Fin s)) (R : StoredMatrix) :
    (w*q₂*Q)*(R.rows*R.cols) ≤
      (StoredMatrix.step (q₁ := q₁) (s := s) (w := w) (Q := Q) μI activity R).rows *
      (StoredMatrix.step (q₁ := q₁) (s := s) (w := w) (Q := Q) μI activity R).cols := by
  have h := executableStep_dimension_lower (q₁ := q₁) (s := s) (w := w) (Q := Q)
    μI activity R.numbered
  convert Nat.mul_le_mul h.1 h.2 using 1 <;> simp only [StoredMatrix.step,
    StoredMatrix.ofNumbered, StoredMatrix.numbered] <;> ring

theorem storedIterate_entries_lower (μI : PositiveRationalLaw (Fin ni))
    (activity : Fin ni → Fin q₂ → Option (Fin s)) (R : StoredMatrix) (k : ℕ) :
    (w*q₂*Q)^k*(R.rows*R.cols) ≤
      (StoredMatrix.iterate (q₁ := q₁) (s := s) (w := w) (Q := Q) μI activity k R).rows *
      (StoredMatrix.iterate (q₁ := q₁) (s := s) (w := w) (Q := Q) μI activity k R).cols := by
  induction k with
  | zero => simp [StoredMatrix.iterate]
  | succ k ih =>
    have h := storedStep_entries_lower (q₁ := q₁) (s := s) (w := w) (Q := Q)
      μI activity (StoredMatrix.iterate (q₁ := q₁) (s := s) (w := w) (Q := Q) μI activity k R)
    exact (by simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm]
      using (Nat.mul_le_mul_left (w*q₂*Q) ih).trans h)

end CurrentAdditive.V39GeneratedConstruction

#print axioms CurrentAdditive.V39GeneratedConstruction.ExactList.decode_surjective
#print axioms CurrentAdditive.V39GeneratedConstruction.storedIterate_entries_lower
