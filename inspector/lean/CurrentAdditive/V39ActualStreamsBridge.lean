import CurrentAdditive.V39GeneratedSourceBridge
import CurrentAdditive.V39GeneratedLaws
import CurrentAdditive.DeterministicIndexedSuccessor

/-! The common-interlace input consists of the actual seven computed lists.
This adapter preserves the complete stream indices and original rational law.
No source selection or desired cost/profile certificate is supplied.
-/

namespace CurrentAdditive.V39ActualStreamsBridge

open Paper2
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.V39GeneratedConstruction
open CurrentAdditive.V39GeneratedSourceBridge

private theorem law_ext {A : Type} [Fintype A]
    (μ ν : PositiveRationalLaw A) (h : μ.weight = ν.weight) : μ = ν := by
  cases μ
  cases ν
  cases h
  rfl

variable {D q₁ q₂ s nx ny ni w : ℕ}
  [NeZero q₁] [NeZero q₂] [NeZero s]
  {μX : PositiveRationalLaw (Fin nx)} {μY : PositiveRationalLaw (Fin ny)}
  {μI : PositiveRationalLaw (Fin ni)}

theorem metadataLaw_eq :
    DeterministicIndexedMatrix.metadataLaw (s := s) μI = mixture (uniform s) μI := by
  apply law_ext
  funext a
  cases a <;> simp [DeterministicIndexedMatrix.metadataLaw, mixture,
    V39GeneratedConstruction.uniform, PositiveRationalLaw.uniform]

def toStreams
    (src : SourceData (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
    (st : src.Streams (w := w) (μI := μI)) :
    Sources.InternalStreams (toSources src) μI w where
  metadataStream := {
    Label := Fin st.metadata.size
    finite := inferInstance
    decEq := inferInstance
    law := st.metadata.law
    decode := st.metadata.decode
    exactLaw := by simpa only [metadataLaw_eq] using st.metadata.exactLaw
  }
  baseStream := st.base.source
  selectorStream := st.selector.source

theorem law_eq
    (src : SourceData (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
    (st : src.Streams (w := w) (μI := μI)) :
    Sources.InternalStreams.law (toSources src) (toStreams src st) =
      SourceData.Streams.law src st := by
  apply law_ext
  rfl

theorem decode_eq
    (src : SourceData (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
    (st : src.Streams (w := w) (μI := μI)) (t : st.Label) (i : Fin w) :
    Sources.InternalStreams.decode (toSources src) (toStreams src st) t i =
      SourceData.Streams.decode src st t i := by
  cases h : st.metadata.decode t.1 i <;>
    simp [Sources.InternalStreams.decode, toStreams, SourceData.Streams.decode,
      ExactList.source, h] <;> rfl

/-- Literal identification with the same W analyzed by common interlacing.
This equality includes the two current column families and their old indices. -/
theorem internal_entry_eq
    (src : SourceData (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
    (st : src.Streams (w := w) (μI := μI))
    (R : Fin nx → Fin ny → Bool)
    (activity : Fin ni → Fin q₂ → Option (Fin s))
    (ξ₀ : SourceMatrix.Tail s (Fin ny)) (t : st.Label)
    (a : Fin w × src.Column) :
    V38IndexedTwoTag.matrix (toSources src) R activity ξ₀ a.2
      (Sources.InternalStreams.decode (toSources src) (toStreams src st) t a.1) =
        src.B R activity (SourceData.Streams.decode src st t a.1) a.2 :=
  (matrix_eq src R activity ξ₀ a.2 _).trans (by rw [decode_eq])

variable {Q : ℕ}

theorem successor_entry_eq
    (src : SourceData (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
    (st : src.Streams (w := w) (μI := μI))
    [NeZero w]
    (out : ExactList D Q (Fin w × src.Column) (product (uniform w) src.columnLaw))
    (R : Fin nx → Fin ny → Bool)
    (activity : Fin ni → Fin q₂ → Option (Fin s))
    (ξ₀ : SourceMatrix.Tail s (Fin ny)) (j : Fin out.size) (a : Fin Q × st.Label) :
    src.successor st out R activity j a =
      V38IndexedTwoTag.matrix (toSources src) R activity ξ₀ (out.decode j a.1).2
        (Sources.InternalStreams.decode (toSources src) (toStreams src st)
          a.2 (out.decode j a.1).1) :=
  (internal_entry_eq src st R activity ξ₀ a.2 (out.decode j a.1)).symm

end CurrentAdditive.V39ActualStreamsBridge

#print axioms CurrentAdditive.V39ActualStreamsBridge.toStreams
#print axioms CurrentAdditive.V39ActualStreamsBridge.law_eq
#print axioms CurrentAdditive.V39ActualStreamsBridge.successor_entry_eq
