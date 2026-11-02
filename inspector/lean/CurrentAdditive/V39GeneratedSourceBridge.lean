import CurrentAdditive.V38IndexedTwoTag
import CurrentAdditive.V39GeneratedConstruction

/-! Bind the collision supplier's indexed two-family carrier to the actual
literal SourceData constructor. This bridge has no NO/profile hypothesis.
The same index labels, entries and input weights occur on both sides. -/

namespace CurrentAdditive.V39GeneratedSourceBridge

open Paper2 CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.V39GeneratedConstruction

private theorem law_eq_of_weights {A : Type*} [Fintype A]
    (μ ν : PositiveRationalLaw A) (h : μ.weight = ν.weight) : μ = ν := by
  cases μ
  cases ν
  cases h
  rfl

theorem uniform_eq (n : ℕ) [NeZero n] :
    V39GeneratedConstruction.uniform n = PositiveRationalLaw.uniform (Fin n) := by
  apply law_eq_of_weights
  funext i
  simp [V39GeneratedConstruction.uniform, PositiveRationalLaw.uniform]

theorem product_eq {A B : Type} [Fintype A] [Fintype B]
    (μ : PositiveRationalLaw A) (ν : PositiveRationalLaw B) :
    V39GeneratedConstruction.product μ ν = μ.prod ν := by
  apply law_eq_of_weights
  rfl

variable {D q₁ q₂ s nx ny ni : ℕ}
  [NeZero q₁] [NeZero q₂] [NeZero s]
  {μX : PositiveRationalLaw (Fin nx)} {μY : PositiveRationalLaw (Fin ny)}

/-- Reuse the literal exact lists with their original finite ordinals.
No quotient, extra labels or altered decoder is introduced. -/
def toSources (src : SourceData (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY) :
    Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY where
  gamma := src.gamma.source
  inner := {
    Label := Fin src.inner.size
    finite := inferInstance
    decEq := inferInstance
    law := src.inner.law
    decode := src.inner.decode
    exactLaw := by
      simpa only [product_eq, uniform_eq] using src.inner.exactLaw
  }
  outer := {
    Label := Fin src.outer.size
    finite := inferInstance
    decEq := inferInstance
    law := src.outer.law
    decode := src.outer.decode
    exactLaw := by
      simpa only [product_eq, uniform_eq] using src.outer.exactLaw
  }

theorem matrix_eq (src : SourceData (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
    (R : Fin nx → Fin ny → Bool)
    (activity : Fin ni → Fin q₂ → Option (Fin s))
    (ξ₀ : Paper2.SourceMatrix.Tail s (Fin ny))
    (c : src.Column) (a : src.Row (ni := ni)) :
    V38IndexedTwoTag.matrix (toSources src) R activity ξ₀ c a =
      src.B R activity a c := by
  cases c <;> cases a <;> rfl

theorem columnLaw_eq
    (src : SourceData (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY) :
    V38IndexedTwoTag.law (toSources src) = src.columnLaw := by
  apply law_eq_of_weights
  funext c
  cases c <;> simp [V38IndexedTwoTag.law, toSources,
    SourceData.columnLaw, V39GeneratedConstruction.mixture,
    V39GeneratedConstruction.product, V39GeneratedConstruction.uniform,
    PositiveRationalLaw.prod, PositiveRationalLaw.uniform, ExactList.source]

end CurrentAdditive.V39GeneratedSourceBridge

#print axioms CurrentAdditive.V39GeneratedSourceBridge.uniform_eq
#print axioms CurrentAdditive.V39GeneratedSourceBridge.product_eq
#print axioms CurrentAdditive.V39GeneratedSourceBridge.toSources
#print axioms CurrentAdditive.V39GeneratedSourceBridge.matrix_eq
#print axioms CurrentAdditive.V39GeneratedSourceBridge.columnLaw_eq
