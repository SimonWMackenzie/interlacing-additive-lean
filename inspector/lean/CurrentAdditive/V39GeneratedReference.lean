import CurrentAdditive.V39IndexedReferenceProfile
import CurrentAdditive.V39GeneratedSourceBridge

/-! The reference profile's row law and ordinary entries are exactly those
of the actual finite-index SourceData constructor. -/

namespace CurrentAdditive.V39GeneratedReference

open Paper2
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.V39GeneratedConstruction
open CurrentAdditive.V39GeneratedSourceBridge

private theorem rationalLaw_ext {A : Type*} [Fintype A]
    (μ ν : PositiveRationalLaw A) (h : μ.weight = ν.weight) : μ = ν := by
  cases μ
  cases ν
  cases h
  rfl

variable {q₁ q₂ s nx ny ni : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
  {μX : PositiveRationalLaw (Fin nx)} {μY : PositiveRationalLaw (Fin ny)}

theorem rowLaw_eq
    (src : SourceData (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
    (μI : PositiveRationalLaw (Fin ni)) :
    V39IndexedReferenceProfile.rowLaw (toSources src) μI = src.rowLaw (μI := μI) := by
  apply rationalLaw_ext
  funext a
  cases a <;> simp [V39IndexedReferenceProfile.rowLaw,toSources,SourceData.rowLaw,
    mixture,product,uniform,PositiveRationalLaw.prod,PositiveRationalLaw.uniform,ExactList.source]

def reference
    (src : SourceData (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
    (R : Fin nx → Fin ny → Bool)
    (activity : Fin ni → Fin q₂ → Option (Fin s)) :
    (Fin src.outer.size × Fin src.gamma.size) → src.Row (ni := ni) → Bool :=
  fun z a => src.B R activity a (Sum.inl z)

theorem reference_eq
    (src : SourceData (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
    (R : Fin nx → Fin ny → Bool)
    (activity : Fin ni → Fin q₂ → Option (Fin s)) (ξ₀ : SourceMatrix.Tail s (Fin ny)) :
    V39IndexedReferenceProfile.reference (toSources src) R activity ξ₀ =
      reference src R activity := by
  funext z a
  exact matrix_eq src R activity ξ₀ (Sum.inl z) a

#print axioms rowLaw_eq
#print axioms reference_eq

end CurrentAdditive.V39GeneratedReference
