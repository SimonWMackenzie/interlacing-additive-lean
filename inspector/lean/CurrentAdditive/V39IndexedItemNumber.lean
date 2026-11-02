import CurrentAdditive.EdgeIndexedLawProduction
import CurrentAdditive.V39GeneratedSourceBridge
import CurrentAdditive.GeneratedShadowMass

/-! The public finite item numbering preserves the exact graph item law,
the actual source row mixture, and each literal matrix entry. -/

namespace CurrentAdditive.V39IndexedItemNumber

open Paper2 CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicIndexedMatrix.Sources
open CurrentAdditive.V39GeneratedConstruction CurrentAdditive.V39GeneratedSourceBridge

private theorem law_eq_of_weights {A : Type*} [Fintype A]
    (μ ν : PositiveRationalLaw A) (h : μ.weight = ν.weight) : μ = ν := by
  cases μ
  cases ν
  cases h
  rfl

theorem itemLaw_eq (s n : ℕ) (hs : 4 ≤ s) (hn : 0 < n)
    [Nonempty (Fin (4*s))] [Nonempty (Fin n)] [Nonempty (Fin (s-3))] :
    DeterministicIndexedMatrix.itemLaw
      (G := Fin (4*s)) (V := Fin n) (A := Fin (s-3)) =
      LiteralEdgeEncoder.itemLaw s n hs hn := by
  apply law_eq_of_weights
  funext i
  rcases i with ⟨g,v|a⟩ <;>
    simp [DeterministicIndexedMatrix.itemLaw,halfSumLaw,
      PositiveRationalLaw.prod,PositiveRationalLaw.uniform,LiteralEdgeEncoder.itemLaw,
      div_eq_mul_inv,mul_inv_rev] <;> ring

variable {D q₁ q₂ s nx ny n : ℕ}
  [NeZero q₁] [NeZero q₂] [NeZero s]
  {μX : PositiveRationalLaw (Fin nx)} {μY : PositiveRationalLaw (Fin ny)}
  (src : SourceData (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

def rowNumber : Sources.Row (I := Paper2.SourceConstruction.Items s (Fin n)) (toSources src) ≃
    src.Row (ni := 4*s*(n+(s-3))) :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.prodCongr (LiteralEdgeEncoder.itemNumber s n) (Equiv.refl _))

theorem rowLaw_relabel (hs : 4 ≤ s) (hn : 0 < n)
    [Nonempty (Fin (4*s))] [Nonempty (Fin n)] [Nonempty (Fin (s-3))] :
    (Sources.rowLaw (toSources src)
      (DeterministicIndexedMatrix.itemLaw (G := Fin (4*s)) (V := Fin n) (A := Fin (s-3)))).relabel
        (rowNumber src) =
      src.rowLaw (μI := LiteralEdgeEncoder.indexedItemLaw s n hs hn) := by
  rw [itemLaw_eq s n hs hn]
  apply law_eq_of_weights
  funext a
  rcases a with pz | ⟨i,u⟩
  · change (255/256 : ℚ)*((Fintype.card (Fin s) : ℚ)⁻¹*src.inner.law.weight pz.2) =
      (255/256 : ℚ)*((s : ℚ)⁻¹*src.inner.law.weight pz.2)
    simp only [Fintype.card_fin]
  · rfl

theorem row_mass_eq (hs : 4 ≤ s) (hn : 0 < n)
    [Nonempty (Fin (4*s))] [Nonempty (Fin n)] [Nonempty (Fin (s-3))]
    (W : Set (src.Row (ni := 4*s*(n+(s-3))))) :
    (Sources.rowLaw (toSources src)
      (DeterministicIndexedMatrix.itemLaw (G := Fin (4*s)) (V := Fin n) (A := Fin (s-3)))).toFiniteLaw.prob
        (fun a => rowNumber src a ∈ W) =
      (src.rowLaw (μI := LiteralEdgeEncoder.indexedItemLaw s n hs hn)).toFiniteLaw.prob (· ∈ W) := by
  rw [← rowLaw_relabel src hs hn,PositiveRationalLaw.relabel_prob]

theorem matrix_rowNumber (R : Fin nx → Fin ny → Bool)
    (activity : Fin (4*s*(n+(s-3))) → Fin q₂ → Option (Fin s))
    (ξ₀ : SourceMatrix.Tail s (Fin ny))
    (c : src.Column) (a : Sources.Row (I := Paper2.SourceConstruction.Items s (Fin n)) (toSources src)) :
    V38IndexedTwoTag.matrix (toSources src) R
      (fun i α => activity (LiteralEdgeEncoder.itemNumber s n i) α) ξ₀ c a =
      src.B R activity (rowNumber src a) c := by
  cases c <;> cases a <;> rfl

end CurrentAdditive.V39IndexedItemNumber

#print axioms CurrentAdditive.V39IndexedItemNumber.itemLaw_eq
#print axioms CurrentAdditive.V39IndexedItemNumber.rowLaw_relabel
#print axioms CurrentAdditive.V39IndexedItemNumber.row_mass_eq
#print axioms CurrentAdditive.V39IndexedItemNumber.matrix_rowNumber
