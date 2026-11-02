import CurrentAdditive.GeneratedDiagonalCapacity
import CurrentAdditive.ExactBoost

/-!
The complete indexed inner source supplies exact eight-wise marginals to
Appendix H `det:exact`. Its lower bound transfers to a literal retained
diagonal/template restriction of the generated final matrix.
-/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix Paper2.SourceProjection
open CurrentAdditive.ArbitraryPrefix

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

theorem inner_eightwise (hD : 8 ≤ D) :
    IsDWise 8 src.inner.law.toFiniteLaw src.inner.decode
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw := by
  intro C hC E
  exact src.inner.exactLaw C (hC.trans hD) E

/-- The original retained inner-label set, rather than a product of its
projected coordinate images, is the common column set of the exact boost.
The gamma supports remain in their own original indexed law. -/
theorem indexed_diagonal_exact_capacity
    (hD : 8 ≤ D) (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (p : Fin s) (K : Set src.inner.Label)
    (Good : Finset (Fin q₂)) (Rows : Fin q₂ → Set src.gamma.Label)
    (U : Set (Column src)) (V : Set (Row (I := I) src))
    (d a : ℕ) (x : ℝ)
    (ha : 1 ≤ a) (hd : 2 ≤ d) (hx : 0 < x)
    (hscale : (2 : ℝ)^a * x ≤ 1)
    (hprofile : RestrictionProfile (A src R)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
      x (d : ℤ))
    (hcount : 2^(a-1)+1 ≤ Good.card)
    (hrow : ∀ i ∈ Good, (2 : ℝ)^a*x ≤
      src.gamma.law.toFiniteLaw.prob (· ∈ Rows i))
    (hKmass : (9/25 : ℝ) ≤ src.inner.law.toFiniteLaw.prob (· ∈ K))
    (hK : ∀ z ∈ K, Sum.inl (p, z) ∈ V)
    (hS : ∀ α ∈ rowRectangle Good Rows,
      Column.diagonal (α.1, α.2) ∈ U) :
    d+a ≤ Paper2.Compression.restrictionD (N src R activity ξ₀) U V := by
  have hboost := CurrentAdditive.ArbitraryPrefix.exactboost
    src.gamma.law ((PositiveRationalLaw.uniform (Fin q₁)).prod μX)
    (A src R) src.inner.law.toFiniteLaw src.inner.decode
    (inner_eightwise src hD) Good Rows K d a x
    ha hd hx hscale hprofile hcount hrow hKmass
  have hmap := restrictionD_map_le (N src R activity ξ₀)
    (fun α : Fin q₂ × src.gamma.Label => Column.diagonal α)
    (fun z : src.inner.Label => Sum.inl (p, z))
    U V (rowRectangle Good Rows) K hS hK
  exact hboost.trans hmap

end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.inner_eightwise
#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.indexed_diagonal_exact_capacity
