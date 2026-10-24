import CurrentAdditive.IndexedIncomingImageFixed

/-! Only the unconditional arithmetic of the two actual protected tagged
column populations, with no owner-node or retained-tuple hypothesis. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2

variable {X Y : Type*} [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

omit [NeZero s] in
/-- More than `2μδ` protected receipt, with `μ=1/256`, forces one of the
two original tagged column populations to retain conditional mass δ. -/
theorem protected_receipt_type_dichotomy
    (w : ℕ) (Vrows : Set (Fin w × Column src)) (j : Fin w)
    (δ : ℝ)
    (hreceipt : 2 * (1/256 : ℝ) * δ <
      protectedReceipt src w Vrows j) :
    δ ≤ src.outer.law.toFiniteLaw.prob
      (fun f => (j, .fixedTail f) ∈ Vrows) ∨
    δ ≤ (diagonalLaw src).toFiniteLaw.prob
      (fun f => (j, .diagonal f) ∈ Vrows) := by
  by_cases hfixed : δ ≤ src.outer.law.toFiniteLaw.prob
      (fun f => (j, .fixedTail f) ∈ Vrows)
  · exact Or.inl hfixed
  · right
    have hfixed' : src.outer.law.toFiniteLaw.prob
        (fun f => (j, .fixedTail f) ∈ Vrows) < δ := lt_of_not_ge hfixed
    dsimp [protectedReceipt] at hreceipt
    norm_num at hreceipt ⊢
    linarith

omit [NeZero s] in
/-- The total protected receipt of one physical origin is at most
`2μ`, because each original tagged population has mass at most one. -/
theorem protected_receipt_le_two_mu
    (w : ℕ) (Vrows : Set (Fin w × Column src)) (j : Fin w) :
    protectedReceipt src w Vrows j ≤ 2 * (1/256 : ℝ) := by
  have hf := src.outer.law.toFiniteLaw.prob_le_one
    (fun f => (j, Column.fixedTail f) ∈ Vrows)
  have hd := (diagonalLaw src).toFiniteLaw.prob_le_one
    (fun f => (j, Column.diagonal f) ∈ Vrows)
  dsimp [protectedReceipt]
  nlinarith

#print axioms protected_receipt_type_dichotomy
#print axioms protected_receipt_le_two_mu

end CurrentAdditive.DeterministicIndexedMatrix.Sources
