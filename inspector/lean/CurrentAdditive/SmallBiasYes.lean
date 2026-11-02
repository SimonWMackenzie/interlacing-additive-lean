import CurrentAdditive.SmallBiasExactListCount
import CurrentAdditive.SmallBiasGenericFieldMatrix

/-!
# The balanced-colouring YES protocol for the v27 field matrix

Source: `sections/07-yao.tex`, `yao:budget` and `yao:lift`. The inherited
Paper2 protocol sends colour, edge address, selected address, within-colour
slot, and answer in strict alternation. This file applies that actual
protocol to the full selector list and labelled field arrays.
-/

namespace CurrentAdditive.SmallBias

open Paper2.Yao Paper2.YaoLookup Workspace.Types.Protocol

/-- A balanced source colouring gives the literal YES budget for the
mathematical indexed field matrix, for any positive field dimension. -/
theorem balanced_yes_indexed_field_matrix
    {V E : Type*} [Fintype V]
    (b t d : ℕ) (ht : 4 ≤ t) (hd : 0 < d)
    (edges : E → Fin (2 ^ t * 2 ^ t) ↪ V)
    (index : E ↪ Fin (2 ^ b))
    (colour : V → Fin (2 ^ t))
    (hbalanced : ∀ e c, 2 ^ t - 1 ≤
      colourFiberCard (fun i => colour (edges e i)) c) :
    Dalt .alice (matrix (placeEdges edges index)
      (fullSelector (2 ^ (t - 1)) (2 ^ b))
      (indexedFieldWord b t d hd (binaryBasis d hd))) ≤
      2 * b + 4 * t + 2 := by
  exact placed_balanced_budget t b (by omega) edges index colour hbalanced
    (fullSelector (2 ^ (t - 1)) (2 ^ b))
    (indexedFieldWord b t d hd (binaryBasis d hd))

/-- The same YES protocol works for the executable constructor's eventual
binary quotient field, provided its basis and exact order are supplied. -/
theorem balanced_yes_generic_field_matrix
    {V E F : Type*} [Fintype V] [Field F] [Fintype F]
    [CharP F 2] [Algebra (ZMod 2) F]
    (b t d : ℕ) (ht : 4 ≤ t)
    (basis : Module.Basis (Fin d) (ZMod 2) F)
    (hcard : Fintype.card F = 2 ^ d)
    (edges : E → Fin (2 ^ t * 2 ^ t) ↪ V)
    (index : E ↪ Fin (2 ^ b))
    (colour : V → Fin (2 ^ t))
    (hbalanced : ∀ e c, 2 ^ t - 1 ≤
      colourFiberCard (fun i => colour (edges e i)) c) :
    Dalt .alice (matrix (placeEdges edges index)
      (fullSelector (2 ^ (t - 1)) (2 ^ b))
      (genericIndexedFieldWord b t d basis hcard)) ≤
      2 * b + 4 * t + 2 := by
  exact placed_balanced_budget t b (by omega) edges index colour hbalanced
    (fullSelector (2 ^ (t - 1)) (2 ^ b))
    (genericIndexedFieldWord b t d basis hcard)

/-- A single finite matrix has the exact source NO gap and, whenever a
balanced colouring is provided, the YES protocol. The list-size constant
matches the displayed v27 Appendix G coefficient. -/
theorem exists_indexed_field_matrix_gap_and_yes
    {V E : Type*} [Fintype V]
    (b t : ℕ) (ht : 4 ≤ t)
    (edges : E → Fin (2 ^ t * 2 ^ t) ↪ V)
    (index : E ↪ Fin (2 ^ b))
    (hno : ∀ colour : V → Fin (2 ^ (2 ^ t - 1)),
      ∃ e c, ∀ i, colour (edges e i) = c) :
    ∃ d : ℕ, ∃ hd : 0 < d,
      (((2 ^ d) ^ 2 : ℕ) : ℚ) <
        4 * ((2 ^ t * 2 ^ t + 1 : ℕ) : ℚ) ^ 2 *
          ((2 : ℚ) ^ (12 * 2 ^ t * t + 3 * t + 1)) ^ 2 *
          ((2 : ℚ) ^ b) ^ (8 * 2 ^ t + 4) ∧
      (∀ colour : V → Fin (2 ^ t),
        (∀ e c, 2 ^ t - 1 ≤
          colourFiberCard (fun i => colour (edges e i)) c) →
        Dalt .alice (matrix (placeEdges edges index)
          (fullSelector (2 ^ (t - 1)) (2 ^ b))
          (indexedFieldWord b t d hd (binaryBasis d hd))) ≤
          2 * b + 4 * t + 2) ∧
      (2 * b + 4 * t + 2) + 2 * t - 6 ≤
        Dalt .alice (matrix (placeEdges edges index)
          (fullSelector (2 ^ (t - 1)) (2 ^ b))
          (indexedFieldWord b t d hd (binaryBasis d hd))) := by
  obtain ⟨d, hd, hsize, hgap⟩ :=
    exists_exact_polynomial_size_field_matrix_gap b t ht edges index hno
  refine ⟨d, hd, hsize, ?_, hgap⟩
  intro colour hbalanced
  exact balanced_yes_indexed_field_matrix b t d ht hd
    edges index colour hbalanced

#print axioms CurrentAdditive.SmallBias.balanced_yes_indexed_field_matrix
#print axioms CurrentAdditive.SmallBias.balanced_yes_generic_field_matrix
#print axioms CurrentAdditive.SmallBias.exists_indexed_field_matrix_gap_and_yes

end CurrentAdditive.SmallBias
