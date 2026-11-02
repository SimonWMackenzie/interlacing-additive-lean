import CurrentAdditive.SmallBiasPrintedPairBridge
import CurrentAdditive.SmallBiasGapParameter
import Paper2.YaoTranspose

/-!
# Same printed matrix: YES, NO, convention variants, dimensions

Source: v27 Section 7 `yao:budget`, `yao:lift`, `yao:comparison`,
`yao:bpp`, and Appendix G `yao:deterministic-table-size`.
The bit-semantic premise is exactly the quotient printer's missing
pointwise equality, not a small-bias or communication conclusion.
-/

namespace CurrentAdditive.SmallBias

open Paper2.Yao Paper2.YaoLookup Workspace.Types.Protocol
open CurrentAdditive.FiniteFieldAdapter
open CurrentAdditive.FiniteFieldConstructor

variable {F E : Type*} {V : Type} [Fintype V] [Field F] [Fintype F]
  [CharP F 2] [Algebra (ZMod 2) F]

/-- The inherited actual protocol gives the YES budget for the very same
row-major executable-bit array used by the NO theorem. -/
theorem balanced_yes_printed_pair_field_matrix
    (b t d modulus : ℕ) (ht : 4 ≤ t)
    (edges : E → Fin (2 ^ t * 2 ^ t) ↪ V)
    (index : E ↪ Fin (2 ^ b))
    (colour : V → Fin (2 ^ t))
    (hbalanced : ∀ e c, 2 ^ t - 1 ≤
      colourFiberCard (fun i => colour (edges e i)) c) :
    Dalt .alice (matrix (placeEdges edges index)
      (fullSelector (2 ^ (t - 1)) (2 ^ b))
      (printedPairFieldWord b t d modulus)) ≤
      2 * b + 4 * t + 2 := by
  exact placed_balanced_budget t b (by omega) edges index colour hbalanced
    (fullSelector (2 ^ (t - 1)) (2 ^ b))
    (printedPairFieldWord b t d modulus)

/-- The exact finite output dimensions before any bit-level running-time
claim: `|rows|=|V|H^q` and `|columns|=qHR²`. -/
theorem printed_pair_matrix_dimensions (b t d : ℕ) :
    Fintype.card (V × Fin (Fintype.card
      (Fin (2 ^ (t - 1)) → Fin (2 ^ b)))) =
        Fintype.card V * (2 ^ b) ^ (2 ^ (t - 1)) ∧
    Fintype.card (Fin (2 ^ (t - 1)) × Fin (2 ^ b) ×
      Fin ((2 ^ d) ^ 2)) =
        2 ^ (t - 1) * 2 ^ b * (2 ^ d) ^ 2 := by
  constructor <;> simp [Fintype.card_prod, Nat.mul_assoc]

/-- Public-output Alice-start, free-starter public output, and free-starter
receiver output differ by at most the one and two bits proved in Paper2.
Bob-start has the identical complexity after transposing the matrix. -/
theorem printed_pair_convention_bounds
    (b t d modulus : ℕ)
    (edges : E → Fin (2 ^ t * 2 ^ t) ↪ V)
    (index : E ↪ Fin (2 ^ b)) :
    let M := matrix (placeEdges edges index)
      (fullSelector (2 ^ (t - 1)) (2 ^ b))
      (printedPairFieldWord b t d modulus)
    Dfree M ≤ Dalt .alice M ∧
    Dalt .alice M ≤ Dfree M + 1 ∧
    Yfree M ≤ Dalt .alice M ∧
    Dalt .alice M ≤ Yfree M + 2 ∧
    Dalt .bob (fun y x => M x y) = Dalt .alice M := by
  dsimp
  let M := matrix (placeEdges edges index)
    (fullSelector (2 ^ (t - 1)) (2 ^ b))
    (printedPairFieldWord b t d modulus)
  have hf := free_starter_comparison M
  have hr := receiver_comparison M
  have ht := Dalt_transpose .alice M
  exact ⟨hf.1, hf.2, hr.1, hr.2, by simpa using ht⟩

/-- From the NO bound for printed bits, the other output conventions keep
the source's exact losses: one bit for free starter, two for receiver output.
The transpose gives the Bob-start bound without loss. -/
theorem lower_bounds_printed_pair_conventions
    (b t d modulus : ℕ) (ht : 4 ≤ t)
    (basis : Module.Basis (Fin d) (ZMod 2) F)
    (hcard : Fintype.card F = 2 ^ d)
    (xDecode : Fin (2 ^ d) ≃ (Fin d → ZMod 2))
    (yDecode : Fin (2 ^ d) ≃ F)
    (hR : ((2 ^ b * (2 ^ t * 2 ^ t + 1) : ℕ) : ℚ) / sourceBiasQ b t ≤
      (2 ^ d : ℚ))
    (hbit : ∀ x y j,
      BitPrinter.bit d modulus (x : Fin (2 ^ d)).val
          (y : Fin (2 ^ d)).val (j : Fin (2 ^ b * (2 ^ t * 2 ^ t + 1))).val =
        vectorWord basis (xDecode x, yDecode y) j)
    (edges : E → Fin (2 ^ t * 2 ^ t) ↪ V)
    (index : E ↪ Fin (2 ^ b))
    (hno : ∀ colour : V → Fin (2 ^ (2 ^ t - 1)),
      ∃ e c, ∀ i, colour (edges e i) = c) :
    let M := matrix (placeEdges edges index)
      (fullSelector (2 ^ (t - 1)) (2 ^ b))
      (printedPairFieldWord b t d modulus)
    (2 * b + 4 * t + 2) + 2 * t - 6 ≤ Dalt .alice M ∧
    (2 * b + 4 * t + 2) + 2 * t - 7 ≤ Dfree M ∧
    (2 * b + 4 * t + 2) + 2 * t - 8 ≤ Yfree M ∧
    (2 * b + 4 * t + 2) + 2 * t - 6 ≤
      Dalt .bob (fun y x => M x y) := by
  dsimp
  let M := matrix (placeEdges edges index)
    (fullSelector (2 ^ (t - 1)) (2 ^ b))
    (printedPairFieldWord b t d modulus)
  have hA : (2 * b + 4 * t + 2) + 2 * t - 6 ≤ Dalt .alice M :=
    lower_bound_printed_pair_field_matrix b t d modulus ht basis hcard
      xDecode yDecode hR hbit edges index hno
  obtain ⟨_, hf, _, hr, htrans⟩ :=
    printed_pair_convention_bounds b t d modulus edges index
  change Dalt .alice M ≤ Dfree M + 1 at hf
  change Dalt .alice M ≤ Yfree M + 2 at hr
  change Dalt .bob (fun y x => M x y) = Dalt .alice M at htrans
  constructor
  · exact hA
  constructor
  · change (2 * b + 4 * t + 2) + 2 * t - 7 ≤ Dfree M
    omega
  constructor
  · change (2 * b + 4 * t + 2) + 2 * t - 8 ≤ Yfree M
    omega
  · rw [htrans]
    exact hA

#print axioms CurrentAdditive.SmallBias.balanced_yes_printed_pair_field_matrix
#print axioms CurrentAdditive.SmallBias.printed_pair_matrix_dimensions
#print axioms CurrentAdditive.SmallBias.lower_bounds_printed_pair_conventions

end CurrentAdditive.SmallBias
