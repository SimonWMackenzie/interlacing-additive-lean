import CurrentAdditive.SmallBiasPrintedEndpoint

/-!
# Semantic midpoint classification for the deterministic finite gap

Source: v27 Section 7 `yao:main` and `yao:bpp`. These are threshold
calculations on an explicit finite matrix, relative to an additive-error
estimate. They do not claim an estimator machine, source reduction, or
printer runtime.
-/

namespace CurrentAdditive.SmallBias

open Paper2.Yao Paper2.YaoLookup Workspace.Types.Protocol
open CurrentAdditive.FiniteFieldAdapter
open CurrentAdditive.FiniteFieldConstructor

/-- An additive-error estimate of an integer quantity distinguishes a
YES bound `B` from an NO bound `B+gap` whenever `gap>2u`. -/
theorem midpoint_separates (cost : ℕ) (estimate B gap u : ℝ)
    (hgap : 2 * u < gap)
    (herror : |estimate - (cost : ℝ)| ≤ u) :
    ((cost : ℝ) ≤ B → estimate < B + gap / 2) ∧
    (B + gap ≤ (cost : ℝ) → B + gap / 2 < estimate) := by
  obtain ⟨hl, hr⟩ := abs_le.mp herror
  constructor <;> intro hcost <;> linarith

/-- The source's four conventions fit one semantic classifier with
offsets 0, 1, 2, 0 from the Alice-start public-output gap. The second
zero is Bob-start on the transposed matrix. -/
def v27ConventionLoss : Fin 4 → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 0

/-- The exact printed-pair matrix has a midpoint test for any of the four
measure values once its corresponding YES/NO inequalities are provided.
This leaves the estimator's physical polynomial-time property explicit. -/
theorem midpoint_separates_v27 (B t cost : ℕ) (estimate u : ℝ)
    (hloss : ℕ) (hgap : 2 * u < (2 * t - 6 - hloss : ℕ))
    (herror : |estimate - (cost : ℝ)| ≤ u) :
    (cost ≤ B → estimate < (B : ℝ) + (2 * t - 6 - hloss : ℕ) / 2) ∧
    (B + (2 * t - 6 - hloss) ≤ cost →
      (B : ℝ) + (2 * t - 6 - hloss : ℕ) / 2 < estimate) := by
  have h := midpoint_separates cost estimate (B : ℝ)
    (2 * t - 6 - hloss : ℕ) u hgap herror
  constructor
  · intro hc
    exact h.1 (by exact_mod_cast hc)
  · intro hc
    apply h.2
    exact_mod_cast hc

/-- The midpoint test for the actual printed-pair matrix. The single
residual algebraic premise is equality of physical printer bits with the
quotient-field words; the estimator supplies only its stated error bound. -/
theorem printed_pair_midpoint_classifier
    {F E : Type*} {V : Type} [Fintype V]
    [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
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
    (estimate u : ℝ) (hgap : 2 * u < (2 * t - 6 : ℕ))
    (herror : |estimate -
        (Dalt .alice (matrix (placeEdges edges index)
          (fullSelector (2 ^ (t - 1)) (2 ^ b))
          (printedPairFieldWord b t d modulus)) : ℝ)| ≤ u) :
    (∀ colour : V → Fin (2 ^ t),
      (∀ e c, 2 ^ t - 1 ≤
        colourFiberCard (fun i => colour (edges e i)) c) →
      estimate < (2 * b + 4 * t + 2 : ℕ) + (2 * t - 6 : ℕ) / 2) ∧
    ((∀ colour : V → Fin (2 ^ (2 ^ t - 1)),
        ∃ e c, ∀ i, colour (edges e i) = c) →
      (2 * b + 4 * t + 2 : ℕ) + (2 * t - 6 : ℕ) / 2 < estimate) := by
  let M := matrix (placeEdges edges index)
    (fullSelector (2 ^ (t - 1)) (2 ^ b))
    (printedPairFieldWord b t d modulus)
  have hs := midpoint_separates_v27 (2 * b + 4 * t + 2) t
    (Dalt .alice M) estimate u 0 (by simpa using hgap) herror
  constructor
  · intro colour hbalanced
    apply hs.1
    exact balanced_yes_printed_pair_field_matrix b t d modulus ht
      edges index colour hbalanced
  · intro hno
    apply hs.2
    have hN := lower_bound_printed_pair_field_matrix b t d modulus
      ht basis hcard xDecode yDecode hR hbit edges index hno
    change (2 * b + 4 * t + 2) + 2 * t - 6 ≤ Dalt .alice M at hN
    omega

#print axioms CurrentAdditive.SmallBias.midpoint_separates
#print axioms CurrentAdditive.SmallBias.midpoint_separates_v27
#print axioms CurrentAdditive.SmallBias.printed_pair_midpoint_classifier

end CurrentAdditive.SmallBias
