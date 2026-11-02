import EthInapproximability.CurrentPaper.MatrixWeightedOrdinalConjugacy

/-!
Explicit concrete interface for the literal physical protected word.

Source scope: current-paper v8 Section 5 prescribed numbering and Appendix B
row-major materialization; CP-EFFECTIVE weighted numbering continuation.
The admitted generic interface is MatrixWeightedOrdinalConjugacy. No same-index equality of the
physical copy-major raw-row order with Iteration's type-first order is used.
-/

namespace EthInapproximability.CurrentPaper.MatrixWeightedIterationConjugacy

open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open MatrixWeightedOrdinalConjugacy

noncomputable section

set_option maxHeartbeats 1000000

attribute [local irreducible] Iteration.nRowNumbering Iteration.nColNumbering
attribute [local irreducible] GraphVectors.vertexCount GraphVectors.auxiliaryCount

variable {VG EG : Type} [Fintype VG] [DecidableEq VG]
  [Fintype EG] [DecidableEq EG]
variable (G : EndpointGraph VG EG) (sourceConstant b y level : ℕ)
  (M : Iteration.Matrix)

/-- Every physical row-major cell is the actual Iteration protected entry at
the explicitly conjugated ordinals. No promise or conclusion-bearing premise
is supplied. The two permutations are the physical numbering followed by the
inverse Iteration numbering, with the source cardinality cast explicit in
`MatrixWeightedOrdinalConjugacy.ordinalPermutation`. -/
theorem literal_entry_conjugacy
    (x : Fin (Fintype.card (Iteration.NRow G sourceConstant b y level M)))
    (z : Fin (Fintype.card (Iteration.NCol G sourceConstant b y level M))) :
    (physicalProtectedWord G sourceConstant b y level M)[x.val *
      Fintype.card (Iteration.NCol G sourceConstant b y level M) + z.val]? =
    some (Iteration.protectedMatrix G sourceConstant b y level M
      ((Iteration.nRowNumbering G sourceConstant b y level M).equiv
        (rowPermutation G sourceConstant b y level M x))
      ((Iteration.nColNumbering G sourceConstant b y level M).equiv
        (columnPermutation G sourceConstant b y level M z))) := by
  unfold physicalProtectedWord rowPermutation columnPermutation
    physicalNRowNumbering physicalNColNumbering
  rw [← physicalProtectedMatrix_eq_iteration]
  unfold physicalProtectedMatrix
  have h := protectedWord_entry_conjugacy M.entry
    (Iteration.a G sourceConstant b y level M)
    (Iteration.s G sourceConstant b y level M)
    (Iteration.q₂ G sourceConstant b y level M)
    (Iteration.labels G sourceConstant b y level M)
    (GraphVectors.vertexCount VG (Iteration.s G sourceConstant b y level M))
    (GraphVectors.auxiliaryCount (Iteration.s G sourceConstant b y level M))
    (lt_of_lt_of_le (by decide : 0 < 4)
      (Iteration.bins_ge_four G sourceConstant b y level M))
    (Iteration.secondFamily G sourceConstant b y level M)
    (GraphVectors.itemOrder G (Iteration.s G sourceConstant b y level M))
    (GraphVectors.vectors G (Iteration.s G sourceConstant b y level M))
    (GraphVectors.supportCap G
      (le_trans (by decide : 3 ≤ 4)
        (Iteration.bins_ge_four G sourceConstant b y level M)))
    (Iteration.nRowNumbering G sourceConstant b y level M)
    (Iteration.nColNumbering G sourceConstant b y level M) x z
  dsimp only [physicalRowNumbering, physicalColumnNumbering] at h
  with_reducible exact h


end
end EthInapproximability.CurrentPaper.MatrixWeightedIterationConjugacy

