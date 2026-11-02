import EthInapproximability.CurrentPaper.MatrixWeightedIterationConjugacy

/-! Actual physical protected word read through the Iteration-numbered entry interface. -/

namespace EthInapproximability.CurrentPaper.MatrixWeightedNumberedWriter

open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open MatrixWeightedOrdinalConjugacy MatrixWeightedIterationConjugacy NPCC Workspace.Types.CommComplexity

noncomputable section

set_option maxHeartbeats 1000000
attribute [local irreducible] Iteration.nRowNumbering Iteration.nColNumbering
attribute [local irreducible] GraphVectors.vertexCount GraphVectors.auxiliaryCount

variable {VG EG : Type} [Fintype VG] [DecidableEq VG]
  [Fintype EG] [DecidableEq EG]
variable (G : EndpointGraph VG EG) (sourceConstant b y level : ℕ)
  (M : Iteration.Matrix)

/-- The literal writer word, read at a physical row-major address, is the
actual Iteration-numbered protected matrix at the corresponding permuted
ordinals. This does not identify the two ordinal orders. -/
theorem physical_word_numbered_entry
    (x : Fin (Fintype.card (Iteration.NRow G sourceConstant b y level M)))
    (z : Fin (Fintype.card (Iteration.NCol G sourceConstant b y level M))) :
    (physicalProtectedWord G sourceConstant b y level M)[x.val *
      Fintype.card (Iteration.NCol G sourceConstant b y level M) + z.val]? =
    some ((Iteration.number
      (Iteration.protectedMatrix G sourceConstant b y level M)
      (Iteration.nRowNumbering G sourceConstant b y level M)
      (Iteration.nColNumbering G sourceConstant b y level M)).entry
      (rowPermutation G sourceConstant b y level M x)
      (columnPermutation G sourceConstant b y level M z)) := by
  have h := literal_entry_conjugacy G sourceConstant b y level M x z
  simpa only [Iteration.number] using h

/-- Row-major word of the actual Iteration-numbered matrix, pulled back along
the two explicit ordinal permutations. -/
def permutedNumberedWord : List Bool :=
  MatrixMaterialization.rowMajor (fun x z =>
    (Iteration.number
      (Iteration.protectedMatrix G sourceConstant b y level M)
      (Iteration.nRowNumbering G sourceConstant b y level M)
      (Iteration.nColNumbering G sourceConstant b y level M)).entry
        (rowPermutation G sourceConstant b y level M x)
        (columnPermutation G sourceConstant b y level M z))

/-- The function serialized by `permutedNumberedWord`; this name prevents a
cost claim from being misread as a cost of a bit string. -/
def physicalNumberedEntry
    (x : Fin (Fintype.card (Iteration.NRow G sourceConstant b y level M)))
    (z : Fin (Fintype.card (Iteration.NCol G sourceConstant b y level M))) : Bool :=
  (Iteration.number
    (Iteration.protectedMatrix G sourceConstant b y level M)
    (Iteration.nRowNumbering G sourceConstant b y level M)
    (Iteration.nColNumbering G sourceConstant b y level M)).entry
      (rowPermutation G sourceConstant b y level M x)
      (columnPermutation G sourceConstant b y level M z)

/-- Communication cost is invariant under the two finite input relabelings.
This is a mathematical cost statement, not an algorithmic permutation bound. -/
theorem physical_numbered_entry_D :
    D (physicalNumberedEntry G sourceConstant b y level M) =
      D (Iteration.number
        (Iteration.protectedMatrix G sourceConstant b y level M)
        (Iteration.nRowNumbering G sourceConstant b y level M)
        (Iteration.nColNumbering G sourceConstant b y level M)).entry := by
  exact D_equiv_invariance _
    (rowPermutation G sourceConstant b y level M)
    (columnPermutation G sourceConstant b y level M)

theorem physical_word_length :
    (physicalProtectedWord G sourceConstant b y level M).length =
      Fintype.card (Iteration.NRow G sourceConstant b y level M) *
        Fintype.card (Iteration.NCol G sourceConstant b y level M) := by
  simp only [physicalProtectedWord, MatrixWeightedOrderWriter.protectedWord,
    MatrixMaterialization.rowMajor_length]

theorem physical_word_eq_permuted_numbered_word :
    physicalProtectedWord G sourceConstant b y level M =
      permutedNumberedWord G sourceConstant b y level M := by
  apply List.ext_getElem?
  intro k
  by_cases hk : k < Fintype.card (Iteration.NRow G sourceConstant b y level M) *
      Fintype.card (Iteration.NCol G sourceConstant b y level M)
  ·
    let p : Fin (Fintype.card (Iteration.NRow G sourceConstant b y level M) *
      Fintype.card (Iteration.NCol G sourceConstant b y level M)) := ⟨k, hk⟩
    let x := (finProdFinEquiv.symm p).1
    let z := (finProdFinEquiv.symm p).2
    have hindex : k = x.val *
        Fintype.card (Iteration.NCol G sourceConstant b y level M) + z.val := by
      have hp : finProdFinEquiv (x,z) = p := by
        change finProdFinEquiv (finProdFinEquiv.symm p) = p
        exact Equiv.apply_symm_apply _ _
      calc
        k = (finProdFinEquiv (x,z)).val := by simpa [p] using congrArg Fin.val hp.symm
        _ = z.val + Fintype.card (Iteration.NCol G sourceConstant b y level M) *
            x.val := finProdFinEquiv_apply_val (x,z)
        _ = x.val * Fintype.card (Iteration.NCol G sourceConstant b y level M) +
            z.val := by ring
    rw [hindex]
    rw [physical_word_numbered_entry]
    simpa only [permutedNumberedWord] using
      (MatrixMaterialization.rowMajor_entry
        (fun x z =>
          (Iteration.number
            (Iteration.protectedMatrix G sourceConstant b y level M)
            (Iteration.nRowNumbering G sourceConstant b y level M)
            (Iteration.nColNumbering G sourceConstant b y level M)).entry
              (rowPermutation G sourceConstant b y level M x)
              (columnPermutation G sourceConstant b y level M z)) x z).symm
  · have hl := physical_word_length G sourceConstant b y level M
    have hr : (permutedNumberedWord G sourceConstant b y level M).length =
        Fintype.card (Iteration.NRow G sourceConstant b y level M) *
          Fintype.card (Iteration.NCol G sourceConstant b y level M) := by
      simp [permutedNumberedWord]
    rw [List.getElem?_eq_none (by rw [hl]; omega),
      List.getElem?_eq_none (by rw [hr]; omega)]


end
end EthInapproximability.CurrentPaper.MatrixWeightedNumberedWriter

