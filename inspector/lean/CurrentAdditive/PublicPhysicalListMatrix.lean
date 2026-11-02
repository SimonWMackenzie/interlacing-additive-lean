import CurrentAdditive.PublicPrintedPairMatrix
import CurrentAdditive.SmallBiasPublicPrintedList

namespace CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge

open CurrentAdditive.SmallBias
open CurrentAdditive.FiniteFieldConstructor
open Paper2.Yao Paper2.YaoLookup Workspace.Types.Protocol

/-- The deterministic public constructor returns a concrete labelled list.
Each cell's physical word is the matrix word, and that matrix has the v27
NO-case communication gap. -/
theorem public_physical_list_no_matrix
    {V E : Type*} [Fintype V]
    (b t : ℕ) (ht : 4 ≤ t)
    (edges : E → Fin (2 ^ t * 2 ^ t) ↪ V)
    (index : E ↪ Fin (2 ^ b))
    (hno : ∀ colour : V → Fin (2 ^ (2 ^ t - 1)),
      ∃ e c, ∀ i, colour (edges e i) = c) :
    ∃ modulus output,
      TrialSearch.firstPassing (publicFieldDegree b t) = some modulus ∧
      TrialSearch.makeList (publicFieldDegree b t)
        (2 ^ b * (2 ^ t * 2 ^ t + 1)) = some output ∧
      output.length = (2 ^ publicFieldDegree b t) ^ 2 ∧
      (2 * b + 4 * t + 2) + 2 * t - 6 ≤
        Dalt .alice (matrix (placeEdges edges index)
          (fullSelector (2 ^ (t - 1)) (2 ^ b))
          (printedPairFieldWord b t (publicFieldDegree b t) modulus)) ∧
      ∀ (ℓ : Fin ((2 ^ publicFieldDegree b t) ^ 2))
        (j : Fin (2 ^ b) × Fin (2 ^ t * 2 ^ t + 1)),
        let xy := (printerPairLabel (publicFieldDegree b t)).symm ℓ
        let k := (finProdFinEquiv j).val
        output[ℓ.val]? = some (xy.1.val, xy.2.val,
          StreamingPrinter.word (publicFieldDegree b t) modulus
            (2 ^ b * (2 ^ t * 2 ^ t + 1)) xy.1.val xy.2.val) ∧
        (StreamingPrinter.word (publicFieldDegree b t) modulus
          (2 ^ b * (2 ^ t * 2 ^ t + 1)) xy.1.val xy.2.val)[k]? =
            some (printedPairFieldWord b t (publicFieldDegree b t)
              modulus ℓ j) := by
  obtain ⟨modulus, hfound, hgap⟩ :=
    public_firstPassing_printed_matrix b t ht edges index hno
  let output := StreamingPrinter.labelledWords (publicFieldDegree b t)
    modulus (2 ^ b * (2 ^ t * 2 ^ t + 1))
  have houtput : TrialSearch.makeList (publicFieldDegree b t)
      (2 ^ b * (2 ^ t * 2 ^ t + 1)) = some output := by
    simp [TrialSearch.makeList, hfound, output]
  refine ⟨modulus, output, hfound, houtput,
    TrialSearch.makeList_length houtput, hgap, ?_⟩
  intro ℓ j
  exact streaming_list_matches_printed_pair_array b t
    (publicFieldDegree b t) modulus ℓ j

#print axioms public_physical_list_no_matrix

end CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge
