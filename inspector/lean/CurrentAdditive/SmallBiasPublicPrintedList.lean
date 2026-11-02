import CurrentAdditive.SmallBiasPublicDegree
import CurrentAdditive.SmallBiasStreamingIndex

/-!
# The public printer output has the row-major indexed bits

Source: v27 Appendix G, `yao:finite-field-list`. The degree is computed
from public parameters, and the option-valued printer is total at that
degree. This theorem identifies its actual returned list cells.
-/

namespace CurrentAdditive.SmallBias

open CurrentAdditive.FiniteFieldConstructor

theorem public_makeList_output_eq (b t : ℕ)
    (output : List (ℕ × ℕ × List Bool))
    (houtput : TrialSearch.makeList (publicFieldDegree b t)
      (2 ^ b * (2 ^ t * 2 ^ t + 1)) = some output) :
    ∃ modulus,
      TrialSearch.firstPassing (publicFieldDegree b t) = some modulus ∧
      output = StreamingPrinter.labelledWords (publicFieldDegree b t)
        modulus (2 ^ b * (2 ^ t * 2 ^ t + 1)) := by
  unfold TrialSearch.makeList at houtput
  cases hmod : TrialSearch.firstPassing (publicFieldDegree b t) with
  | none => simp [hmod] at houtput
  | some modulus =>
      simp only [hmod, Option.map_some, Option.some.injEq] at houtput
      exact ⟨modulus, rfl, houtput.symm⟩

/-- Every returned cell keeps its own pair label and the corresponding
physical matrix bit at the selected payload position. -/
theorem public_makeList_indexed_bit (b t : ℕ)
    (output : List (ℕ × ℕ × List Bool))
    (houtput : TrialSearch.makeList (publicFieldDegree b t)
      (2 ^ b * (2 ^ t * 2 ^ t + 1)) = some output)
    (ℓ : Fin ((2 ^ publicFieldDegree b t) ^ 2))
    (j : Fin (2 ^ b) × Fin (2 ^ t * 2 ^ t + 1)) :
    ∃ modulus,
      TrialSearch.firstPassing (publicFieldDegree b t) = some modulus ∧
      let xy := (printerPairLabel (publicFieldDegree b t)).symm ℓ
      let k := (finProdFinEquiv j).val
      output[ℓ.val]? = some (xy.1.val, xy.2.val,
        StreamingPrinter.word (publicFieldDegree b t) modulus
          (2 ^ b * (2 ^ t * 2 ^ t + 1)) xy.1.val xy.2.val) ∧
      (StreamingPrinter.word (publicFieldDegree b t) modulus
        (2 ^ b * (2 ^ t * 2 ^ t + 1)) xy.1.val xy.2.val)[k]? =
        some (printedPairFieldWord b t (publicFieldDegree b t)
          modulus ℓ j) := by
  obtain ⟨modulus, hmod, rfl⟩ :=
    public_makeList_output_eq b t output houtput
  exact ⟨modulus, hmod,
    streaming_list_matches_printed_pair_array b t
      (publicFieldDegree b t) modulus ℓ j⟩

#print axioms CurrentAdditive.SmallBias.public_makeList_output_eq
#print axioms CurrentAdditive.SmallBias.public_makeList_indexed_bit

end CurrentAdditive.SmallBias
