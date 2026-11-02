import CurrentAdditive.SmallBiasPublicPrintedList
import CurrentAdditive.SmallBiasConventionYes
import CurrentAdditive.PublicPrintedPairMatrix

/-!
# A single actual printer output for the source YES and NO implications

Source: v27 Section 7 `yao:lift`, and Appendix G
`yao:finite-field-list`. The printer result depends only on public `b,t`.
The finite matrix has the source budgets under the corresponding graph
promises. Physical running time is a separate obligation.
-/

namespace CurrentAdditive.SmallBias

open CurrentAdditive.FiniteFieldConstructor
open CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge
open Paper2.Yao Paper2.YaoLookup Workspace.Types.Protocol

theorem public_printed_matrix_yes_no
    {V : Type} {E : Type*} [Fintype V]
    (b t : ℕ) (ht : 4 ≤ t)
    (edges : E → Fin (2 ^ t * 2 ^ t) ↪ V)
    (index : E ↪ Fin (2 ^ b)) :
    ∃ output : List (ℕ × ℕ × List Bool), ∃ modulus : ℕ,
      TrialSearch.makeList (publicFieldDegree b t)
        (2 ^ b * (2 ^ t * 2 ^ t + 1)) = some output ∧
      TrialSearch.firstPassing (publicFieldDegree b t) = some modulus ∧
      output = StreamingPrinter.labelledWords (publicFieldDegree b t)
        modulus (2 ^ b * (2 ^ t * 2 ^ t + 1)) ∧
      (let M := matrix (placeEdges edges index)
          (fullSelector (2 ^ (t - 1)) (2 ^ b))
          (printedPairFieldWord b t (publicFieldDegree b t) modulus)
       (∀ colour : V → Fin (2 ^ t),
          (∀ e c, 2 ^ t - 1 ≤
            colourFiberCard (fun i => colour (edges e i)) c) →
          Dalt .alice M ≤ 2 * b + 4 * t + 2) ∧
       ((∀ colour : V → Fin (2 ^ (2 ^ t - 1)),
          ∃ e c, ∀ i, colour (edges e i) = c) →
          (2 * b + 4 * t + 2) + 2 * t - 6 ≤ Dalt .alice M)) := by
  obtain ⟨output, houtput⟩ := public_makeList_total b t
  obtain ⟨modulus, hmod, heq⟩ :=
    public_makeList_output_eq b t output houtput
  refine ⟨output, modulus, houtput, hmod, heq, ?_⟩
  dsimp
  constructor
  · intro colour hbalanced
    exact balanced_yes_printed_pair_field_matrix (V := V) (E := E) b t
      (publicFieldDegree b t) modulus ht edges index colour hbalanced
  · intro hno
    obtain ⟨modulus', hmod', hgap⟩ :=
      public_firstPassing_printed_matrix b t ht edges index hno
    have hm : modulus' = modulus :=
      Option.some.inj (hmod'.symm.trans hmod)
    subst modulus'
    exact hgap

#print axioms CurrentAdditive.SmallBias.public_printed_matrix_yes_no

end CurrentAdditive.SmallBias
