import CurrentAdditive.SmallBiasPublicEndpoint

/-! The source's fixed gap uses the same executable list output. -/

namespace CurrentAdditive.SmallBias

open CurrentAdditive.FiniteFieldConstructor
open Paper2.Yao Paper2.YaoLookup Workspace.Types.Protocol

theorem public_printed_matrix_fixed_gap
    {V : Type} {E : Type*} [Fintype V]
    (g b : ℕ)
    (edges : E → Fin (2 ^ (v27GapParameter g) *
      2 ^ (v27GapParameter g)) ↪ V)
    (index : E ↪ Fin (2 ^ b)) :
    let t := v27GapParameter g
    ∃ output : List (ℕ × ℕ × List Bool), ∃ modulus : ℕ,
      TrialSearch.makeList (publicFieldDegree b t)
        (2 ^ b * (2 ^ t * 2 ^ t + 1)) = some output ∧
      TrialSearch.firstPassing (publicFieldDegree b t) = some modulus ∧
      output = StreamingPrinter.labelledWords (publicFieldDegree b t)
        modulus (2 ^ b * (2 ^ t * 2 ^ t + 1)) ∧
      (((2 ^ publicFieldDegree b t) ^ 2 : ℕ) : ℚ) <
        4 * ((2 ^ t * 2 ^ t + 1 : ℕ) : ℚ) ^ 2 *
          ((2 : ℚ) ^ (12 * 2 ^ t * t + 3 * t + 1)) ^ 2 *
          ((2 : ℚ) ^ b) ^ (8 * 2 ^ t + 4) ∧
      (let M := matrix (placeEdges edges index)
          (fullSelector (2 ^ (t - 1)) (2 ^ b))
          (printedPairFieldWord b t (publicFieldDegree b t) modulus)
       (∀ colour : V → Fin (2 ^ t),
          (∀ e c, 2 ^ t - 1 ≤
            colourFiberCard (fun i => colour (edges e i)) c) →
          Dalt .alice M ≤ 2 * b + 4 * t + 2) ∧
       ((∀ colour : V → Fin (2 ^ (2 ^ t - 1)),
          ∃ e c, ∀ i, colour (edges e i) = c) →
          (2 * b + 4 * t + 2) + g ≤ Dalt .alice M)) := by
  dsimp only
  let t := v27GapParameter g
  have ht : 4 ≤ t := v27GapParameter_ge_four g
  obtain ⟨output, modulus, hmake, hmod, heq, hyes, hno⟩ :=
    public_printed_matrix_yes_no b t ht edges index
  refine ⟨output, modulus, hmake, hmod, heq,
    public_degree_exact_list_bound b t ht, hyes, ?_⟩
  intro hn
  have hgap := v27GapParameter_gap g
  have hbound := hno hn
  change (2 * b + 4 * t + 2) + g ≤
    Dalt .alice (matrix (placeEdges edges index)
      (fullSelector (2 ^ (t - 1)) (2 ^ b))
      (printedPairFieldWord b t (publicFieldDegree b t) modulus))
  omega

#print axioms CurrentAdditive.SmallBias.public_printed_matrix_fixed_gap

end CurrentAdditive.SmallBias
