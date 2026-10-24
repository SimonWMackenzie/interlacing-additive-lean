import CurrentAdditive.ConcretePrintedPairMatrix
import CurrentAdditive.SmallBiasPublicDegree

namespace CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge

open CurrentAdditive.SmallBias
open CurrentAdditive.FiniteFieldConstructor
open Paper2.Yao Paper2.YaoLookup Workspace.Types.Protocol

/-- The executable search at the public degree returns a modulus whose
literal printed pair array has the v27 NO-case matrix gap. -/
theorem public_firstPassing_printed_matrix
    {V E : Type*} [Fintype V]
    (b t : ℕ) (ht : 4 ≤ t)
    (edges : E → Fin (2 ^ t * 2 ^ t) ↪ V)
    (index : E ↪ Fin (2 ^ b))
    (hno : ∀ colour : V → Fin (2 ^ (2 ^ t - 1)),
      ∃ e c, ∀ i, colour (edges e i) = c) :
    ∃ modulus,
      TrialSearch.firstPassing (publicFieldDegree b t) = some modulus ∧
      (2 * b + 4 * t + 2) + 2 * t - 6 ≤
        Dalt .alice (matrix (placeEdges edges index)
          (fullSelector (2 ^ (t - 1)) (2 ^ b))
          (printedPairFieldWord b t (publicFieldDegree b t) modulus)) := by
  obtain ⟨modulus, hfound, hirr⟩ := public_firstPassing_correct b t
  obtain ⟨tail, htail, hcandidate⟩ := TrialSearch.firstPassing_is_candidate hfound
  have hlt : modulus < 2 ^ (publicFieldDegree b t + 1) := by
    rw [hcandidate]
    exact monicBits_lt _ tail htail
  have htop : modulus.testBit (publicFieldDegree b t) = true := by
    rw [hcandidate]
    exact monicBits_topBit _ tail htail
  have hmonic : (polynomial (publicFieldDegree b t + 1) modulus).Monic := by
    rw [hcandidate]
    exact monicBits_monic _ tail htail
  have hdegree :
      (polynomial (publicFieldDegree b t + 1) modulus).natDegree =
        publicFieldDegree b t := by
    rw [hcandidate]
    exact monicBits_degree _ tail htail
  letI : Fact (Irreducible
      (polynomial (publicFieldDegree b t + 1) modulus)) := ⟨hirr⟩
  refine ⟨modulus, hfound, ?_⟩
  exact lower_bound_concrete_printed_pair_matrix b t
    (publicFieldDegree b t) modulus ht (public_degree_pos b t)
    hlt htop hmonic hdegree (public_degree_source_bounds b t).1
    edges index hno

#print axioms public_firstPassing_printed_matrix

end CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge
