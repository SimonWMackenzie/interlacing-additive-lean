import Paper2.AEndpoint

/-!
# D-A1: the map's recommended option is satisfied by the actual reduction law

Lane `owner:a-endpoint-1` (private, 26 September 2026). This does NOT choose D-A1. It shows that
IF the author selects the unit-4 map's recommendation (the uniform law on the words of one exact
length, `AEndpoint.uniformExact`), then the hypothesis `AEndpoint.DA1 D B uniformExact` of
`T01_endpoint` holds: every experiment law of every T10 graph is the uniform law on exact-length
bit lists (scheduled branch: `RecursiveSamplingTape.serializedTapeLaw` on
`{bits // bits.length = bitCount}`; fallback branch: the point mass on the empty word).
No ledger row is closed.
-/

set_option maxHeartbeats 4000000

namespace Paper2.AEndpoint

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2 Paper2.Unit4Shell.T10Finite

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

/-- The recommended D-A1 option holds for the actual reduction law (no choice is made). -/
theorem DA1_uniformExact : DA1 D B uniformExact := by
  intro Φ k _
  by_cases hc : CompletePublicScheduleScratch.Checks
      (V := Fin (t10Graph D B Φ).vertices) (E := Fin (t10Graph D B Φ).edges.length)
      (Nat.clog 2 (t10Graph D B Φ).vertices) B.degreeBound (sourceGap D B)
  · rw [TotalFiniteConstructorScratch.experiment_good _ _ _ _ _ hc]
    unfold uniformExact
    exact ⟨_, fun t => t.property, Subtype.val_injective, fun w hw => ⟨⟨w, hw⟩, rfl⟩,
      fun _ => rfl⟩
  · rw [TotalFiniteConstructorScratch.experiment_bad _ _ _ _ _ hc]
    unfold uniformExact
    refine ⟨0, fun _ => rfl, fun _ _ _ => rfl, fun w hw => ⟨(), ?_⟩, fun _ => ?_⟩
    · exact (List.eq_nil_of_length_eq_zero hw).symm
    · show (1 : ℝ) = (1 / 2 : ℝ) ^ 0
      simp

end Paper2.AEndpoint

#print axioms Paper2.AEndpoint.DA1_uniformExact
