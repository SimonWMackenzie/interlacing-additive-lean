import CurrentAdditive.SmallBiasBoundedCost
import Paper2.YaoLowerBound

/-!
# Feeding the v27 explicit-array property into the actual matrix lift

Source: v27 `sections/07-yao.tex`, `yao:lift`. The small-bias law supplies
the forbidden lookup restriction; the checked Paper2 lift performs the
dominant-strategy colouring, projection, and actual row/column restriction.
-/

namespace CurrentAdditive.SmallBias

open Paper2.Yao Paper2.YaoLookup Workspace.Types.Protocol

variable {V E : Type*} [Fintype V] {b t m n : ℕ}

/-- The real matrix lower bound, conditional on the selector projection
property. The payload premise is only small bias of the actual labelled
array list; no communication lower bound is supplied as a certificate. -/
theorem lower_bound_of_small_biased_payload
    (ht : 4 ≤ t) (hm : 0 < m)
    (edges : E → Fin (2 ^ t * 2 ^ t) ↪ V)
    (index : E ↪ Fin (2 ^ b))
    (hno : ∀ colour : V → Fin (2 ^ (2 ^ t - 1)),
      ∃ e c, ∀ i, colour (edges e i) = c)
    (C : Fin m → Fin (2 ^ (t - 1)) → Fin (2 ^ b))
    (hC : selectorGood (2 ^ (t - 1)) (2 ^ b) (2 ^ (2 ^ t - 1)) m C)
    (W : Fin n → Fin (2 ^ b) × Fin (2 ^ t * 2 ^ t + 1) → Bool)
    (μ : Paper2.FiniteLaw (Fin n))
    (hμ : IsSmallBiased μ W
      ((1 / 2 : ℝ) ^
        (2 ^ sourceSuffixDepth b t + t + sourceCutIndex b t + 2))) :
    (2 * b + 4 * t + 2) + 2 * t - 6 ≤
      Dalt .alice (matrix (placeEdges edges index) C W) := by
  exact Paper2.YaoLowerBound.lower_bound_of_good_events t b ht hm edges index
    hno C hC W (no_payloadShortProtocolFailure_of_small_bias b t n ht μ W hμ)

#print axioms CurrentAdditive.SmallBias.lower_bound_of_small_biased_payload

end CurrentAdditive.SmallBias
