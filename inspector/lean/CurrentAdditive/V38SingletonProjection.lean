import CurrentAdditive.V38FirstMessage
import Paper2.SourceProjection

/-!
An actual projected base rectangle from a restricted full-product interlace.
The projected column event is measured under the original base law. A choice
of an actual retained tuple for each projected label transfers the protocol
cost, even when the retained tuples are correlated.
-/

namespace Paper2.V38SmallBlocks

open Workspace.Types.CommComplexity

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem singleton_projected_cost_le (F : X → Y → Bool) (p : ℕ)
    (U : Set (Fin p × X)) (V : Set (Fin p → Y)) (i : Fin p) :
    Compression.restrictionD F
      {x | (i, x) ∈ U} ((fun z : Fin p → Y => z i) '' V) ≤
      Compression.restrictionD (fullInterlace F p) U V := by
  apply SourceProjection.restrictionD_projected_le
    (fullInterlace F p) F (fun x : X => (i, x))
    (fun z : Fin p → Y => z i) U V {x | (i, x) ∈ U}
  · intro x hx
    exact hx
  · intro x hx z hz
    rfl

theorem singleton_profile_bound (F : X → Y → Bool)
    (μX : FiniteLaw X) (μY : FiniteLaw Y) (p : ℕ)
    (θ : ℝ) (H : ℤ)
    (hp : V38RestrictionProfiles.TwoThresholdProfile F μX μY θ H)
    (U : Set (Fin p × X)) (V : Set (Fin p → Y)) (i : Fin p)
    (hrow : θ ≤ μX.prob (fun x => (i, x) ∈ U))
    (j : Fin 2)
    (hcol : (3 / 5 : ℝ) * (1 / 2 : ℝ) ^ j.val ≤
      μY.prob (· ∈ (fun z : Fin p → Y => z i) '' V)) :
    H - (j.val : ℤ) ≤
      (Compression.restrictionD (fullInterlace F p) U V : ℤ) := by
  have hbase := hp j {x | (i, x) ∈ U}
    ((fun z : Fin p → Y => z i) '' V) hrow hcol
  exact hbase.trans (by exact_mod_cast singleton_projected_cost_le F p U V i)

#print axioms singleton_projected_cost_le
#print axioms singleton_profile_bound

end Paper2.V38SmallBlocks
