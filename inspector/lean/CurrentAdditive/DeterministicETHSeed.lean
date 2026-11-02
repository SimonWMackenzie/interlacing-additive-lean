import Paper2.SeedTableFinal
import CurrentAdditive.DeterministicParameters

/-! The actual Boolean-cube indexing seed at the deterministic public
dyadic parameter. Its finite cost/profile and the physical indexed table
printer are inherited from separately checked seed modules. -/

namespace CurrentAdditive.DeterministicETHSeed

set_option maxHeartbeats 1000000

open EthInapproximability.CurrentPaper
open CurrentAdditive.DeterministicParameters
open Paper2.LookupSeed
open SeedT45.SeedTable
open Workspace.Types.CommComplexity

def indexedSeed (L : ℕ) :
    Fin (2 ^ width L) → Fin (width L) → Bool := seedTable (width L)

theorem indexedSeed_entry (L : ℕ) (i : Fin (2 ^ width L))
    (j : Fin (width L)) :
    indexedSeed L i j = matrix (width L) (seedRow (width L) i) j := rfl

/-- The row indices are a bijective enumeration of the original Boolean
cube, hence the indexed seed has exactly its established communication cost. -/
theorem indexedSeed_cost (L : ℕ) :
    D (indexedSeed L) = exponent L + 1 := by
  let e : Fin (2 ^ width L) ≃ (Fin (width L) → Bool) :=
    Equiv.ofBijective (seedRow (width L)) (seedRow_bijective (width L))
  have h := NPCC.D_equiv_invariance (matrix (width L))
    e (Equiv.refl (Fin (width L)))
  have hseed : D (indexedSeed L) = D (matrix (width L)) := by
    simpa only [indexedSeed, seedTable, e, Equiv.ofBijective_apply,
      Equiv.refl_apply] using h
  exact hseed.trans (selected_seed_finite L).1

#print axioms indexedSeed_entry
#print axioms indexedSeed_cost

end CurrentAdditive.DeterministicETHSeed
