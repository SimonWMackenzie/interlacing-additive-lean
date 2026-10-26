import CurrentAdditive.IndexedLawBytesSource
import CurrentAdditive.V39ExecutableGenerated

/-! The same physical writer extracts the actual executable Code D law.
The weight equality is discharged here, never passed to the caller. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
namespace CurrentAdditive.IndexedLawBytes
open EthInapproximability.CurrentPaper
open V39GeneratedConstruction

theorem actual_uniform : ∃ C E : Nat,∀ (D q n : Nat) (μ : Paper2.PositiveRationalLaw (Fin n)),
    machine.OutputsWithin
      (CodeDCanonicalSourceV2.encodedSource (IndexedLaw.construct D μ.weight q))
      (StoredWeightedState.lawBytes (((executableCodeD D).run q n μ).law))
      (C*((CodeDCanonicalSourceV2.encodedSource (IndexedLaw.construct D μ.weight q)).length+1)^E) := by
  obtain ⟨C,E,h⟩ := law_uniform
  refine ⟨C,E,?_⟩
  intro D q n μ
  exact h q (IndexedLaw.construct D μ.weight q) (((executableCodeD D).run q n μ).law)
    (fun j => executable_weight D q n μ j)

theorem actual8192_uniform : ∃ C E : Nat,∀ (q n : Nat) (μ : Paper2.PositiveRationalLaw (Fin n)),
    machine.OutputsWithin
      (CodeDCanonicalSourceV2.encodedSource (IndexedLaw.construct 8192 μ.weight q))
      (StoredWeightedState.lawBytes (((executableCodeD 8192).run q n μ).law))
      (C*((CodeDCanonicalSourceV2.encodedSource (IndexedLaw.construct 8192 μ.weight q)).length+1)^E) := by
  obtain ⟨C,E,h⟩ := actual_uniform
  exact ⟨C,E,h 8192⟩

#print axioms actual_uniform
#print axioms actual8192_uniform
end CurrentAdditive.IndexedLawBytes
