import CurrentAdditive.IndexedSeedPhysicalBinding

/-! The physical seed payload is the actual matrix field of the indexed
construction's initial stage. -/

namespace CurrentAdditive.IndexedExecutableStepRecovery

open EthInapproximability.CurrentPaper
open CurrentAdditive.DeterministicParameters

theorem indexed_seed_stage_payload_physical :
    ∃ M : BitMachine.Machine, ∃ C E : ℕ, ∀ L : ℕ, 2 ≤ L →
      M.OutputsWithin (List.replicate (N L) true)
        (MatrixMaterialization.rowMajor (indexedSeedStage L).matrix)
        (C * (N L + 1) ^ E) := by
  obtain ⟨M, C, E, hM⟩ := indexed_seed_table_physical
  refine ⟨M, C, E, ?_⟩
  intro L hL
  exact hM L hL

#print axioms indexed_seed_stage_payload_physical

end CurrentAdditive.IndexedExecutableStepRecovery
