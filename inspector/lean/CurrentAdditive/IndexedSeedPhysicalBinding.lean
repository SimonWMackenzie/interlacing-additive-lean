import CurrentAdditive.SeedIndexedStage
import Paper2.SeedTableFinal

/-! The inherited fixed lookup-table printer is bound to the explicit seed
row order at the public dyadic parameter.  This is the table payload only;
the rectangle header and the successor's source computation are separate. -/

namespace CurrentAdditive.IndexedExecutableStepRecovery

open EthInapproximability.CurrentPaper
open CurrentAdditive.DeterministicParameters
open CurrentAdditive.DeterministicETHSeed
open SeedT45.SeedTable

theorem indexed_seed_table_physical :
    ∃ M : BitMachine.Machine, ∃ C E : ℕ, ∀ L : ℕ, 2 ≤ L →
      M.OutputsWithin (List.replicate (N L) true)
        (MatrixMaterialization.rowMajor (indexedSeed L))
        (C * (N L + 1) ^ E) := by
  obtain ⟨M, C, E, hM⟩ := SeedT45.SeedTableFinal.seed_table_machine
  refine ⟨M, C, E, ?_⟩
  intro L hL
  have hn : 4 ≤ 2 ^ L := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by decide) hL
  have hm := hM (2 ^ L) hn
  rw [Nat.clog_pow 2 L (by decide)] at hm
  simpa only [N, indexedSeed, seedTable] using hm

#print axioms indexed_seed_table_physical

end CurrentAdditive.IndexedExecutableStepRecovery
