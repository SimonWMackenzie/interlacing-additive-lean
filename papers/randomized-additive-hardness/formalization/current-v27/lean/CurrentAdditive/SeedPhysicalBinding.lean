import Paper2.SeedTableFinal
import Paper2.LookupSeed

/-! Private v27 Appendix A, `cl:seed` binding. The inherited machine is a
literal finite bit-machine program with a charged polynomial clock; this
adapter identifies its output with the complete coordinate-evaluation table. -/

namespace CurrentAdditive.DeterministicSeedPhysical

open EthInapproximability.CurrentPaper

theorem seed_truth_table_physical :
    ∃ M : BitMachine.Machine, ∃ C E : ℕ, ∀ n : ℕ, 4 ≤ n →
      let L := Nat.clog 2 n
      let p := Paper2.LookupSeed.width L
      M.OutputsWithin (List.replicate n true)
        (MatrixMaterialization.rowMajor
          (fun (k : Fin (2 ^ p)) (j : Fin p) =>
            Paper2.LookupSeed.matrix p (SeedT45.SeedTable.seedRow p k) j))
        (C * (n + 1) ^ E) ∧
      Function.Bijective (SeedT45.SeedTable.seedRow p) ∧
      2 ^ p < n ^ 256 := by
  obtain ⟨M, C, E, hM⟩ := SeedT45.SeedTableFinal.seed_table_machine
  refine ⟨M, C, E, ?_⟩
  intro n hn
  exact ⟨hM n hn, SeedT45.SeedTable.seedRow_bijective _,
    Paper2.LookupSeed.rows_source_bound n hn⟩

#print axioms seed_truth_table_physical

end CurrentAdditive.DeterministicSeedPhysical
