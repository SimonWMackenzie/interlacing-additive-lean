import Paper2.SeedTableMachine
import Paper2.SeedTableClock

/-!
# WP-SEED: the literal effectivity clause of `cl:seed` (IA:689-691)

Lane `owner:a-seed-t45-1`. One fixed `BitMachine.Machine` (`SeedTable.seedMachine`) that on
unary `n ≥ 4` halts within `seedC·(n+1)^1536` steps with the row-major truth table of the actual
`LookupSeed.matrix p`, `p = LookupSeed.width ⌈log₂ n⌉` (the least power of two `≥ 64(L+1)`,
`L = ⌈log₂ n⌉`), rows enumerated by the bijection `seedRow p : Fin (2^p) → (Fin p → Bool)`.
-/

namespace SeedT45.SeedTableFinal

open EthInapproximability.CurrentPaper
open SeedT45.SeedTable

theorem seedBound_eq (n : ℕ) : seedBound n = SeedClock.clockExpr n := rfl

/-- **WP-SEED (T42, IA:689-691).** -/
theorem seed_table_machine :
    ∃ M : BitMachine.Machine, ∃ C E : ℕ, ∀ n : ℕ, 4 ≤ n →
      M.OutputsWithin (List.replicate n true)
        (MatrixMaterialization.rowMajor
          (fun (k : Fin (2 ^ Paper2.LookupSeed.width (Nat.clog 2 n)))
               (j : Fin (Paper2.LookupSeed.width (Nat.clog 2 n))) =>
            Paper2.LookupSeed.matrix (Paper2.LookupSeed.width (Nat.clog 2 n))
              (seedRow (Paper2.LookupSeed.width (Nat.clog 2 n)) k) j))
        (C * (n + 1) ^ E) := by
  refine ⟨seedMachine, SeedClock.seedC, 1536, fun n hn => ?_⟩
  obtain ⟨t, ht, hl, ho, -, -⟩ := seed_raw_run n
  have hb : t ≤ SeedClock.seedC * (n + 1) ^ 1536 :=
    le_trans ht (by rw [seedBound_eq]; exact SeedClock.clock_poly n hn)
  exact BitMachineEncoding.outputsWithin_of_raw_run _ _ _ _ Q _ _ t _ hb hl ho

/-- The companion facts: the rows enumerate the row input set `{0,1}^p` bijectively, and the
table's `k`-th block of `p` bits is the row word `seedRow p k` itself. -/
theorem seed_input_sets (p : ℕ) :
    Function.Bijective (seedRow p) ∧
    ∀ (k : Fin (2 ^ p)) (j : Fin p),
      (MatrixMaterialization.rowMajor (seedTable p))[k.val * p + j.val]? = some (seedRow p k j) :=
  ⟨seedRow_bijective p, fun k j => MatrixMaterialization.rowMajor_entry _ k j⟩

end SeedT45.SeedTableFinal

#print axioms SeedT45.SeedTableFinal.seed_table_machine
#print axioms SeedT45.SeedTableFinal.seed_input_sets
