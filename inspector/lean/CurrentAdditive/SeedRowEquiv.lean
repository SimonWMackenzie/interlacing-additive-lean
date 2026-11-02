import Paper2.SeedTableFinal

/-! The explicit seed-row decoder used by the inherited physical printer.
Its forward function is executable `Nat.testBit`; the inverse certifies that
all Boolean rows occur exactly once and is never used as a machine step. -/

namespace CurrentAdditive.IndexedExecutableStepRecovery

open SeedT45.SeedTable

noncomputable def seedRowEquiv (p : ℕ) :
    Fin (2 ^ p) ≃ (Fin p → Bool) :=
  Equiv.ofBijective (seedRow p) (seedRow_bijective p)

theorem seedRowEquiv_apply (p : ℕ) (i : Fin (2 ^ p)) :
    seedRowEquiv p i = seedRow p i := rfl

#print axioms seedRowEquiv_apply

end CurrentAdditive.IndexedExecutableStepRecovery
