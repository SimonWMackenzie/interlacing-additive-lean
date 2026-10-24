import Paper2.CodeRecursiveSeedJoin
import CurrentAdditive.V39DeadCodeInitialLayout
import CurrentAdditive.V39DeadCodeLoop

/-! The physically constructed seed occupies precisely the loop input
bank. The literal public count cells and fuel are not reconstructed by fiat. -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

namespace CurrentAdditive.V39DeadCodeSeedLayout

open Paper2

open Paper2.GeneratorCode Paper2.GeneratorSerialization
open CurrentAdditive.V39DeadCodeLoop Paper2.CodeRecursiveSeedPrep
open Paper2.CodeRecursiveSeedJoin
open CurrentAdditive.V39DeadCodeInitialLayout
open Paper2.CodeRowsGraphCompiler
open CurrentAdditive.V39DeadCodeReentry
open EthInapproximability.CurrentPaper

theorem seed_clean_at (n s q₁ q₂ w Q p : Nat)
    (fuel : List Bool) (j : RoundStack) :
    seedClean n s q₁ q₂ w Q p fuel (embedRound j) =
      Paper2.CodeRecursiveColumn.initial n s q₁ q₂ w Q
        (copies p .bit) (.ticket p) j := by
  by_cases hj : j ∈ keepAfter
  · simp only [keepAfter, publicCells, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with h | h
    · rcases h with h | h | h | h | h | h
      · subst j
        change seedClean n s q₁ q₂ w Q p fuel 12 = _
        simp [seedClean, CodeRecursiveSeedRow.afterRow,
          afterCountCopy, CodeRecursiveSeedPrep.afterTicket, publicBase,
          initial_core_at n s q₁ q₂ w Q _ _ 12 (by decide),
          CodeRowsGraphCompiler.initial_q₂]
      · subst j
        change seedClean n s q₁ q₂ w Q p fuel 16 = _
        simp [seedClean, CodeRecursiveSeedRow.afterRow,
          afterCountCopy, CodeRecursiveSeedPrep.afterTicket, publicBase,
          initial_core_at n s q₁ q₂ w Q _ _ 16 (by decide),
          CodeRowsGraphCompiler.initial_q₁]
      · subst j
        change seedClean n s q₁ q₂ w Q p fuel 17 = _
        simp [seedClean, CodeRecursiveSeedRow.afterRow,
          afterCountCopy, CodeRecursiveSeedPrep.afterTicket, publicBase,
          initial_core_at n s q₁ q₂ w Q _ _ 17 (by decide),
          CodeRowsGraphCompiler.initial_s]
      · subst j
        change seedClean n s q₁ q₂ w Q p fuel 18 = _
        simp [seedClean, CodeRecursiveSeedRow.afterRow,
          afterCountCopy, CodeRecursiveSeedPrep.afterTicket, publicBase,
          initial_core_at n s q₁ q₂ w Q _ _ 18 (by decide),
          CodeRowsGraphCompiler.initial_n]
      · subst j
        change seedClean n s q₁ q₂ w Q p fuel 31 = _
        simp [seedClean, CodeRecursiveSeedRow.afterRow,
          afterCountCopy, CodeRecursiveSeedPrep.afterTicket, publicBase,
          Paper2.CodeRecursiveColumn.initial,
          Paper2.CodeRecursiveColumn.foreign_at w Q (.ticket p) _ 31 (by decide),
          Paper2.CodeRecursiveColumn.foreignWords]
      · subst j
        change seedClean n s q₁ q₂ w Q p fuel 32 = _
        simp [seedClean, CodeRecursiveSeedRow.afterRow,
          afterCountCopy, CodeRecursiveSeedPrep.afterTicket, publicBase,
          Paper2.CodeRecursiveColumn.initial,
          Paper2.CodeRecursiveColumn.foreign_at w Q (.ticket p) _ 32 (by decide),
          Paper2.CodeRecursiveColumn.foreignWords]
    · rcases h with h | h
      · subst j
        change seedClean n s q₁ q₂ w Q p fuel 2 = _
        simp [seedClean, CodeRecursiveSeedRow.afterRow,
          afterCountCopy, CodeRecursiveSeedPrep.afterTicket,
          initial_core_at n s q₁ q₂ w Q _ _ 2 (by decide),
          CodeRowsGraphCompiler.initial_child]
      · subst j
        change seedClean n s q₁ q₂ w Q p fuel 33 = _
        simp [seedClean, CodeRecursiveSeedRow.afterRow,
           afterCountCopy, CodeRecursiveSeedPrep.afterTicket,
           Paper2.CodeRecursiveColumn.initial,
           Paper2.CodeRecursiveColumn.foreign_at w Q (.ticket p) _ 33 (by decide),
           Paper2.CodeRecursiveColumn.foreignWords]
  · have hright := initial_other_blank n s q₁ q₂ w Q
      (copies p .bit) (.ticket p) j hj
    rw [hright]
    have h2 : j ≠ (2 : RoundStack) := by
      intro h; subst j; exact hj (by decide)
    have h33 : j ≠ (33 : RoundStack) := by
      intro h; subst j; exact hj (by decide)
    have h12 : j ≠ (12 : RoundStack) := by
      intro h; subst j; exact hj (by decide)
    have h16 : j ≠ (16 : RoundStack) := by
      intro h; subst j; exact hj (by decide)
    have h17 : j ≠ (17 : RoundStack) := by
      intro h; subst j; exact hj (by decide)
    have h18 : j ≠ (18 : RoundStack) := by
      intro h; subst j; exact hj (by decide)
    have h31 : j ≠ (31 : RoundStack) := by
      intro h; subst j; exact hj (by decide)
    have h32 : j ≠ (32 : RoundStack) := by
      intro h; subst j; exact hj (by decide)
    by_cases h63 : j = (63 : RoundStack)
    · subst j
      change Function.update
        (CodeRecursiveSeedRow.afterRow n s q₁ q₂ w Q p fuel)
        63 [] 63 = []
      simp
    · have hne (m : RoundStack) (hm : j ≠ m) :
          embedRound j ≠ embedRound m := by
        intro h
        exact hm (embedRound.injective h)
      have h2' : embedRound j ≠ (2 : V39DeadCodeLoop.Stack) :=
        hne 2 h2
      have h33' : embedRound j ≠ (33 : V39DeadCodeLoop.Stack) :=
        hne 33 h33
      have h12' : embedRound j ≠ (12 : V39DeadCodeLoop.Stack) :=
        hne 12 h12
      have h16' : embedRound j ≠ (16 : V39DeadCodeLoop.Stack) :=
        hne 16 h16
      have h17' : embedRound j ≠ (17 : V39DeadCodeLoop.Stack) :=
        hne 17 h17
      have h18' : embedRound j ≠ (18 : V39DeadCodeLoop.Stack) :=
        hne 18 h18
      have h31' : embedRound j ≠ (31 : V39DeadCodeLoop.Stack) :=
        hne 31 h31
      have h32' : embedRound j ≠ (32 : V39DeadCodeLoop.Stack) :=
        hne 32 h32
      have h63' : embedRound j ≠ (63 : V39DeadCodeLoop.Stack) :=
        hne 63 h63
      by_cases h41' : embedRound j = (41 : V39DeadCodeLoop.Stack)
      · rw [h41']
        simp [seedClean, CodeRecursiveSeedRow.afterRow,
          afterCountCopy]
      · have h64' : embedRound j ≠ (64 : V39DeadCodeLoop.Stack) := by
          intro h
          have hv := congrArg Fin.val h
          simp [embedRound] at hv
          omega
        simp [seedClean, CodeRecursiveSeedRow.afterRow,
          afterCountCopy, CodeRecursiveSeedPrep.afterTicket,
          publicBase, h41', h2', h33', h12', h16', h17',
          h18', h31', h32', h63', h64']

theorem seed_clean_is_loop_bank (n s q₁ q₂ w Q p : Nat)
    (fuel : List Bool) :
    seedClean n s q₁ q₂ w Q p fuel =
      BitMachineStackEmbedding.bank embedRound (foreign fuel)
        (Paper2.CodeRecursiveColumn.initial n s q₁ q₂ w Q
          (copies p .bit) (.ticket p)) := by
  funext i
  by_cases hi : i = (64 : V39DeadCodeLoop.Stack)
  · subst i
    rw [BitMachineStackEmbedding.bank_outside]
    · simp [seedClean, CodeRecursiveSeedRow.afterRow,
        afterCountCopy, CodeRecursiveSeedPrep.afterTicket, publicBase, foreign]
    · rintro ⟨j,hj⟩
      have hv := congrArg Fin.val hj
      simp [embedRound] at hv
      omega
  · have hval : i.val ≠ 64 := by
      intro h
      exact hi (Fin.ext h)
    have hlt : i.val < 64 := by omega
    let j : RoundStack := ⟨i.val, hlt⟩
    have he : embedRound j = i := Fin.ext rfl
    rw [← he, BitMachineStackEmbedding.bank_at]
    exact seed_clean_at n s q₁ q₂ w Q p fuel j

#print axioms seed_clean_is_loop_bank

end CurrentAdditive.V39DeadCodeSeedLayout
