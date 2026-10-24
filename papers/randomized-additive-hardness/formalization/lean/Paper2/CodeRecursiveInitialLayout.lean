import Paper2.CodeRecursiveReentry

/-! The reentry bank is exactly the public-input bank of the frozen
successor compiler, not merely a bank carrying its two desired outputs. -/

set_option maxHeartbeats 1000000

namespace Paper2.CodeRecursiveInitialLayout

open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.CodeRowsJoin Paper2.CodeRowsPreparation
open Paper2.CodeRowsGraphCompiler
open Paper2.CodeRowsArmA
open Paper2.CodeRecursiveColumn Paper2.CodeRecursiveRow
open Paper2.CodeRecursiveStep
open Paper2.CodeRecursiveReentry
open EthInapproximability.CurrentPaper

theorem initial_core_at (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) (i : Stack) (hi : i.val ≤ 30) :
    initial n s q₁ q₂ w Q previousRow previousCol i =
      initialBank n s q₁ q₂ previousRow ⟨i.val, by omega⟩ := by
  let j : FinalBank := ⟨i.val, by omega⟩
  have hj : embedRow j = i := Fin.ext rfl
  have h := BitMachineStackEmbedding.bank_at embedRow
    (foreignWords w Q previousCol)
    (initialBank n s q₁ q₂ previousRow) j
  change initial n s q₁ q₂ w Q previousRow previousCol
    (embedRow j) = initialBank n s q₁ q₂ previousRow j at h
  rw [hj] at h
  exact h

theorem initial_other_blank (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) (i : Stack)
    (hi : i ∉ keepAfter) :
    initial n s q₁ q₂ w Q previousRow previousCol i = [] := by
  have notVal (m : Stack) (hm : m ∈ keepAfter) : i.val ≠ m.val := by
    intro h
    have he : i = m := Fin.ext h
    exact hi (he ▸ hm)
  have h2 := notVal 2 (by decide)
  have h12 := notVal 12 (by decide)
  have h16 := notVal 16 (by decide)
  have h17 := notVal 17 (by decide)
  have h18 := notVal 18 (by decide)
  have h31 := notVal 31 (by decide)
  have h32 := notVal 32 (by decide)
  have h33 := notVal 33 (by decide)
  by_cases hcore : i.val ≤ 30
  · rw [initial_core_at n s q₁ q₂ w Q previousRow previousCol i hcore]
    let j : FinalBank := ⟨i.val, by omega⟩
    change initialBank n s q₁ q₂ previousRow j = []
    by_cases hhigh : 22 ≤ i.val
    · exact initial_blank_high n s q₁ q₂ previousRow j (by omega)
    by_cases hprep : 19 ≤ i.val
    · let p : PrepBank := ⟨i.val, by omega⟩
      have hp : embedPrep p = j := Fin.ext rfl
      rw [← hp, initialBank, BitMachineStackEmbedding.bank_at]
      have hout : ¬ ∃ t : TemplateBank, embedTemplate t = p := by
        rintro ⟨t,ht⟩
        have hv : t.val = i.val := by
          simpa [embedTemplate, p] using congrArg Fin.val ht
        omega
      rw [prepBefore, BitMachineStackEmbedding.bank_outside
        embedTemplate (prepForeign n) _ p hout]
      have hne : p ≠ (18 : PrepBank) := by
        intro h
        have hv : i.val = 18 := by
          simpa [p] using congrArg Fin.val h
        omega
      simp [prepForeign, hne]
    · have hsmall : i.val ≤ 15 := by omega
      let b : Bank := ⟨i.val, by omega⟩
      have hb : embedPrep (embedTemplate (embedTicketBank (embedOld b))) = j :=
        Fin.ext rfl
      rw [← hb]
      exact initial_core_other_blank n s q₁ q₂ previousRow b
        (by
          intro h
          have hv : i.val = 2 := by simpa [b] using congrArg Fin.val h
          exact h2 hv)
        (by
          intro h
          have hv : i.val = 12 := by simpa [b] using congrArg Fin.val h
          exact h12 hv)
  · have hforeign : 31 ≤ i.val := by omega
    rw [initial, foreign_at w Q previousCol _ i hforeign]
    have h31' : i ≠ (31 : Stack) := by
      intro h; have hv := congrArg Fin.val h; exact h31 hv
    have h32' : i ≠ (32 : Stack) := by
      intro h; have hv := congrArg Fin.val h; exact h32 hv
    have h33' : i ≠ (33 : Stack) := by
      intro h; have hv := congrArg Fin.val h; exact h33 hv
    simp [foreignWords, h31', h32', h33']

theorem reentered_is_initial (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    reentered (afterRow n s q₁ q₂ w Q previousRow previousCol) =
      initial n s q₁ q₂ w Q
        (rowCode q₁ q₂ s w Q previousCol)
        (columnCode n s q₁ q₂ w Q previousRow) := by
  funext i
  by_cases hi : i ∈ keepAfter
  · simp only [keepAfter, publicCells, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with h | h
    · rcases h with h | h | h | h | h | h
      · subst i
        rw [reentered_public _ 12 (by decide), raw_q₂_retained]
        rw [initial_core_at n s q₁ q₂ w Q _ _ 12 (by decide)]
        change List.replicate q₂ true = initialBank n s q₁ q₂ _ 12
        rw [initial_q₂]
      · subst i
        rw [reentered_public _ 16 (by decide), raw_q₁_retained]
        rw [initial_core_at n s q₁ q₂ w Q _ _ 16 (by decide)]
        change List.replicate q₁ true = initialBank n s q₁ q₂ _ 16
        rw [initial_q₁]
      · subst i
        rw [reentered_public _ 17 (by decide), raw_s_retained]
        rw [initial_core_at n s q₁ q₂ w Q _ _ 17 (by decide)]
        change List.replicate s true = initialBank n s q₁ q₂ _ 17
        rw [initial_s]
      · subst i
        rw [reentered_public _ 18 (by decide), raw_n_retained]
        rw [initial_core_at n s q₁ q₂ w Q _ _ 18 (by decide)]
        change List.replicate n true = initialBank n s q₁ q₂ _ 18
        rw [initial_n]
      · subst i
        rw [reentered_public _ 31 (by decide), raw_w_retained]
        rw [initial, foreign_at w Q _ _ 31 (by decide)]
        rfl
      · subst i
        rw [reentered_public _ 32 (by decide), raw_Q_retained]
        rw [initial, foreign_at w Q _ _ 32 (by decide)]
        rfl
    · rcases h with h | h
      · subst i
        rw [reentered_row, CodeRecursiveStep.row_output]
        rw [initial_core_at n s q₁ q₂ w Q _ _ 2 (by decide)]
        change encodeCode (rowCode q₁ q₂ s w Q previousCol) =
          initialBank n s q₁ q₂ _ 2
        rw [initial_child]
      · subst i
        rw [reentered_column, CodeRecursiveStep.column_output]
        rw [initial, foreign_at w Q _ _ 33 (by decide)]
        rfl
  · rw [reentered_other _ i hi,
      initial_other_blank n s q₁ q₂ w Q _ _ i hi]

#print axioms reentered_is_initial

end Paper2.CodeRecursiveInitialLayout
