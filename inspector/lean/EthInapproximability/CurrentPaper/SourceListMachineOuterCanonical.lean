import EthInapproximability.CurrentPaper.SourceListMachineOuterLoop

/-! Canonical input bank for the physical list loop. -/

namespace EthInapproximability.CurrentPaper.SourceListMachineOuter

open Turing TM2.Stmt BitMachine BitMachineEncoding EncodedCommunication

variable (M : Machine)

theorem initial_invariant (xs : List (List Bool)) :
    LoopInvariant M
      (initBanks M (SourceListEncoding.encode xs)
        {input := SourceListEncoding.fields xs, count := xs.length.bits,
          output := (natField xs.length).reverse} [])
      (SourceListEncoding.fields xs) xs.length.bits (natField xs.length).reverse := by
  let d : SourceListMachineInitialize.Data :=
    {input := SourceListEncoding.fields xs, count := xs.length.bits,
      output := (natField xs.length).reverse}
  let S := initBanks M (SourceListEncoding.encode xs) d []
  have houtside (j : Stack M) (hj : ¬ ∃ k : SourceListMachineInitialize.Stack,
      initStack M k = j) : S j = banks M (SourceListEncoding.encode xs) [] [] [] j :=
    BitMachineStackEmbedding.bank_outside (initStack M) _ d.stacks j hj
  constructor
  · intro k
    cases k with
    | inl k =>
        change ([] : List Bool) = S (.inl (.inl k))
        rw [houtside]
        · rfl
        · rintro ⟨j,hj⟩
          fin_cases j <;> cases hj
    | inr k =>
        fin_cases k
        · change SourceListEncoding.fields xs = S (.inl (.inr 0))
          exact (init_input M _ d []).symm
        · change ([] : List Bool) = S (.inl (.inr 1))
          exact (init_saved M _ d []).symm
        · change ([] : List Bool) = S (.inl (.inr 2))
          rw [houtside]
          · rfl
          · rintro ⟨j,hj⟩; fin_cases j <;> cases hj
        · change ([] : List Bool) = S (.inl (.inr 3))
          rw [houtside]
          · rfl
          · rintro ⟨j,hj⟩; fin_cases j <;> cases hj
        · change ([] : List Bool) = S (.inl (.inr 4))
          rw [houtside]
          · rfl
          · rintro ⟨j,hj⟩; fin_cases j <;> cases hj
        · change ([] : List Bool) = S (.inl (.inr 5))
          rw [houtside]
          · rfl
          · rintro ⟨j,hj⟩; fin_cases j <;> cases hj
        · change ([] : List Bool) = S (.inl (.inr 6))
          rw [houtside]
          · rfl
          · rintro ⟨j,hj⟩; fin_cases j <;> cases hj
        · change (natField xs.length).reverse = S (.inl (.inr 7))
          exact (init_accumulator M _ d []).symm
  · exact init_count M _ d []
  · exact init_temp M _ d []
  · change S (.inr 2) = []
    rw [houtside]
    · rfl
    · rintro ⟨j,hj⟩
      fin_cases j <;> cases hj

end EthInapproximability.CurrentPaper.SourceListMachineOuter
