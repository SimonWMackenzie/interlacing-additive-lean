import CurrentAdditive.GaussWorkItemCallbackFields

/-! The exact bank invariant after one column request has been serialized,
framed, appended, and all transient banks cleared. -/

namespace CurrentAdditive.GaussWorkItemRoundBank

open EthInapproximability.CurrentPaper

abbrev Bank := GaussWorkItemCallbackFields.Bank

private noncomputable def cleaned (S : Bank → List Bool)
    (matrix free index raw field accumulated : List Bool)
    (W : BitMachineBankSerialize.Bank 3) : Bank → List Bool :=
  BitMachineClearBank.cleared GaussWorkItemDisposableCleanup.cells
    (Function.update
      (Function.update
        (Function.update
          (Function.update
            (GaussWorkItemCallbackFields.afterItem S matrix free index raw W)
            ⟨13, by omega⟩ field)
          ⟨24, by omega⟩ accumulated)
        ⟨8, by omega⟩ [])
      ⟨13, by omega⟩ [])

theorem clean_round (S : Bank → List Bool)
    (matrix free index raw field accumulated : List Bool)
    (W : BitMachineBankSerialize.Bank 3)
    (h6 : S ⟨6, by omega⟩ = [])
    (h7 : S ⟨7, by omega⟩ = [])
    (h8 : S ⟨8, by omega⟩ = [])
    (h9 : S ⟨9, by omega⟩ = [])
    (h10 : S ⟨10, by omega⟩ = [])
    (h11 : S ⟨11, by omega⟩ = [])
    (h13 : S ⟨13, by omega⟩ = []) :
    cleaned S matrix free index raw field accumulated W =
      Function.update S ⟨24, by omega⟩ accumulated := by
  funext z
  unfold cleaned
  by_cases h9z : z = (⟨9, by omega⟩ : Bank)
  · subst z
    change BitMachineClearBank.cleared
      GaussWorkItemDisposableCleanup.cells _
      (GaussWorkItemDisposableCleanup.cells 0) = _
    rw [BitMachineClearBank.cleared_bank]
    simp [h9]
  by_cases h10z : z = (⟨10, by omega⟩ : Bank)
  · subst z
    change BitMachineClearBank.cleared
      GaussWorkItemDisposableCleanup.cells _
      (GaussWorkItemDisposableCleanup.cells 1) = _
    rw [BitMachineClearBank.cleared_bank]
    simp [h10]
  by_cases h11z : z = (⟨11, by omega⟩ : Bank)
  · subst z
    change BitMachineClearBank.cleared
      GaussWorkItemDisposableCleanup.cells _
      (GaussWorkItemDisposableCleanup.cells 2) = _
    rw [BitMachineClearBank.cleared_bank]
    simp [h11]
  rw [GaussWorkItemDisposableCleanup.cleared_foreign _ z
    ⟨h9z, h10z, h11z⟩]
  by_cases h8z : z = (⟨8, by omega⟩ : Bank)
  · subst z; simp [h8]
  by_cases h13z : z = (⟨13, by omega⟩ : Bank)
  · subst z; simp [h13]
  by_cases h24z : z = (⟨24, by omega⟩ : Bank)
  · subst z; simp
  by_cases h6z : z = (⟨6, by omega⟩ : Bank)
  · subst z
    simp [GaussWorkItemCallbackFields.source_empty, h6]
  by_cases h7z : z = (⟨7, by omega⟩ : Bank)
  · subst z
    simp [GaussWorkItemCallbackFields.source_empty, h7]
  simp [GaussWorkItemCallbackFields.preserved,
    h6z, h7z, h8z, h9z, h10z, h11z, h13z, h24z]

#print axioms clean_round

end CurrentAdditive.GaussWorkItemRoundBank
