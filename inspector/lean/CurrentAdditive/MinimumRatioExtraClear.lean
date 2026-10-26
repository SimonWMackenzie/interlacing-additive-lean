import CurrentAdditive.MinimumRatioStepPhysicalBridge

namespace CurrentAdditive.MinimumRatioExtraClear

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.MinimumRatioCallbackLayout

noncomputable def extraBank : Fin 17 ↪ Stack where
  toFun j := low ⟨15+j.val, by omega⟩
  inj' := by
    intro a b h
    apply Fin.ext
    have hv := congrArg Fin.val h
    simp [low] at hv
    omega

abbrev Label := Fin 18 ⊕ Unit
abbrev Control := Unit × Option Bool

def next (j : Fin 18) (h : j.val < 17) : Fin 18 :=
  ⟨j.val+1, by omega⟩

noncomputable def program : Label →
    TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl j =>
      if h : j.val < 17 then
        BitMachineClearBank.clearStep (extraBank ⟨j.val,h⟩)
          (.inl j) (.inl (next j h))
      else BitMachineClearBank.finishStep id (.inr ())
  | .inr () => .halt

theorem run (S : Bank) :
    ((advance program)^[(∑ j : Fin 17, (S (extraBank j)).length)+19])
      (⟨some (.inl 0), ((),none), S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, ((),none), BitMachineClearBank.cleared extraBank S⟩ := by
  have hsteps : ∀ j : Fin 17,
      program (.inl j.castSucc) =
      BitMachineClearBank.clearStep (extraBank j)
        (.inl j.castSucc) (.inl j.succ) := by
    intro j
    have hn : next j.castSucc (by simpa using j.isLt) = j.succ := by
      apply Fin.ext
      rfl
    simpa [program, j.isLt, hn]
  have hfinish : program (.inl (Fin.last 17)) =
      BitMachineClearBank.finishStep id (.inr ()) := by
    simp [program]
  have hr := BitMachineClearBank.clear_bank_run program id (.inr ())
    17 extraBank extraBank.injective (fun j : Fin 18 => .inl j)
    hsteps hfinish () S
  rw [show (∑ j : Fin 17, (S (extraBank j)).length)+19 =
      1 + ((∑ j : Fin 17, (S (extraBank j)).length)+17+1) by omega,
    Function.iterate_add_apply]
  rw [hr]
  simp [advance, program, TM2.step]

theorem covered (j : Fin 32) (hj : 15 ≤ j.val) :
    ∃ i : Fin 17, extraBank i = low j := by
  let i : Fin 17 := ⟨j.val-15, by have := j.isLt; omega⟩
  refine ⟨i, ?_⟩
  apply Fin.ext
  simp [extraBank, low, i]
  omega

theorem cleaned_eq (S U : Bank) (best : List Bool)
    (hS : CurrentAdditive.MinimumRatioCallbackFull.ScratchEmpty S)
    (hforeign : ∀ k : Stack, (¬∃ i : Fin 17, extraBank i = k) →
      U k = (Function.update S (low 9) best) k) :
    BitMachineClearBank.cleared extraBank U =
      Function.update S (low 9) best := by
  funext k
  by_cases hi : ∃ i : Fin 17, extraBank i = k
  · obtain ⟨i, rfl⟩ := hi
    rw [BitMachineClearBank.cleared_bank]
    have hne : extraBank i ≠ low 9 := by
      intro he
      have hv := congrArg Fin.val he
      simp [extraBank, low] at hv
      omega
    rw [Function.update_of_ne hne]
    simpa only [extraBank] using
      (hS.1 ⟨15+i.val, by have := i.isLt; omega⟩ (by simp)).symm
  · rw [BitMachineClearBank.cleared_foreign]
    · exact hforeign k hi
    · intro i he
      exact hi ⟨i, he⟩

end CurrentAdditive.MinimumRatioExtraClear
