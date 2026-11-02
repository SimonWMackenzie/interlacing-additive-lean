import CurrentAdditive.TrialSearchCombinedZero

/-! Physical cleanup and callback result transfer after a remainder test. -/

namespace CurrentAdditive.FieldMachineHelper.TrialSearchCombinedCleanup

open Turing
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine

private theorem run_succ {c e : Config}
    (h : TM2.step program c = some e) (t : Nat) :
    run (t + 1) c = run t e := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem step_clear_cons (r : Registers) (S : Fin 12 → List Bool)
    (b : Bool) (rest : List Bool) (hs : S 4 = b :: rest) :
    TM2.step program ⟨some .clearDivisor, r, S⟩ =
      some ⟨some .clearDivisor,
        {r with outer := (r.zero.1, r.outer.2.1, some b)},
        Function.update S 4 rest⟩ := by
  simp [TM2.step, TM2.stepAux, program, hs]

private theorem step_clear_nil (r : Registers) (S : Fin 12 → List Bool)
    (hs : S 4 = []) :
    TM2.step program ⟨some .clearDivisor, r, S⟩ =
      some ⟨some (.outer .afterTest),
        {r with outer := (r.zero.1, r.outer.2.1, none)}, S⟩ := by
  simp [TM2.step, TM2.stepAux, program, hs,
    Function.update_eq_self_iff]

theorem clear_divisor_run (r : Registers) (S : Fin 12 → List Bool)
    (word : List Bool) (hs : S 4 = word) :
    run (word.length + 1) ⟨some .clearDivisor, r, S⟩ =
      ⟨some (.outer .afterTest),
        {r with outer := (r.zero.1, r.outer.2.1, none)},
        Function.update S 4 []⟩ := by
  induction word generalizing r S with
  | nil =>
    have h := step_clear_nil r S hs
    have hu : Function.update S 4 [] = S :=
      Function.update_eq_self_iff.mpr hs.symm
    rw [hu]
    simpa [run] using run_succ h 0
  | cons b rest ih =>
    have h := step_clear_cons r S b rest hs
    rw [List.length_cons, run_succ h]
    have hrest : (Function.update S 4 rest) 4 = rest := Function.update_self 4 rest S
    have htail := ih
      {r with outer := (r.zero.1, r.outer.2.1, some b)}
      (Function.update S 4 rest) hrest
    simpa [Function.update_idem] using htail

#print axioms clear_divisor_run

end CurrentAdditive.FieldMachineHelper.TrialSearchCombinedCleanup
