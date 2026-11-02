import EthInapproximability.CurrentPaper.BoundedBitMachine
import EthInapproximability.CurrentPaper.BitMachineFinalFlag

/-!
# Encoded bounded simulation with an explicit success bit

Source: frozen v8 `05-iteration.tex`, the bounded prefix clock. The first
returned bit says whether the source program halted within its unary budget;
the remaining bits are its output stack at the end of that budget. The
success bit is read from real finite control, not an uncharged predicate.
Preparation, bounded execution, and output of this bit all count as steps.
-/

namespace EthInapproximability.CurrentPaper.FlaggedBoundedBitMachine

open BitMachine
open BoundedBitMachine

variable (M : Machine)

noncomputable def completionFlag (v : Fin (BoundedBitMachine.machine M).controlCount) : Bool :=
  ((Fintype.equivFin (BoundedBitMachine.Control M)).symm v).2.isNone

noncomputable def machine : Machine :=
  BitMachineFinalFlag.machine (BoundedBitMachine.machine M) (completionFlag M)

noncomputable def report (input : List Bool) : List Bool :=
  completionFlag M ((BoundedBitMachine.machine M).run (2 * (input.length + 1))
    ((BoundedBitMachine.machine M).init input)).var :: result M input

theorem outputs_all (input : List Bool) :
    (machine M).OutputsWithin input (report M input) (2 * (input.length + 1) + 1) := by
  obtain ⟨hh, ho⟩ := outputsWithin_at_bound _ (BoundedBitMachine.outputs_all M input)
  have h := BitMachineFinalFlag.outputs (BoundedBitMachine.machine M) (completionFlag M)
    input (2 * (input.length + 1)) hh
  simpa only [machine, report, ho] using h

theorem report_polytime : Polytime (report M) := by
  refine ⟨machine M, 3, 1, fun input => ?_⟩
  exact outputsWithin_mono _ (outputs_all M input) (by simp only [pow_one]; omega)

theorem completionFlag_encoded_terminal (flag : Option Bool) (fuel : ℕ) (c : M.Config) :
    completionFlag M (encode M (terminal M flag fuel c)).var = flag.isNone := by
  unfold completionFlag encode BitMachineEncoding.renameCfg terminal
  exact congrArg (fun v : BoundedBitMachine.Control M => v.2.isNone)
    ((Fintype.equivFin (BoundedBitMachine.Control M)).symm_apply_apply (c.var, flag))

theorem report_packed (n : ℕ) (bits : List Bool) :
    report M (packed n bits) =
      decide ((M.run n (M.init bits)).l = none) :: (M.run n (M.init bits)).stk M.output := by
  obtain ⟨remaining, _, hr⟩ := packed_simulation M n bits
  have hsmall : 2 * (n + 1) ≤ 2 * ((packed n bits).length + 1) := by
    simp only [packed, List.length_append, List.length_replicate, List.length_cons]
    omega
  have hhalt : ((BoundedBitMachine.machine M).run (2 * (n + 1))
      ((BoundedBitMachine.machine M).init (packed n bits))).l = none := by rw [hr]; rfl
  have hbig : (BoundedBitMachine.machine M).run (2 * ((packed n bits).length + 1))
      ((BoundedBitMachine.machine M).init (packed n bits)) =
      (BoundedBitMachine.machine M).run (2 * (n + 1))
        ((BoundedBitMachine.machine M).init (packed n bits)) := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hsmall
    rw [hd, BitMachine.run_add, BitMachine.run_halted _ _ hhalt]
  unfold report
  rw [hbig, hr, completionFlag_encoded_terminal]
  simp only [result, parseBudget_packed]
  by_cases h : (M.run n (M.init bits)).l = none <;> simp [h]

/-- The normal input API both decides bounded halting and returns the exact
bounded output. No source termination hypothesis is required. -/
theorem packed_outputs (n : ℕ) (bits : List Bool) :
    (machine M).OutputsWithin (packed n bits)
      (decide ((M.run n (M.init bits)).l = none) :: (M.run n (M.init bits)).stk M.output)
      (2 * ((packed n bits).length + 1) + 1) := by
  simpa only [report_packed] using outputs_all M (packed n bits)

end EthInapproximability.CurrentPaper.FlaggedBoundedBitMachine
