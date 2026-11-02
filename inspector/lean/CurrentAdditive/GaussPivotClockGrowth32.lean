import CurrentAdditive.GaussPivotRawToFinish32
import EthInapproximability.CurrentPaper.BitMachineStackGrowth

/-! A growth bound for the *same fixed Fin32 controller* used by the
raw pivot-to-packet theorem.  This includes all 32 banks, so later cleanup
cannot silently discard uncharged data. -/

namespace CurrentAdditive.GaussPivotClockGrowth32

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineStackGrowth
open CurrentAdditive.GaussStepFields32

noncomputable section

def pushConstant : Nat := perStep program

theorem bank_growth (start : Config) (t : Nat) (j : Stack) :
    ((run t start).stk j).length ≤
      (start.stk j).length + pushConstant * t := by
  exact run_growth program start t j

theorem bank_growth_from_charge (start : Config) (t charge : Nat)
    (hcharge : ∀ j : Stack, (start.stk j).length ≤ charge)
    (j : Stack) :
    ((run t start).stk j).length ≤ charge + pushConstant * t := by
  exact (bank_growth start t j).trans
    (Nat.add_le_add_right (hcharge j) _)

theorem reset_writer_clock_le (start : Config) (t charge : Nat)
    (hcharge : ∀ j : Stack, (start.stk j).length ≤ charge) :
    GaussWorkerReset32.clock (run t start).stk + 1 ≤
      8 * (charge + pushConstant * t) + 10 := by
  unfold GaussWorkerReset32.clock
  have h (j : Fin 8) :
      (((run t start).stk (GaussWorkerReset32.bank j)).length) ≤
        charge + pushConstant * t :=
    bank_growth_from_charge start t charge hcharge _
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 8))) => h j)
  simpa using Nat.add_le_add_right hs 10

theorem reset_assembler_clock_le (start : Config) (t charge : Nat)
    (hcharge : ∀ j : Stack, (start.stk j).length ≤ charge) :
    GaussAssemblerReset32.clock (run t start).stk + 1 ≤
      12 * (charge + pushConstant * t) + 14 := by
  unfold GaussAssemblerReset32.clock
  have h (j : Fin 12) :
      (((run t start).stk (GaussAssemblerReset32.bank j)).length) ≤
        charge + pushConstant * t :=
    bank_growth_from_charge start t charge hcharge _
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 12))) => h j)
  simpa using Nat.add_le_add_right hs 14

#print axioms bank_growth
#print axioms reset_writer_clock_le
#print axioms reset_assembler_clock_le

end
end CurrentAdditive.GaussPivotClockGrowth32
