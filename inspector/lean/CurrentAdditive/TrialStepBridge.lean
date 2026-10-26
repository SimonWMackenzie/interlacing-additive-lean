import CurrentAdditive.DivisionBitStep
import CurrentAdditive.DivisionRec

/-!
The physical conditional-XOR machine executes exactly one of the semantic
steps in the frozen trial-remainder recurrence. This does not yet join the
steps into a complete divisor-testing TM: dropping the known zero top bit,
changing the shift, and controlling the loop remain separate tasks.
-/

namespace CurrentAdditive.FieldMachineHelper.TrialStepBridge

open CurrentAdditive.FieldMachineHelper.DivisionBitStep
open EthInapproximability.CurrentPaper.SamplerMachineAccumulate

open CurrentAdditive.FiniteFieldConstructor.TrialSearch (monicBits)
open CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge
  (step monicBits_shifted_topBit)

theorem physical_trial_step (e i tail acc : ℕ)
    (htail : tail < 2 ^ e) :
    run (2 * (e + i + 1) + 2)
      (cfg (some .scan) (acc.testBit (e + i), none, none)
        (bitsBE (e + i + 1) acc)
        (bitsBE (e + i + 1)
          ((monicBits e tail) <<< i)) [] []) =
    cfg none (acc.testBit (e + i), none, none)
      (bitsBE (e + i + 1)
        (step e i (monicBits e tail) acc))
      (bitsBE (e + i + 1)
        ((monicBits e tail) <<< i)) [] [] := by
  have htop := monicBits_shifted_topBit e i tail htail
  simpa only [step] using
    run_cancel_nat_step (e + i) acc
      ((monicBits e tail) <<< i) htop

#print axioms physical_trial_step

end CurrentAdditive.FieldMachineHelper.TrialStepBridge
