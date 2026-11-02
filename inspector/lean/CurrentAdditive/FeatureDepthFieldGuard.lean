import CurrentAdditive.FeatureDepthGuard
import EthInapproximability.CurrentPaper.AllowanceBitPrograms
import EthInapproximability.CurrentPaper.BitMachineComposition

/-!
Physical depth test from the actual V2 count-field bytes.  A checked field
projection first extracts the canonical binary count; the fixed 16-label
guard then tests whether it is below 8192.  This still requires the outer
enumerator to physically select each feature's count field.
-/

namespace CurrentAdditive.FeatureDepthFieldGuard

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachine
open EthInapproximability.CurrentPaper.EncodedCommunication

noncomputable def machine : Machine :=
  BitMachineComposition.composition
    (BankFieldProjection.machine (0 : Fin 1))
    CurrentAdditive.FeatureDepthGuard.machine

theorem physical_count_field (n : Nat) :
    machine.OutputsWithin (natField n) [decide (n < 8192)]
      (6 * ((natField n).length + 1) + 2 * n.bits.length + 2 + 15) := by
  have hproject := BankFieldProjection.outputs (0 : Fin 1) (natField n)
  rw [AllowanceBitPrograms.project_natField] at hproject
  have hguard := CurrentAdditive.FeatureDepthGuard.physical_guard n
  simpa only [machine] using
    BitMachineComposition.composition_outputsWithin
      (BankFieldProjection.machine (0 : Fin 1))
      CurrentAdditive.FeatureDepthGuard.machine hproject hguard

#print axioms physical_count_field

end CurrentAdditive.FeatureDepthFieldGuard
