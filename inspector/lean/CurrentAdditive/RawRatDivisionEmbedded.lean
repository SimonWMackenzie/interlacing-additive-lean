import CurrentAdditive.RawRatPreGCD
import EthInapproximability.CurrentPaper.BitMachineStackRun
import Mathlib.Tactic

/-!
The restoring long-division program on the shared rational arithmetic region.
Its dividend is MSB-first at bank 3, its positive divisor is LSB-first at
bank 4, and the output quotient is LSB-first at bank 9.
-/
namespace CurrentAdditive.RawRatDivisionEmbedded

open Turing
open EthInapproximability.CurrentPaper
open BitMachineEncoding

abbrev Bank := RawRatPreparation.Bank

def program := fun l => BitMachineStackEmbedding.stackStmt
  RawRatGCDStage.location (BitMachineBinaryDivision.program l)

noncomputable def result (S : Bank) : Bank :=
  BitMachineStackEmbedding.bank RawRatGCDStage.location S
    (BitMachineBinaryDivision.finalBank (S 3) (S 4))

def clock (S : Bank) : Nat :=
  BitMachineBinaryDivision.totalTime (S 3) (S 4) []

theorem local_initial (S : Bank)
    (h2 : S 8 = []) (h3 : S 9 = []) (h4 : S 10 = [])
    (h5 : S 11 = []) (h6 : S 12 = []) :
    (fun i : Fin 7 => S (RawRatGCDStage.location i)) =
      BitMachineBinaryDivision.initialBank (S 3) (S 4) := by
  funext i
  fin_cases i <;>
    simp [RawRatGCDStage.location, BitMachineBinaryDivision.initialBank,
      BitMachineBinaryDivision.bank, h2, h3, h4, h5, h6]

theorem run (S : Bank)
    (h2 : S 8 = []) (h3 : S 9 = []) (h4 : S 10 = [])
    (h5 : S 11 = []) (h6 : S 12 = []) :
    ((advance program)^[clock S])
      (⟨some BitMachineBinaryDivision.Label.outer,
        BitMachineBinaryDivision.initial, S⟩ :
        TM2.Cfg (fun _ : Fin 13 => Bool) _ _) =
      ⟨none, BitMachineBinaryDivision.initial, result S⟩ := by
  have hlocal := local_initial S h2 h3 h4 h5 h6
  have hs := BitMachineStackRun.run RawRatGCDStage.location S
    BitMachineBinaryDivision.program
    (BitMachineBinaryDivision.cfg (some .outer) BitMachineBinaryDivision.initial
      (S 3) (S 4) [] [] [] [] []) (clock S)
  have hbank : BitMachineStackEmbedding.bank RawRatGCDStage.location S
      (BitMachineBinaryDivision.initialBank (S 3) (S 4)) = S := by
    rw [← hlocal]
    exact BitMachineStackEmbedding.bank_restrict RawRatGCDStage.location S
  change ((advance program)^[clock S])
      ⟨some BitMachineBinaryDivision.Label.outer,
        BitMachineBinaryDivision.initial,
        BitMachineStackEmbedding.bank RawRatGCDStage.location S
          (BitMachineBinaryDivision.initialBank (S 3) (S 4))⟩ =
      BitMachineStackEmbedding.stackCfg RawRatGCDStage.location S
        (BitMachineBinaryDivision.run (clock S)
          (BitMachineBinaryDivision.cfg (some .outer)
            BitMachineBinaryDivision.initial (S 3) (S 4) [] [] [] [] [])) at hs
  rw [hbank] at hs
  change ((advance program)^[clock S])
      ⟨some BitMachineBinaryDivision.Label.outer,
        BitMachineBinaryDivision.initial, S⟩ =
      BitMachineStackEmbedding.stackCfg RawRatGCDStage.location S
        (BitMachineBinaryDivision.run
          (BitMachineBinaryDivision.totalTime (S 3) (S 4) [])
          (BitMachineBinaryDivision.cfg (some .outer)
            BitMachineBinaryDivision.initial (S 3) (S 4) [] [] [] [] [])) at hs
  rw [BitMachineBinaryDivision.total_run] at hs
  simpa [clock, result, BitMachineBinaryDivision.finalBank] using hs

theorem quotient_value (S : Bank)
    (hd : 0 < EncodedCommunication.bitsValue (S 4)) :
    EncodedCommunication.bitsValue (result S 9) =
      BitMachineBinaryDivision.msbValue (S 3) /
        EncodedCommunication.bitsValue (S 4) := by
  have hs := (BitMachineBinaryDivision.standard_division_spec (S 3) (S 4) hd).1
  change EncodedCommunication.bitsValue
      (BitMachineStackEmbedding.bank RawRatGCDStage.location S
        (BitMachineBinaryDivision.finalBank (S 3) (S 4))
          (RawRatGCDStage.location 3)) = _
  rw [BitMachineStackEmbedding.bank_at]
  simpa [BitMachineBinaryDivision.finalBank,
    BitMachineBinaryDivision.bank] using hs

theorem clock_bound (S : Bank) :
    clock S ≤ (S 3).length *
      (4 * ((S 3).length + (S 4).length + 1) + 5) + 1 := by
  simpa [clock] using
    BitMachineBinaryDivision.totalTime_bound (S 3) (S 4) []
      (S 3).length (by simp) le_rfl

end CurrentAdditive.RawRatDivisionEmbedded
