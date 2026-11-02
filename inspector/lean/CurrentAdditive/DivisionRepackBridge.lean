import CurrentAdditive.DivisionBitStep
import CurrentAdditive.DivisionRepackMachine
import CurrentAdditive.DivisionRec

/-!
The physical repack after a nonterminal trial-division XOR drops exactly
the two bit positions that disappear when the recurrence moves from shift
`i+1` to shift `i`. The shifted divisor is represented high-bit-first.
-/

namespace CurrentAdditive.FieldMachineHelper.DivisionRepackBridge

open CurrentAdditive.FieldMachineHelper.DivisionBitStep (bitsBE bitsBE_succ)
open CurrentAdditive.FiniteFieldConstructor.TrialSearch (monicBits)
open CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge
  (step monicBits_shifted_topBit divisionStep_topBit_false)

theorem bitsBE_shiftLeft_one (width value : Nat) :
    bitsBE (width + 1) (value <<< 1) = bitsBE width value ++ [false] := by
  induction width with
  | zero => simp [bitsBE]
  | succ width ih =>
    rw [bitsBE_succ, ih, bitsBE_succ]
    simp [Nat.testBit_shiftLeft, show 1 ≤ width + 1 by omega]

private theorem shiftLeft_succ (value i : Nat) :
    value <<< (i + 1) = (value <<< i) <<< 1 := by
  simp [Nat.shiftLeft_eq, pow_succ, Nat.mul_assoc]

theorem bitsBE_shifted_succ (e i divisor : Nat) :
    bitsBE (e + (i + 1) + 1) (divisor <<< (i + 1)) =
      bitsBE (e + i + 1) (divisor <<< i) ++ [false] := by
  rw [shiftLeft_succ]
  convert bitsBE_shiftLeft_one (e + i + 1) (divisor <<< i) using 1

/-- The repack machine prepares exactly the next trial-remainder step. -/
theorem physical_repack_trial_step (e i tail acc : Nat)
    (htail : tail < 2 ^ e) :
    DivisionRepackMachine.run (2 * (e + i + 2) + 3)
      (DivisionRepackMachine.cfg (some .dropAcc) none
        (bitsBE (e + i + 2) (step e (i + 1) (monicBits e tail) acc))
        (bitsBE (e + i + 2) ((monicBits e tail) <<< (i + 1))) []) =
    DivisionRepackMachine.cfg none none
      (bitsBE (e + i + 1) (step e (i + 1) (monicBits e tail) acc))
      (bitsBE (e + i + 1) ((monicBits e tail) <<< i)) [] := by
  have htop := monicBits_shifted_topBit e (i + 1) tail htail
  have hcancel := divisionStep_topBit_false e (i + 1)
    (monicBits e tail) acc htop
  have hcancel' :
      (step e (i + 1) (monicBits e tail) acc).testBit (e + i + 1) = false := by
    simpa [step, Nat.add_assoc] using hcancel
  rw [bitsBE_succ, hcancel']
  have hshift :
      bitsBE (e + i + 2) ((monicBits e tail) <<< (i + 1)) =
        bitsBE (e + i + 1) ((monicBits e tail) <<< i) ++ [false] := by
    simpa [Nat.add_assoc] using bitsBE_shifted_succ e i (monicBits e tail)
  rw [hshift]
  simpa [DivisionBitStep.bitsBE_length] using
    DivisionRepackMachine.run_repack
      (bitsBE (e + i + 1) (step e (i + 1) (monicBits e tail) acc))
      (bitsBE (e + i + 1) ((monicBits e tail) <<< i))

#print axioms bitsBE_shifted_succ
#print axioms physical_repack_trial_step

end CurrentAdditive.FieldMachineHelper.DivisionRepackBridge
