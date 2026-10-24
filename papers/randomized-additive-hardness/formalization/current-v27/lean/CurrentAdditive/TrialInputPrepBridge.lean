import CurrentAdditive.TrialInputPrepMachine
import CurrentAdditive.DivisionRepackBridge
import CurrentAdditive.TrialDividerTotal
import CurrentAdditive.MonicBits

/-!
The literal preparation machine writes exactly the aligned high-first words
and unary iteration count expected by the physical long-divider. The two
machines are still separate programs; this bridge identifies their data.
-/

namespace CurrentAdditive.FieldMachineHelper.TrialInputPrepBridge

open CurrentAdditive.FieldMachineHelper.TrialInputPrepMachine
open CurrentAdditive.FieldMachineHelper.TrialCounterMachine (counterWord counterWord_length)
open CurrentAdditive.FieldMachineHelper.CounterBitEncoding (counterWord_reverse_bitsBE)
open CurrentAdditive.FieldMachineHelper.DivisionBitStep (bitsBE bitsBE_succ)
open CurrentAdditive.FieldMachineHelper.DivisionRepackBridge (bitsBE_shiftLeft_one)
open CurrentAdditive.FieldMachineHelper.TrialDividerTotal (divisorWord)
open CurrentAdditive.FiniteFieldConstructor.TrialSearch (monicBits)
open CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge (monicBits_topBit)

theorem bitsBE_monic (width tail : Nat) (htail : tail < 2 ^ width) :
    bitsBE (width + 1) (monicBits width tail) =
      true :: bitsBE width tail := by
  rw [bitsBE_succ, monicBits_topBit width tail htail]
  congr 1
  unfold bitsBE
  congr 1
  apply List.map_congr_left
  intro j hj
  exact Nat.testBit_two_pow_add_gt (List.mem_range.mp hj) tail

theorem bitsBE_shiftLeft_replicate (width value shift : Nat) :
    bitsBE (width + shift) (value <<< shift) =
      bitsBE width value ++ List.replicate shift false := by
  induction shift with
  | zero => simp
  | succ shift ih =>
    have hshift : value <<< (shift + 1) = (value <<< shift) <<< 1 := by
      simp [Nat.shiftLeft_eq, pow_succ, Nat.mul_assoc]
    calc
      bitsBE (width + (shift + 1)) (value <<< (shift + 1)) =
          bitsBE ((width + shift) + 1) ((value <<< shift) <<< 1) := by
        rw [hshift]
        congr 1
      _ = bitsBE (width + shift) (value <<< shift) ++ [false] :=
        bitsBE_shiftLeft_one _ _
      _ = bitsBE width value ++ List.replicate (shift + 1) false := by
        rw [ih, List.replicate_succ']
        simp [List.append_assoc]

theorem bitsBE_monic_shifted (e tail shift : Nat)
    (htail : tail < 2 ^ e) :
    bitsBE (e + shift + 1) ((monicBits e tail) <<< shift) =
      true :: bitsBE e tail ++ List.replicate shift false := by
  have h := bitsBE_shiftLeft_replicate (e + 1) (monicBits e tail) shift
  rw [bitsBE_monic e tail htail] at h
  have hw : e + 1 + shift = e + shift + 1 := by omega
  rw [hw] at h
  simpa [List.cons_append] using h

/-- All counter and shift-source words are restored after physical prep. -/
theorem run_prepare_trial_input
    (d e candidateTail divisorTail : Nat)
    (he : e ≤ d) (hc : candidateTail < 2 ^ d)
    (hv : divisorTail < 2 ^ e) :
    TrialInputPrepMachine.run (4 * d + 6)
      (TrialInputPrepMachine.cfg (some .shiftScan) none
        (counterWord d candidateTail)
        (counterWord e divisorTail)
        (List.replicate (d - e) true) [] [] [] []) =
    TrialInputPrepMachine.cfg none none
      (counterWord d candidateTail)
      (counterWord e divisorTail)
      (List.replicate (d - e) true)
      (bitsBE (d + 1) (monicBits d candidateTail))
      (divisorWord e divisorTail (d - e + 1))
      (List.replicate (d - e + 1) true) [] := by
  have hw : e + (d - e) + 1 = d + 1 := by omega
  have hcword := counterWord_reverse_bitsBE d candidateTail hc
  have hvword := counterWord_reverse_bitsBE e divisorTail hv
  have hclock : 2 * ((List.replicate (d - e) true).length +
      (counterWord d candidateTail).length +
      (counterWord e divisorTail).length) + 6 = 4 * d + 6 := by
    simp [counterWord_length]
    omega
  have h := run_prepare (counterWord d candidateTail)
    (counterWord e divisorTail) (List.replicate (d - e) true)
  rw [hclock] at h
  rw [hcword, hvword] at h
  rw [← bitsBE_monic d candidateTail hc] at h
  have hdiv : true :: bitsBE e divisorTail ++ List.replicate (d - e) false =
      divisorWord e divisorTail (d - e + 1) := by
    change true :: bitsBE e divisorTail ++ List.replicate (d - e) false =
      bitsBE (e + (d - e) + 1)
        ((monicBits e divisorTail) <<< (d - e))
    exact (bitsBE_monic_shifted e divisorTail (d - e) hv).symm
  simpa [hdiv, List.replicate_succ, List.cons_append]
    using h

#print axioms run_prepare_trial_input

end CurrentAdditive.FieldMachineHelper.TrialInputPrepBridge
