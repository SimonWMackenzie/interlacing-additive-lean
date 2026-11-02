import CurrentAdditive.TrialCounterMachine
import CurrentAdditive.DivisionBitStep

/-! Exact bit orientation of the physical fixed-width trial counter. -/

namespace CurrentAdditive.FieldMachineHelper.CounterBitEncoding

open CurrentAdditive.FieldMachineHelper.TrialCounterMachine
open CurrentAdditive.FieldMachineHelper.DivisionBitStep (bitsBE)

private theorem bitsValue_cons (b : Bool) (rest : List Bool) :
    bitsValue (b :: rest) = Nat.bit b (bitsValue rest) := by
  cases b <;> simp [bitsValue, Nat.bit, Nat.add_comm]

theorem testBit_bitsValue (word : List Bool) (i : Nat) :
    (bitsValue word).testBit i = word[i]?.getD false := by
  induction word generalizing i with
  | nil => simp [bitsValue]
  | cons b rest ih =>
    rw [bitsValue_cons]
    cases i with
    | zero => simp
    | succ i => simpa [Nat.testBit_bit_succ] using ih i

theorem counterWord_eq_natBits (d k : Nat) (hk : k < 2 ^ d) :
    counterWord d k = (List.range d).map k.testBit := by
  apply List.ext_getElem
  · simp [counterWord_length]
  · intro i hi hj
    have hb := testBit_bitsValue (counterWord d k) i
    rw [counterWord_value_lt d k hk] at hb
    simp only [List.getElem?_eq_getElem hi, Option.getD_some] at hb
    simpa [List.getElem_map] using hb.symm

theorem counterWord_reverse_bitsBE (d k : Nat) (hk : k < 2 ^ d) :
    (counterWord d k).reverse = bitsBE d k := by
  rw [counterWord_eq_natBits d k hk]
  rfl

#print axioms counterWord_reverse_bitsBE

end CurrentAdditive.FieldMachineHelper.CounterBitEncoding
