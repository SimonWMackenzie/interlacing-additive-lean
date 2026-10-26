import CurrentAdditive.TrialSearchControllerMachine
import CurrentAdditive.CounterBitEncoding

/-!
Numeric interpretation of the outer controller's physical binary counters.
These lemmas identify exactly when its carry means the last candidate or
divisor tail of a fixed width has been visited.
-/

namespace CurrentAdditive.FieldMachineHelper.TrialSearchControllerBridge

open CurrentAdditive.FieldMachineHelper.TrialCounterMachine
open CurrentAdditive.FieldMachineHelper.CounterBitEncoding
open CurrentAdditive.FieldMachineHelper.TrialSearchControllerMachine

theorem increment_counter_value (width tail : Nat) (htail : tail < 2 ^ width) :
    bitsValue (incrementAux true (counterWord width tail)).2 +
      (if (incrementAux true (counterWord width tail)).1
        then 2 ^ width else 0) = tail + 1 := by
  have h := incrementAux_value true (counterWord width tail)
  rw [counterWord_length, counterWord_value_lt width tail htail] at h
  simpa using h

theorem increment_counter_carry_nonlast (width tail : Nat)
    (htail : tail + 1 < 2 ^ width) :
    (incrementAux true (counterWord width tail)).1 = false := by
  have hk : tail < 2 ^ width := by omega
  have h := increment_counter_value width tail hk
  cases hc : (incrementAux true (counterWord width tail)).1 <;>
    simp [hc] at h ⊢; omega

theorem increment_counter_carry_last (width tail : Nat)
    (htail : tail + 1 = 2 ^ width) :
    (incrementAux true (counterWord width tail)).1 = true := by
  have hk : tail < 2 ^ width := by omega
  have h := increment_counter_value width tail hk
  have hbound := bitsValue_lt_pow
    (incrementAux true (counterWord width tail)).2
  have hlen : (incrementAux true (counterWord width tail)).2.length = width := by
    simpa [counterWord] using counterWord_length width (tail + 1)
  rw [hlen] at hbound
  cases hc : (incrementAux true (counterWord width tail)).1 <;>
    simp [hc] at h ⊢; omega

theorem counterWord_increment (width tail : Nat) :
    (incrementAux true (counterWord width tail)).2 =
      counterWord width (tail + 1) := by
  rfl

theorem counterWord_value_wrap_last (width tail : Nat)
    (htail : tail + 1 = 2 ^ width) :
    bitsValue (incrementAux true (counterWord width tail)).2 = 0 := by
  have hk : tail < 2 ^ width := by omega
  have h := increment_counter_value width tail hk
  rw [increment_counter_carry_last width tail htail] at h
  simp at h
  omega

#print axioms increment_counter_carry_nonlast
#print axioms increment_counter_carry_last

end CurrentAdditive.FieldMachineHelper.TrialSearchControllerBridge
