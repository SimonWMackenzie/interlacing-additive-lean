import CurrentAdditive.SeedPairSplit
import EthInapproximability.CurrentPaper.SamplerMachineEnumeration
import CurrentAdditive.DotMachine

/-! The existing physical fixed-width counter uses the same least-first
binary words as the new Nat-bit finite-field printer. -/

namespace CurrentAdditive.FiniteFieldMachine.CounterNatBridge

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.SamplerMachineIncrement
open EthInapproximability.CurrentPaper.SamplerEnumeration
open CurrentAdditive.FiniteFieldMachine.DotMachine

theorem testBit_bitsValue (q : List Bool) (i : ℕ) :
    (EncodedCommunication.bitsValue q).testBit i = q[i]?.getD false := by
  induction q generalizing i with
  | nil => simp [EncodedCommunication.bitsValue]
  | cons b q ih =>
      cases i with
      | zero => simp [EncodedCommunication.bitsValue, Nat.testBit_bit_zero]
      | succ i => simpa [EncodedCommunication.bitsValue,
          Nat.testBit_bit_succ] using ih i

theorem natBits_bitsValue (q : List Bool) :
    DotMachine.natBits q.length (EncodedCommunication.bitsValue q) = q := by
  apply List.ext_getElem
  · simp [DotMachine.natBits]
  · intro i hi hj
    simp only [DotMachine.natBits, List.getElem_map, List.getElem_range]
    rw [testBit_bitsValue]
    simp only [List.getElem?_eq_getElem hj, Option.getD_some]

private theorem bitsValue_replicate_false (d : ℕ) :
    EncodedCommunication.bitsValue (List.replicate d false) = 0 := by
  induction d with
  | zero => rfl
  | succ d ih => simp [List.replicate_succ, EncodedCommunication.bitsValue, ih]

theorem counter_value_at (d k : ℕ) (hk : k < 2 ^ d) :
    EncodedCommunication.bitsValue
      ((increment^[k]) (List.replicate d false)) = k := by
  induction k with
  | zero => simpa using bitsValue_replicate_false d
  | succ k ih =>
      have hk' : k < 2 ^ d := by omega
      rw [Function.iterate_succ_apply', increment_value_mod,
        increment_iterate_length, ih hk', Nat.mod_eq_of_lt hk]

theorem bitsValue_append (u v : List Bool) :
    EncodedCommunication.bitsValue (u ++ v) =
      EncodedCommunication.bitsValue u +
        2 ^ u.length * EncodedCommunication.bitsValue v := by
  induction u with
  | nil => simp [EncodedCommunication.bitsValue]
  | cons b u ih =>
      simp only [List.cons_append, List.length_cons,
        EncodedCommunication.bitsValue, Nat.bit_val, pow_succ, ih]
      ring

theorem counter_pair_values (d : ℕ) (j : Fin ((2 ^ d) ^ 2)) :
    let q := (increment^[j.val]) (List.replicate (2 * d) false)
    EncodedCommunication.bitsValue (q.take d) = j.val % (2 ^ d) ∧
    EncodedCommunication.bitsValue (q.drop d) = j.val / (2 ^ d) := by
  intro q
  have hq : q.length = 2 * d := increment_iterate_length (2 * d) j.val
  have hj : j.val < 2 ^ (2 * d) := by
    rw [show 2 * d = d * 2 by omega, pow_mul]
    exact j.isLt
  have hv : EncodedCommunication.bitsValue q = j.val :=
    counter_value_at (2 * d) j.val hj
  have hsplit : q.take d ++ q.drop d = q := List.take_append_drop d q
  have hlowLen : (q.take d).length = d := by
    simp [List.length_take, hq]
    omega
  have hlow : EncodedCommunication.bitsValue (q.take d) < 2 ^ d := by
    simpa only [hlowLen] using bitsValue_lt (q.take d)
  have hvalue : j.val = EncodedCommunication.bitsValue (q.take d) +
      2 ^ d * EncodedCommunication.bitsValue (q.drop d) := by
    have h := bitsValue_append (q.take d) (q.drop d)
    rw [hsplit, hlowLen] at h
    exact hv.symm.trans h
  constructor
  · rw [hvalue]
    simp [Nat.add_mod, Nat.mod_eq_of_lt hlow]
  · rw [hvalue]
    simpa [Nat.add_mul_div_left, Nat.div_eq_of_lt hlow]

theorem counter_pair_natBits (d : ℕ) (j : Fin ((2 ^ d) ^ 2)) :
    let q := (increment^[j.val]) (List.replicate (2 * d) false)
    q = DotMachine.natBits d (j.val % 2 ^ d) ++
      DotMachine.natBits d (j.val / 2 ^ d) := by
  intro q
  have hq : q.length = 2 * d := increment_iterate_length (2 * d) j.val
  have hlenY : (q.take d).length = d := by
    simp [List.length_take, hq]
    omega
  have hlenX : (q.drop d).length = d := by
    simp [List.length_drop, hq]
    omega
  obtain ⟨hy, hx⟩ := counter_pair_values d j
  have hY : q.take d = DotMachine.natBits d (j.val % 2 ^ d) := by
    calc
      q.take d = DotMachine.natBits (q.take d).length
          (EncodedCommunication.bitsValue (q.take d)) :=
        (natBits_bitsValue (q.take d)).symm
      _ = DotMachine.natBits d (j.val % 2 ^ d) := by rw [hlenY, hy]
  have hX : q.drop d = DotMachine.natBits d (j.val / 2 ^ d) := by
    calc
      q.drop d = DotMachine.natBits (q.drop d).length
          (EncodedCommunication.bitsValue (q.drop d)) :=
        (natBits_bitsValue (q.drop d)).symm
      _ = DotMachine.natBits d (j.val / 2 ^ d) := by rw [hlenX, hx]
  rw [← List.take_append_drop d q, hY, hX]

#print axioms testBit_bitsValue
#print axioms counter_value_at
#print axioms counter_pair_values
#print axioms counter_pair_natBits

end CurrentAdditive.FiniteFieldMachine.CounterNatBridge
