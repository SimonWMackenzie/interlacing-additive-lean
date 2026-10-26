import CurrentAdditive.DeterministicCodeDSerializedSize
import CurrentAdditive.OrderedAlphabetCodec
import Mathlib.Tactic

/-! Exact byte length of the actual ordered numeric alphabet used by Code D. -/

namespace CurrentAdditive.DeterministicOrderedAlphabetSize

open CurrentAdditive.OrderedAlphabetCodec
open CurrentAdditive.DeterministicCodeDSerializedSize
open Paper2 CurrentAdditive.ExecutableCodeSource

theorem numericEntry_bounds {Y : Type} [Fintype Y] [DecidableEq Y]
    (μ : PositiveRationalLaw Y) (table : AlphabetTable Y μ) (S : Nat)
    (hweights : ∀ e ∈ table.entries.toList,
      Nat.size e.2.num.natAbs ≤ S ∧ Nat.size e.2.den ≤ S)
    (e : Nat × ℚ) (he : e ∈ (numericEntries μ table).toList) :
    e.1.bits.length ≤ table.entries.size ∧
    Nat.size e.2.num.natAbs ≤ S ∧ Nat.size e.2.den ≤ S := by
  simp only [numericEntries, Array.toList_map] at he
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp he
  have hidx := encode_lt μ table old.1
  have hbits : (encode μ table old.1).bits.length ≤ table.entries.size := by
    simpa only [Nat.size_eq_bits_len] using
      (Nat.size_le.mpr (lt_trans hidx Nat.lt_two_pow_self))
  exact ⟨hbits, (hweights old hold).1, (hweights old hold).2⟩

theorem numericAlphabetBytes_length_le {Y : Type} [Fintype Y] [DecidableEq Y]
    (μ : PositiveRationalLaw Y) (table : AlphabetTable Y μ) (S : Nat)
    (hweights : ∀ e ∈ table.entries.toList,
      Nat.size e.2.num.natAbs ≤ S ∧ Nat.size e.2.den ≤ S) :
    (CodeDTargetV2.alphabetBytes (numericEntries μ table)).length ≤
      3 * table.entries.size *
        (2 * table.entries.size + 8 * S + 13) + 1 := by
  have h := alphabetBytes_length_le (numericEntries μ table)
    table.entries.size S
    (by intro e he; exact (numericEntry_bounds μ table S hweights e he).1)
    (by intro e he; exact (numericEntry_bounds μ table S hweights e he).2.1)
    (by intro e he; exact (numericEntry_bounds μ table S hweights e he).2.2)
  simpa only [numericEntries_size] using h

def totalWeightBits {Y : Type} [Fintype Y] [DecidableEq Y]
    (μ : PositiveRationalLaw Y) (table : AlphabetTable Y μ) : Nat :=
  (table.entries.toList.map fun e =>
    Nat.size e.2.num.natAbs + Nat.size e.2.den).sum

theorem numericEntries_mass {Y : Type} [Fintype Y] [DecidableEq Y]
    (μ : PositiveRationalLaw Y) (table : AlphabetTable Y μ) :
    SequentialCode.sourceMass (numericEntries μ table) = 1 := by
  simpa [SequentialCode.sourceMass, numericEntries,
    Array.toList_map, List.map_map, Function.comp_def] using table.normalized

theorem numericEntries_codes_lt {Y : Type} [Fintype Y] [DecidableEq Y]
    (μ : PositiveRationalLaw Y) (table : AlphabetTable Y μ) :
    ∀ e ∈ (numericEntries μ table).toList, e.1 < table.entries.size := by
  intro e he
  simp only [numericEntries, Array.toList_map] at he
  obtain ⟨old, _, rfl⟩ := List.mem_map.mp he
  exact encode_lt μ table old.1

theorem numericAlphabetBytes_concrete_length_le {Y : Type}
    [Fintype Y] [DecidableEq Y]
    (μ : PositiveRationalLaw Y) (table : AlphabetTable Y μ) :
    (CodeDTargetV2.alphabetBytes (numericEntries μ table)).length ≤
      3 * table.entries.size *
        (2 * table.entries.size + 8 * totalWeightBits μ table + 13) + 1 := by
  apply numericAlphabetBytes_length_le
  intro e he
  have hmem : Nat.size e.2.num.natAbs + Nat.size e.2.den ∈
      (table.entries.toList.map fun x =>
        Nat.size x.2.num.natAbs + Nat.size x.2.den) :=
    List.mem_map.mpr ⟨e, he, rfl⟩
  have hsum := List.le_sum_of_mem hmem
  dsimp [totalWeightBits]
  omega

#print axioms numericAlphabetBytes_length_le
#print axioms numericAlphabetBytes_concrete_length_le
#print axioms numericEntries_mass

end CurrentAdditive.DeterministicOrderedAlphabetSize
