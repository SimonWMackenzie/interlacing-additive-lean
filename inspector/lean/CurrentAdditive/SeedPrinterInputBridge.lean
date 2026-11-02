import CurrentAdditive.CounterNatBridge
import CurrentAdditive.StreamingBitMachine

/-! The physical pair counter's literal bits are the prepared seed/base
words expected by the one-seed streaming printer. -/

namespace CurrentAdditive.FiniteFieldMachine.SeedPrinterInputBridge

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.SamplerMachineIncrement
open CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge

def pairX (d : ℕ) (j : Fin ((2 ^ d) ^ 2)) : Fin (2 ^ d) :=
  ⟨j.val / (2 ^ d), by
    apply Nat.div_lt_of_lt_mul
    simpa only [pow_two] using j.isLt⟩

def pairY (d : ℕ) (j : Fin ((2 ^ d) ^ 2)) : Fin (2 ^ d) :=
  ⟨j.val % (2 ^ d), Nat.mod_lt _ (by positivity)⟩

theorem counter_pair_printer_bits (d : ℕ) (j : Fin ((2 ^ d) ^ 2)) :
    (increment^[j.val]) (List.replicate (2 * d) false) =
      SamplerMachine.encodeWord (xBits d (pairY d j)) ++
      SamplerMachine.encodeWord (xBits d (pairX d j)) := by
  rw [CounterNatBridge.counter_pair_natBits]
  simp only [StreamingBitMachine.encodeWord_xBits, pairX, pairY]

#print axioms counter_pair_printer_bits

end CurrentAdditive.FiniteFieldMachine.SeedPrinterInputBridge
