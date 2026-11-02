import CurrentAdditive.PhysicalPolynomialClock
import CurrentAdditive.PolynomialFuelPrefixBound

/-! A fixed degree-thirteen bound for the ordinary-input clock wrapper. -/
namespace CurrentAdditive.PhysicalPolynomialClock

set_option maxHeartbeats 2000000

open EthInapproximability.CurrentPaper

theorem clockLength_le (bits : List Bool) :
    PolynomialFuelPrefix.clockLength bits ≤
      4096 * (bits.length+1)^13 := by
  let n := bits.length
  let q := n+1
  have hq : 0 < q := by omega
  have hb : n+2 ≤ 2*q := by omega
  have hpow : (n+2)^12 ≤ (2*q)^12 := Nat.pow_le_pow_left hb 12
  have hqpow : q^12 ≤ q^13 :=
    Nat.pow_le_pow_right hq (show 12 ≤ 13 by omega)
  calc
    PolynomialFuelPrefix.clockLength bits = (n+2)^12 := rfl
    _ ≤ (2*q)^12 := hpow
    _ = 4096*q^12 := by ring
    _ ≤ 4096*q^13 := Nat.mul_le_mul_left 4096 hqpow

theorem packed_length_le (bits : List Bool) :
    (packed bits).length + 1 ≤ 5000 * (bits.length+1)^13 := by
  let q := bits.length+1
  change (packed bits).length + 1 ≤ 5000*q^13
  have hq : 0 < q := by omega
  have hq1 : q ≤ q^13 := by
    simpa only [pow_one] using
      (Nat.pow_le_pow_right hq (show 1 ≤ 13 by omega))
  have hone : 1 ≤ q^13 := by omega
  have hclock := clockLength_le bits
  change PolynomialFuelPrefix.clockLength bits ≤ 4096*q^13 at hclock
  have hlen : (packed bits).length + 1 =
      PolynomialFuelPrefix.clockLength bits + bits.length + 2 := by
    simp only [packed, BoundedBitMachine.packed, List.length_append,
      List.length_replicate, List.length_cons]
    omega
  rw [hlen]
  omega

private theorem time_le_aux (bits : List Bool) (c : ℕ) :
    PolynomialFuelPrefix.rawTime bits + 2*(packed bits).length+2 +
      c*((packed bits).length+1) ≤
        (1010000 + 5000*c)*(bits.length+1)^13 := by
  let q := bits.length+1
  have hr := PolynomialFuelPrefixBound.rawTime_le bits
  have hlen := packed_length_le bits
  change PolynomialFuelPrefix.rawTime bits ≤ 1000000*q^13 at hr
  change (packed bits).length+1 ≤ 5000*q^13 at hlen
  have htransfer : 2*(packed bits).length+2 ≤ 10000*q^13 := by omega
  have hsim : c*((packed bits).length+1) ≤ c*(5000*q^13) :=
    Nat.mul_le_mul_left c hlen
  calc
    PolynomialFuelPrefix.rawTime bits + 2*(packed bits).length+2 +
        c*((packed bits).length+1) =
        PolynomialFuelPrefix.rawTime bits + (2*(packed bits).length+2) +
          c*((packed bits).length+1) := by omega
    _ ≤
        1000000*q^13 + 10000*q^13 + c*(5000*q^13) := by
      exact Nat.add_le_add (Nat.add_le_add hr htransfer) hsim
    _ = (1010000+5000*c)*q^13 := by ring

theorem time_le (M : BitMachine.Machine) (bits : List Bool) :
    time M bits ≤
      (1010000 + 5000 * ClockedPackedWrapper.clockCoefficient M) *
        (bits.length+1)^13 := by
  unfold time
  exact time_le_aux bits (ClockedPackedWrapper.clockCoefficient M)

/-- A fixed source machine with its literal polynomial clock defines a
polynomial-time total function on ordinary, unframed inputs. -/
theorem polytime (M : BitMachine.Machine) :
    BitMachine.Polytime (result M) := by
  refine ⟨machine M,
    1010000 + 5000 * ClockedPackedWrapper.clockCoefficient M, 13, ?_⟩
  intro bits
  exact BitMachine.outputsWithin_mono (machine M)
    (outputs_all M bits) (time_le M bits)

#print axioms polytime

end CurrentAdditive.PhysicalPolynomialClock
