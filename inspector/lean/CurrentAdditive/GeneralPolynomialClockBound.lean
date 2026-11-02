import CurrentAdditive.GeneralPolynomialClock
import Mathlib.Tactic

namespace CurrentAdditive.GeneralPolynomialClock

open EthInapproximability.CurrentPaper

set_option maxHeartbeats 2000000

def exponent (degree : ℕ) : ℕ := degree + 2

def rawCoefficient (degree : ℕ) : ℕ :=
  (degree+2) * (3*2^(degree+2) + 5*2^(degree+1) + 18) +
    2*2^(degree+1) + degree + 100

theorem rawTime_le (degree : ℕ) (bits : List Bool) :
    GeneralPolynomialFuelPrefix.rawTime (degree := degree) bits ≤
      rawCoefficient degree * (bits.length+1)^(exponent degree) := by
  let n := bits.length
  let q := n+1
  let b := n+2
  let s := degree+1
  let k := degree+2
  have hq : 0 < q := by omega
  have hk : 1 ≤ k := by omega
  have hks : k = s+1 := by omega
  have hqk : q ≤ q^k := by
    simpa only [pow_one] using Nat.pow_le_pow_right hq hk
  have hone : 1 ≤ q^k := by omega
  have hb : b ≤ 2*q := by omega
  have hbq : b ≤ 2*q^k := by omega
  have hqs : q^s ≤ q^k := Nat.pow_le_pow_right hq (by omega)
  have hbs : b^s ≤ 2^s*q^k := by
    calc
      b^s ≤ (2*q)^s := Nat.pow_le_pow_left hb s
      _ = 2^s*q^s := by rw [mul_pow]
      _ ≤ 2^s*q^k := Nat.mul_le_mul_left _ hqs
  have hbk : b^k ≤ 2^k*q^k := by
    calc
      b^k ≤ (2*q)^k := Nat.pow_le_pow_left hb k
      _ = 2^k*q^k := by rw [mul_pow]
  have hpower := MatrixWeightedPower.powerBound_polynomial b s
  have hpower' : MatrixWeightedPower.powerBound b s ≤
      (s+1)*(3*b^k+3*b+5*b^s+12) := by
    calc
      MatrixWeightedPower.powerBound b s ≤
        (s+1)*(3*(b^s+1)*b+5*(b^s+1)+7) := hpower
      _ = (s+1)*(3*b^k+3*b+5*b^s+12) := by
        rw [hks, pow_succ]
        ring
  have hpower'' : MatrixWeightedPower.powerBound b s ≤
      (s+1)*(3*2^k+5*2^s+18)*q^k := by
    calc
      MatrixWeightedPower.powerBound b s ≤
        (s+1)*(3*b^k+3*b+5*b^s+12) := hpower'
      _ ≤ (s+1)*(3*(2^k*q^k)+3*(2*q^k)+5*(2^s*q^k)+12*q^k) := by
        gcongr
        exact Nat.mul_le_mul_left 12 hone
      _ = (s+1)*(3*2^k+5*2^s+18)*q^k := by ring
  have hn : n ≤ q^k := by omega
  have hd : degree ≤ degree*q^k := by
    simpa using Nat.mul_le_mul_left degree hone
  have htail : 5*n+degree+13 ≤ (degree+100)*q^k := by
    calc
      5*n+degree+13 ≤ 5*q^k+degree*q^k+13 := by omega
      _ ≤ 5*q^k+degree*q^k+95*q^k := by omega
      _ = (degree+100)*q^k := by ring
  change (3*n+4)+(degree+4)+MatrixWeightedPower.powerBound b s+
    (2*n+2*b^s+5) ≤ rawCoefficient degree*q^k
  calc
    _ = MatrixWeightedPower.powerBound b s + 2*b^s +
          (5*n+degree+13) := by omega
    _ ≤ (s+1)*(3*2^k+5*2^s+18)*q^k +
          2*(2^s*q^k) + (degree+100)*q^k := by
      gcongr
    _ = rawCoefficient degree*q^k := by
      simp only [rawCoefficient, s, k]
      ring

def packedCoefficient (degree : ℕ) : ℕ := 2^(degree+1)+3

theorem packed_length_le (degree : ℕ) (bits : List Bool) :
    (packed degree bits).length+1 ≤
      packedCoefficient degree * (bits.length+1)^(exponent degree) := by
  let n := bits.length
  let q := n+1
  let b := n+2
  let s := degree+1
  let k := degree+2
  have hq : 0 < q := by omega
  have hqk : q ≤ q^k := by
    simpa only [pow_one] using Nat.pow_le_pow_right hq (by omega : 1 ≤ k)
  have hqs : q^s ≤ q^k := Nat.pow_le_pow_right hq (by omega)
  have hb : b ≤ 2*q := by omega
  have hbs : b^s ≤ 2^s*q^k := by
    calc
      b^s ≤ (2*q)^s := Nat.pow_le_pow_left hb s
      _ = 2^s*q^s := by rw [mul_pow]
      _ ≤ 2^s*q^k := Nat.mul_le_mul_left _ hqs
  have hlen : (packed degree bits).length+1 = b^s+n+2 := by
    simp [packed, BoundedBitMachine.packed,
      GeneralPolynomialFuelPrefix.clockLength,
      GeneralPolynomialFuelPrefix.baseLength, b, s, n]
    omega
  rw [hlen]
  change b^s+n+2 ≤ packedCoefficient degree*q^k
  have hone : 1 ≤ q^k := by omega
  have htail : n+2 ≤ 3*q^k := by omega
  calc
    b^s+n+2 ≤ 2^s*q^k+3*q^k := by omega
    _ = packedCoefficient degree*q^k := by
      simp only [packedCoefficient, s]
      ring

noncomputable def timeCoefficient (degree : ℕ) (M : BitMachine.Machine) : ℕ :=
  rawCoefficient degree +
    (2+ClockedPackedWrapper.clockCoefficient M)*packedCoefficient degree

theorem time_le (degree : ℕ) (M : BitMachine.Machine)
    (bits : List Bool) :
    time degree M bits ≤
      timeCoefficient degree M * (bits.length+1)^(exponent degree) := by
  let q := (bits.length+1)^(exponent degree)
  have hr := rawTime_le degree bits
  have hp := packed_length_le degree bits
  change GeneralPolynomialFuelPrefix.rawTime (degree := degree) bits ≤
    rawCoefficient degree*q at hr
  change (packed degree bits).length+1 ≤ packedCoefficient degree*q at hp
  have htw : 2*(packed degree bits).length+2 ≤
      2*packedCoefficient degree*q := by
    calc
      2*(packed degree bits).length+2 =
          2*((packed degree bits).length+1) := by omega
      _ ≤ 2*(packedCoefficient degree*q) := Nat.mul_le_mul_left 2 hp
      _ = 2*packedCoefficient degree*q := by ring
  have hsim := Nat.mul_le_mul_left
    (ClockedPackedWrapper.clockCoefficient M) hp
  unfold time timeCoefficient
  calc
    _ ≤ rawCoefficient degree*q +
        2*packedCoefficient degree*q +
        ClockedPackedWrapper.clockCoefficient M*(packedCoefficient degree*q) := by
      omega
    _ = (rawCoefficient degree +
        (2+ClockedPackedWrapper.clockCoefficient M)*packedCoefficient degree)*q := by ring

theorem polytime (degree : ℕ) (M : BitMachine.Machine) :
    BitMachine.Polytime (result degree M) := by
  refine ⟨machine degree M, timeCoefficient degree M,
    exponent degree, ?_⟩
  intro bits
  exact BitMachine.outputsWithin_mono (machine degree M)
    (outputs_all degree M bits) (time_le degree M bits)

#print axioms rawTime_le
#print axioms polytime

end CurrentAdditive.GeneralPolynomialClock
