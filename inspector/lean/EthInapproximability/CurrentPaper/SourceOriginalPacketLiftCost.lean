import EthInapproximability.CurrentPaper.SourceOriginalPacketLiftMachine

/-! Polynomial physical clock for a canonical second-field packet lift. -/

namespace EthInapproximability.CurrentPaper.SourceOriginalPacketLiftCost

open SourceOriginalPacketLiftMachine

theorem output_packet_size (M : BitMachine.Machine) (n : ℕ)
    (word output : List Bool) (T : ℕ)
    (h : M.OutputsWithin word output T) :
    (SourceOriginalBranchPackets.packet n output).length ≤
      (SourceOriginalBranchPackets.packet n word).length +
        2 * T * M.pushBound := by
  have ho := BitMachine.output_length_bound M h
  rw [SourceOriginalBranchPackets.packet_length,
    SourceOriginalBranchPackets.packet_length]
  calc
    2 * (n + output.length) + 2 ≤
        2 * (n + word.length + T * M.pushBound) + 2 := by omega
    _ = 2 * (n + word.length) + 2 + 2 * T * M.pushBound := by ring

theorem outputs_charged (M : BitMachine.Machine) (n : ℕ)
    (word output : List Bool) (T : ℕ)
    (h : M.OutputsWithin word output T) :
    (liftMachine M).OutputsWithin
      (SourceOriginalBranchPackets.packet n word)
      (SourceOriginalBranchPackets.packet n output)
      (7 * ((SourceOriginalBranchPackets.packet n word).length + 2) +
        (1 + 4 * M.pushBound) * T) := by
  have hr := outputs_canonical M n word output T h
  apply BitMachine.outputsWithin_mono _ hr
  have hs := output_packet_size M n word output T h
  have he : 2 * T * M.pushBound = 2 * (T * M.pushBound) := by ring
  rw [he] at hs
  have he' : (1 + 4 * M.pushBound) * T =
      T + 4 * (T * M.pushBound) := by ring
  rw [he']
  omega

theorem outputs_polynomial_canonical (M : BitMachine.Machine)
    (F : List Bool → List Bool) (c d n : ℕ) (word : List Bool)
    (h : M.ComputesWithin F (fun q => c * (q + 1)^d)) :
    (liftMachine M).OutputsWithin
      (SourceOriginalBranchPackets.packet n word)
      (SourceOriginalBranchPackets.packet n (F word))
      (10 * (c + 1) * (M.pushBound + 1) *
        ((SourceOriginalBranchPackets.packet n word).length + 3)^(d+1)) := by
  let I := (SourceOriginalBranchPackets.packet n word).length
  let p := M.pushBound
  let b := I + 3
  let q := b^(d+1)
  have hword : word.length + 1 ≤ b := by
    have hp := SourceOriginalBranchPackets.packet_length n word
    dsimp [I,b]
    omega
  have hpow : (word.length + 1)^d ≤ q :=
    (Nat.pow_le_pow_left hword d).trans
      (Nat.pow_le_pow_right (by dsimp [b,I]; omega) (by omega))
  have hbase : I + 2 ≤ q := by
    have hp : b ≤ q := by
      simpa only [pow_one] using
        (Nat.pow_le_pow_right (by dsimp [b,I]; omega) (show 1 ≤ d+1 by omega))
    dsimp [b] at hp
    omega
  have htime : c * (word.length + 1)^d ≤ c * q :=
    Nat.mul_le_mul_left c hpow
  have hrun := outputs_charged M n word (F word)
    (c * (word.length + 1)^d) (h word)
  apply BitMachine.outputsWithin_mono _ hrun
  change 7 * (I + 2) + (1 + 4*p) * (c * (word.length + 1)^d) ≤
    10 * (c+1) * (p+1) * q
  have hterm : (1 + 4*p) * (c * (word.length + 1)^d) ≤
      (1 + 4*p) * (c*q) := Nat.mul_le_mul_left _ htime
  have hcoeff : 7 + (1+4*p)*c ≤ 10*(c+1)*(p+1) := by
    nlinarith [Nat.zero_le (c*p)]
  calc
    7 * (I + 2) + (1+4*p)*(c*(word.length+1)^d) ≤
        7*q + (1+4*p)*(c*q) := Nat.add_le_add
          (Nat.mul_le_mul_left 7 hbase) hterm
    _ = (7+(1+4*p)*c)*q := by ring
    _ ≤ (10*(c+1)*(p+1))*q := Nat.mul_le_mul_right q hcoeff
    _ = 10*(c+1)*(p+1)*q := by ring

end EthInapproximability.CurrentPaper.SourceOriginalPacketLiftCost
