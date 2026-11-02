import EthInapproximability.CurrentPaper.SourceOriginalPacketLiftCost
import EthInapproximability.CurrentPaper.BitMachineComposition

/-! Charged composition of a lifted packet machine and a packet consumer. -/

namespace EthInapproximability.CurrentPaper.SourceOriginalPacketLiftCompose

theorem compose_packet_polynomial
    (A B : BitMachine.Machine) (input middle output : List Bool)
    (C N K : ℕ) (hN : 1 ≤ N)
    (ha : A.OutputsWithin input middle
      (C * (input.length + 3)^N))
    (hb : B.OutputsWithin middle output
      (K * (middle.length + 3)^8)) :
    (BitMachineComposition.composition A B).OutputsWithin input output
      ((C + 2 * (1 + C * A.pushBound) + 2 +
          K * (1 + C * A.pushBound)^8) *
        (input.length + 3)^(8*N)) := by
  let I := input.length
  let Q := (I + 3)^N
  let R := 1 + C * A.pushBound
  have hbase : I + 3 ≤ Q := by
    simpa only [pow_one] using
      (Nat.pow_le_pow_right (show 1 ≤ I + 3 by omega) hN)
  have hQ : 1 ≤ Q := by omega
  have hsize := BitMachine.output_length_bound A ha
  change middle.length ≤ I + (C * Q) * A.pushBound at hsize
  have hm : middle.length + 3 ≤ R * Q := by
    calc
      middle.length + 3 ≤ I + 3 + (C * Q) * A.pushBound := by omega
      _ ≤ Q + (C * Q) * A.pushBound := Nat.add_le_add_right hbase _
      _ = R * Q := by dsimp [R]; ring
  have hQ8 : Q ≤ Q^8 := by
    simpa only [pow_one] using
      (Nat.pow_le_pow_right hQ (show 1 ≤ 8 by omega))
  have hrun := BitMachineComposition.composition_outputsWithin A B ha hb
  apply BitMachine.outputsWithin_mono _ hrun
  change C*Q + 2*middle.length + 2 + K*(middle.length+3)^8 ≤
    (C + 2*R + 2 + K*R^8) * (I+3)^(8*N)
  have hm0 : middle.length ≤ R*Q := by omega
  have hpow := Nat.pow_le_pow_left hm 8
  have hstep : C*Q + 2*middle.length + 2 + K*(middle.length+3)^8 ≤
      (C+2*R+2)*Q + K*(R*Q)^8 := by
    have hh : 2 ≤ 2*Q := by omega
    nlinarith [Nat.mul_le_mul_left 2 hm0, Nat.mul_le_mul_left K hpow]
  calc
    C*Q + 2*middle.length + 2 + K*(middle.length+3)^8 ≤
        (C+2*R+2)*Q + K*(R*Q)^8 := hstep
    _ = (C+2*R+2)*Q + K*R^8*Q^8 := by rw [mul_pow]; ring
    _ ≤ (C+2*R+2)*Q^8 + K*R^8*Q^8 := by
      exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hQ8) _
    _ = (C+2*R+2+K*R^8)*Q^8 := by ring
    _ = (C+2*R+2+K*R^8)*(I+3)^(8*N) := by
      rw [show 8*N = N*8 by omega, pow_mul]

end EthInapproximability.CurrentPaper.SourceOriginalPacketLiftCompose
