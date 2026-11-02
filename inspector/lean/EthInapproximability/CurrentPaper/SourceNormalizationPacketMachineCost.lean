import EthInapproximability.CurrentPaper.SourceNormalizationPacketMachineCore

/-! The canonical two-bank packet clock is polynomial in its physical input length. -/

namespace EthInapproximability.CurrentPaper.SourceNormalizationPacketMachineCost

open SourceNormalizationPacketMachineCore

private theorem resultWord_eq_numeric (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) :
    resultWord g hg originalN = EncodedGraph.encode
      (SourceNormalizationMachineGraphOutput.numeric g originalN) := by
  have h := SourceNormalizationMachineComplete.final_abstract_output g hg originalN
  rw [SourceNormalizationMachineGraphOutput.final_output] at h
  exact h.symm

private theorem output_length_le_finalizer (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) :
    (resultWord g hg originalN).length ≤
      SourceNormalizationMachineGraphOutput.finalizerTime g originalN := by
  rw [resultWord_eq_numeric g hg originalN]
  simp only [EncodedGraph.encode, List.length_append, EncodedGraph.unary,
    List.length_replicate, List.length_cons, List.length_nil]
  rw [EncodedCommunication.natField, EncodedCommunication.field_length]
  simp only [SourceNormalizationMachineGraphOutput.finalizerTime]
  omega

private theorem finalizer_le_total (g : EncodedGraph.Graph) (originalN : ℕ) :
    SourceNormalizationMachineGraphOutput.finalizerTime g originalN ≤
      SourceNormalizationMachineGraphOutput.totalBound g originalN := by
  unfold SourceNormalizationMachineGraphOutput.totalBound
  omega

theorem output_packet_length_bound (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) :
    (SourceOriginalBranchPackets.packet originalN
      (resultWord g hg originalN)).length ≤
    2 * (originalN +
      10000 * (UnaryBinaryEncoding.coefficient + 5) *
        ((EncodedGraph.encode g).length + originalN + 4)^8) + 2 := by
  rw [SourceOriginalBranchPackets.packet_length]
  have h := (output_length_le_finalizer g hg originalN).trans
    ((finalizer_le_total g originalN).trans
      (SourceNormalizationMachineGraphCost.totalBound_polynomial g hg originalN))
  dsimp [SourceNormalizationMachineGraphCost.inputSize] at h
  have h' : (resultWord g hg originalN).length ≤
      10000 * (UnaryBinaryEncoding.coefficient + 5) *
        ((EncodedGraph.encode g).length + originalN + 4)^8 := by
    simpa only [show (3 : ℕ) + 1 = 4 by omega, Nat.add_assoc] using h
  omega

theorem canonical_packet_polynomial_run (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) :
    ∃ t ≤ 150000 * (UnaryBinaryEncoding.coefficient + 5) *
      ((SourceOriginalBranchPackets.packet originalN
        (EncodedGraph.encode g)).length + 3)^8,
      (run t (entry (SourceOriginalBranchPackets.packet originalN
        (EncodedGraph.encode g)))).l = none ∧
      (run t (entry (SourceOriginalBranchPackets.packet originalN
        (EncodedGraph.encode g)))).stk (.inr (2 : Fin 3)) =
        SourceOriginalBranchPackets.packet originalN (resultWord g hg originalN) := by
  let I := (SourceOriginalBranchPackets.packet originalN
    (EncodedGraph.encode g)).length
  let D := (EncodedGraph.encode g).length + originalN + 4
  let K := UnaryBinaryEncoding.coefficient + 5
  let P := 10000 * K * (I + 3)^8
  have hlen : I = 2 * (originalN + (EncodedGraph.encode g).length) + 2 := by
    exact SourceOriginalBranchPackets.packet_length originalN (EncodedGraph.encode g)
  have hn : originalN ≤ I := by omega
  have hD : D ≤ I + 3 := by omega
  have hpoly : 10000 * K * D^8 ≤ P := by
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hD 8)
  have hout := output_packet_length_bound g hg originalN
  change (SourceOriginalBranchPackets.packet originalN
    (resultWord g hg originalN)).length ≤ 2 * (originalN + 10000*K*D^8) + 2 at hout
  obtain ⟨t,ht,hl,hw⟩ := canonical_packet_run g hg originalN
  have hclock : t ≤ 5 * (I + 1) + 10000 * K * D^8 +
      2 * (SourceOriginalBranchPackets.packet originalN
        (resultWord g hg originalN)).length + 2 := ht
  have hbig : I + 3 ≤ (I + 3)^8 := by
    calc
      I + 3 = (I + 3) * 1 := by omega
      _ ≤ (I + 3) * (I + 3)^7 := by
        have hb : 1 ≤ (I + 3)^7 := by
          have hp : 0 < (I + 3)^7 := pow_pos (by omega) 7
          omega
        exact Nat.mul_le_mul_left _ hb
      _ = (I + 3)^8 := by ring
  have hK : 5 ≤ K := by dsimp [K]; omega
  have hP : I + 3 ≤ P := by
    dsimp [P]
    have hp := Nat.mul_le_mul_left (10000 * K) hbig
    nlinarith
  refine ⟨t, ?_, hl, hw⟩
  have hout' : (SourceOriginalBranchPackets.packet originalN
      (resultWord g hg originalN)).length ≤ 2 * (originalN + P) + 2 := by
    omega
  have hbound : t ≤ 5*(I+1) + P + 2*(2*(originalN+P)+2)+2 := by
    calc
      t ≤ 5*(I+1) + 10000*K*D^8 +
          2*(SourceOriginalBranchPackets.packet originalN
            (resultWord g hg originalN)).length + 2 := hclock
      _ ≤ 5*(I+1) + P + 2*(2*(originalN+P)+2)+2 := by
        gcongr
  have hlinear : t ≤ 15 * P := by omega
  simpa only [P, ← mul_assoc, show (15 : ℕ) * 10000 = 150000 by norm_num]
    using hlinear

end EthInapproximability.CurrentPaper.SourceNormalizationPacketMachineCost
