import EthInapproximability.CurrentPaper.SourceOriginalPacketLiftCompose
import EthInapproximability.CurrentPaper.SourceNormalizationPacketMachine

/-! The cited BOT CNF-to-raw-graph machine, physically lifted to a packet,
followed by the checked ordered graph normalizer on the same original n. -/

namespace EthInapproximability.CurrentPaper.SourceBOTNormalizedPacketMachine

theorem exists_canonical_machine {k : ℕ}
    (B : EncodedETHSource.BOTReduction k) :
    ∃ (M : BitMachine.Machine) (C D : ℕ),
      ∀ (f : EncodedCNF.Formula) (hf : f.Valid) (originalN : ℕ),
        M.OutputsWithin
          (SourceOriginalBranchPackets.packet originalN (EncodedCNF.encode f))
          (SourceOriginalBranchPackets.packet originalN
            (EncodedGraph.encode (B.output f hf originalN)))
          (C * ((SourceOriginalBranchPackets.packet originalN
            (EncodedCNF.encode f)).length + 3) ^ D) := by
  obtain ⟨N,c,d,hN⟩ := B.polytime
  let A := SourceOriginalPacketLiftMachine.liftMachine N
  let P := SourceNormalizationPacketMachine.machine
  let C₁ := 10 * (c + 1) * (N.pushBound + 1)
  let K := 150000 * (UnaryBinaryEncoding.coefficient + 5)
  let R := 1 + C₁ * A.pushBound
  refine ⟨BitMachineComposition.composition A P,
    C₁ + 2*R + 2 + K*R^8, 8*(d+1), ?_⟩
  intro f hf originalN
  let input := SourceOriginalBranchPackets.packet originalN (EncodedCNF.encode f)
  let middle := SourceOriginalBranchPackets.packet originalN
    (EncodedGraph.encode (B.reduce f))
  let output := SourceOriginalBranchPackets.packet originalN
    (EncodedGraph.encode (B.output f hf originalN))
  have ha : A.OutputsWithin input middle
      (C₁ * (input.length + 3)^(d+1)) := by
    have h := SourceOriginalPacketLiftCost.outputs_polynomial_canonical
      N B.bitFunction c d originalN (EncodedCNF.encode f) hN
    rw [B.bitFunction_valid f hf] at h
    exact h
  have hb : P.OutputsWithin middle output
      (K * (middle.length + 3)^8) := by
    exact SourceNormalizationPacketMachine.outputs_B_output B f hf originalN
  have hc := SourceOriginalPacketLiftCompose.compose_packet_polynomial
    A P input middle output C₁ (d+1) K (by omega) ha hb
  simpa only [input, middle, output, C₁, K, R, A, P, Nat.add] using hc

noncomputable def machine {k : ℕ} (B : EncodedETHSource.BOTReduction k) :
    BitMachine.Machine := (exists_canonical_machine B).choose

theorem machine_outputs {k : ℕ} (B : EncodedETHSource.BOTReduction k) :
    ∃ C D : ℕ,
      ∀ (f : EncodedCNF.Formula) (hf : f.Valid) (originalN : ℕ),
        (machine B).OutputsWithin
          (SourceOriginalBranchPackets.packet originalN (EncodedCNF.encode f))
          (SourceOriginalBranchPackets.packet originalN
            (EncodedGraph.encode (B.output f hf originalN)))
          (C * ((SourceOriginalBranchPackets.packet originalN
            (EncodedCNF.encode f)).length + 3)^D) :=
  (exists_canonical_machine B).choose_spec

end EthInapproximability.CurrentPaper.SourceBOTNormalizedPacketMachine
