import EthInapproximability.CurrentPaper.SourceNormalizationPacketMachineCost
import EthInapproximability.CurrentPaper.SourceNormalizationBOutputBridge

/-! A finite machine for exact, original-size-bearing normalized graph packets. -/

namespace EthInapproximability.CurrentPaper.SourceNormalizationPacketMachine

open Turing BitMachineEncoding SourceNormalizationPacketMachineCore

noncomputable def machine : BitMachine.Machine :=
  ofFinite (.inr (0 : Fin 3)) (.inr (2 : Fin 3))
    (.inl (.scan 0)) (parserControl none) program

private theorem entry_eq_rawInit (packet : List Bool) :
    entry packet = rawInit (.inr (0 : Fin 3)) (.inl (.scan 0))
      (parserControl none) packet := by
  let S : Stack → List Bool := fun k => if k = .inr (0 : Fin 3) then packet else []
  have hs : ∀ k : BitMachineBankCodec.Stack 2,
      (BitMachineBankCodec.parserCfg (some (.scan 0)) none
        (fun _ => []) packet [] []).stk k = S (parserStack k) := by
    intro k
    cases k with
    | inl k => fin_cases k <;> simp [S, parserStack,
        BitMachineBankCodec.parserCfg, BitMachineBankCodec.contents]
    | inr k => fin_cases k <;> simp [S, parserStack,
        BitMachineBankCodec.parserCfg, BitMachineBankCodec.contents]
  have hb : BitMachineStackEmbedding.bank parserStack (fun _ => [])
      (BitMachineBankCodec.parserCfg (some (.scan 0)) none
        (fun _ => []) packet [] []).stk = S := by
    funext k
    by_cases hk : ∃ p : BitMachineBankCodec.Stack 2, parserStack p = k
    · obtain ⟨p,rfl⟩ := hk
      rw [BitMachineStackEmbedding.bank_at]
      exact hs p
    · rw [BitMachineStackEmbedding.bank_outside _ _ _ _ hk]
      have hne : k ≠ (.inr (0 : Fin 3) : Stack) := by
        intro he
        exact hk ⟨.inr 0, by simpa [parserStack] using he.symm⟩
      simp [S, hne]
  change (⟨some (.inl (.scan 0)), parserControl none,
      BitMachineStackEmbedding.bank parserStack (fun _ => [])
        (BitMachineBankCodec.parserCfg (some (.scan 0)) none
          (fun _ => []) packet [] []).stk⟩ : Config) =
    ⟨some (.inl (.scan 0)), parserControl none, S⟩
  rw [hb]

theorem outputs_canonical (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) :
    machine.OutputsWithin
      (SourceOriginalBranchPackets.packet originalN (EncodedGraph.encode g))
      (SourceOriginalBranchPackets.packet originalN
        (resultWord g hg originalN))
      (150000 * (UnaryBinaryEncoding.coefficient + 5) *
        ((SourceOriginalBranchPackets.packet originalN
          (EncodedGraph.encode g)).length + 3)^8) := by
  obtain ⟨t,ht,hl,hw⟩ :=
    SourceNormalizationPacketMachineCost.canonical_packet_polynomial_run g hg originalN
  exact outputsWithin_of_raw_run (.inr (0 : Fin 3)) (.inr (2 : Fin 3))
    (.inl (.scan 0)) (parserControl none) program
    (SourceOriginalBranchPackets.packet originalN (EncodedGraph.encode g))
    (SourceOriginalBranchPackets.packet originalN (resultWord g hg originalN))
    t _ ht (by rw [← entry_eq_rawInit]; exact hl)
    (by rw [← entry_eq_rawInit]; exact hw)

theorem outputs_B_output {k : ℕ} (B : EncodedETHSource.BOTReduction k)
    (f : EncodedCNF.Formula) (hf : f.Valid) (originalN : ℕ) :
    machine.OutputsWithin
      (SourceOriginalBranchPackets.packet originalN
        (EncodedGraph.encode (B.reduce f)))
      (SourceOriginalBranchPackets.packet originalN
        (EncodedGraph.encode (B.output f hf originalN)))
      (150000 * (UnaryBinaryEncoding.coefficient + 5) *
        ((SourceOriginalBranchPackets.packet originalN
          (EncodedGraph.encode (B.reduce f))).length + 3)^8) := by
  have h := outputs_canonical (B.reduce f) (B.valid f hf) originalN
  simpa only [resultWord,
    ← SourceNormalizationBOutputBridge.output_eq_serializeNormalized]
    using h

end EthInapproximability.CurrentPaper.SourceNormalizationPacketMachine
