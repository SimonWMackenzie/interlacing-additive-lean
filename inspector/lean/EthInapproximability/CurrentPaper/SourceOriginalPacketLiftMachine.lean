import EthInapproximability.CurrentPaper.SourceOriginalPacketLiftCore

/-! The generic second-field packet lift as a finite Boolean-stack machine. -/

namespace EthInapproximability.CurrentPaper.SourceOriginalPacketLiftMachine

open Turing BitMachineEncoding

variable (M : BitMachine.Machine)

noncomputable def liftMachine : BitMachine.Machine :=
  ofFinite (.inr (.inr (0 : Fin 3))) (.inr (.inr (2 : Fin 3)))
    (.inl (.scan 0)) (SourceOriginalPacketLiftCore.parserControl M none)
    (SourceOriginalPacketLiftCore.program M)

private theorem entry_eq_rawInit (packet : List Bool) :
    SourceOriginalPacketLiftCore.entry M packet =
      rawInit (.inr (.inr (0 : Fin 3))) (.inl (.scan 0))
        (SourceOriginalPacketLiftCore.parserControl M none) packet := by
  let S : SourceOriginalPacketLiftCore.Stack M → List Bool :=
    fun k => if k = .inr (.inr (0 : Fin 3)) then packet else []
  have hs : ∀ k : BitMachineBankCodec.Stack 2,
      (BitMachineBankCodec.parserCfg (some (.scan 0)) none
        (fun _ => []) packet [] []).stk k =
      S (SourceOriginalPacketLiftCore.parserStack M k) := by
    intro k
    cases k with
    | inl k => fin_cases k <;> simp [S, SourceOriginalPacketLiftCore.parserStack,
        BitMachineBankCodec.parserCfg, BitMachineBankCodec.contents]
    | inr k => fin_cases k <;> simp [S, SourceOriginalPacketLiftCore.parserStack,
        BitMachineBankCodec.parserCfg, BitMachineBankCodec.contents]
  have hb : BitMachineStackEmbedding.bank
      (SourceOriginalPacketLiftCore.parserStack M) (fun _ => [])
      (BitMachineBankCodec.parserCfg (some (.scan 0)) none
        (fun _ => []) packet [] []).stk = S := by
    funext k
    by_cases hk : ∃ p : BitMachineBankCodec.Stack 2,
        SourceOriginalPacketLiftCore.parserStack M p = k
    · obtain ⟨p,rfl⟩ := hk
      rw [BitMachineStackEmbedding.bank_at]
      exact hs p
    · rw [BitMachineStackEmbedding.bank_outside _ _ _ _ hk]
      have hne : k ≠
          (.inr (.inr (0 : Fin 3)) : SourceOriginalPacketLiftCore.Stack M) := by
        intro he
        exact hk ⟨.inr 0, by
          simpa [SourceOriginalPacketLiftCore.parserStack] using he.symm⟩
      simp [S, hne]
  change (⟨some (.inl (.scan 0)),
      SourceOriginalPacketLiftCore.parserControl M none,
      BitMachineStackEmbedding.bank
        (SourceOriginalPacketLiftCore.parserStack M) (fun _ => [])
        (BitMachineBankCodec.parserCfg (some (.scan 0)) none
          (fun _ => []) packet [] []).stk⟩ :
        SourceOriginalPacketLiftCore.Config M) =
    ⟨some (.inl (.scan 0)),
      SourceOriginalPacketLiftCore.parserControl M none, S⟩
  rw [hb]

theorem outputs_canonical (n : ℕ) (word output : List Bool) (T : ℕ)
    (h : M.OutputsWithin word output T) :
    (liftMachine M).OutputsWithin
      (SourceOriginalBranchPackets.packet n word)
      (SourceOriginalBranchPackets.packet n output)
      (5 * ((SourceOriginalBranchPackets.packet n word).length + 1) +
        T + 1 + 2 * (SourceOriginalBranchPackets.packet n output).length + 2) := by
  obtain ⟨t,ht,hl,hw⟩ :=
    SourceOriginalPacketLiftCore.canonical_packet_run M n word output T h
  exact outputsWithin_of_raw_run (.inr (.inr (0 : Fin 3)))
    (.inr (.inr (2 : Fin 3))) (.inl (.scan 0))
    (SourceOriginalPacketLiftCore.parserControl M none)
    (SourceOriginalPacketLiftCore.program M)
    (SourceOriginalBranchPackets.packet n word)
    (SourceOriginalBranchPackets.packet n output)
    t _ ht (by rw [← entry_eq_rawInit]; exact hl)
    (by rw [← entry_eq_rawInit]; exact hw)

end EthInapproximability.CurrentPaper.SourceOriginalPacketLiftMachine
