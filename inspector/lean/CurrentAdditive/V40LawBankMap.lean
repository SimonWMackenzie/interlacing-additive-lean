import CurrentAdditive.V40LawBankCore
import EthInapproximability.CurrentPaper.SourceOriginalPacketLiftMachine
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

/-! The generic second-field packet lift as a finite Boolean-stack machine. -/

namespace CurrentAdditive.V40LawBankMap

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
attribute [local simp] SourceOriginalPacketLiftCore.parserStack

variable (M : BitMachine.Machine)

noncomputable def liftMachine : BitMachine.Machine :=
  SourceOriginalPacketLiftMachine.liftMachine M

private theorem entry_eq_rawInit (packet : List Bool) :
    CurrentAdditive.V40LawBankCore.entry M packet =
      rawInit (.inr (.inr (0 : Fin 3))) (.inl (.scan 0))
        (CurrentAdditive.V40LawBankCore.parserControl M none) packet := by
  let S : CurrentAdditive.V40LawBankCore.Stack M → List Bool :=
    fun k => if k = .inr (.inr (0 : Fin 3)) then packet else []
  have hs : ∀ k : BitMachineBankCodec.Stack 2,
      (BitMachineBankCodec.parserCfg (some (.scan 0)) none
        (fun _ => []) packet [] []).stk k =
      S (CurrentAdditive.V40LawBankCore.parserStack M k) := by
    intro k
    cases k with
    | inl k => fin_cases k <;> simp [S, CurrentAdditive.V40LawBankCore.parserStack,
        BitMachineBankCodec.parserCfg, BitMachineBankCodec.contents]
    | inr k => fin_cases k <;> simp [S, CurrentAdditive.V40LawBankCore.parserStack,
        BitMachineBankCodec.parserCfg, BitMachineBankCodec.contents]
  have hb : BitMachineStackEmbedding.bank
      (CurrentAdditive.V40LawBankCore.parserStack M) (fun _ => [])
      (BitMachineBankCodec.parserCfg (some (.scan 0)) none
        (fun _ => []) packet [] []).stk = S := by
    funext k
    by_cases hk : ∃ p : BitMachineBankCodec.Stack 2,
        CurrentAdditive.V40LawBankCore.parserStack M p = k
    · obtain ⟨p,rfl⟩ := hk
      rw [BitMachineStackEmbedding.bank_at]
      exact hs p
    · rw [BitMachineStackEmbedding.bank_outside _ _ _ _ hk]
      have hne : k ≠
          (.inr (.inr (0 : Fin 3)) : CurrentAdditive.V40LawBankCore.Stack M) := by
        intro he
        exact hk ⟨.inr 0, by
          simpa [CurrentAdditive.V40LawBankCore.parserStack] using he.symm⟩
      simp [S, hne]
  change (⟨some (.inl (.scan 0)),
      CurrentAdditive.V40LawBankCore.parserControl M none,
      BitMachineStackEmbedding.bank
        (CurrentAdditive.V40LawBankCore.parserStack M) (fun _ => [])
        (BitMachineBankCodec.parserCfg (some (.scan 0)) none
          (fun _ => []) packet [] []).stk⟩ :
        CurrentAdditive.V40LawBankCore.Config M) =
    ⟨some (.inl (.scan 0)),
      CurrentAdditive.V40LawBankCore.parserControl M none, S⟩
  rw [hb]

theorem outputs_canonical (header : List Bool) (word output : List Bool) (T : ℕ)
    (h : M.OutputsWithin word output T) :
    (liftMachine M).OutputsWithin
      (CurrentAdditive.V40LawPacket.packet header word)
      (CurrentAdditive.V40LawPacket.packet header output)
      (5 * ((CurrentAdditive.V40LawPacket.packet header word).length + 1) +
        T + 1 + 2 * (CurrentAdditive.V40LawPacket.packet header output).length + 2) := by
  obtain ⟨t,ht,hl,hw⟩ :=
    CurrentAdditive.V40LawBankCore.canonical_packet_run M header word output T h
  exact outputsWithin_of_raw_run (.inr (.inr (0 : Fin 3)))
    (.inr (.inr (2 : Fin 3))) (.inl (.scan 0))
    (CurrentAdditive.V40LawBankCore.parserControl M none)
    (CurrentAdditive.V40LawBankCore.program M)
    (CurrentAdditive.V40LawPacket.packet header word)
    (CurrentAdditive.V40LawPacket.packet header output)
    t _ ht (by rw [← entry_eq_rawInit]; exact hl)
    (by rw [← entry_eq_rawInit]; exact hw)

end CurrentAdditive.V40LawBankMap
