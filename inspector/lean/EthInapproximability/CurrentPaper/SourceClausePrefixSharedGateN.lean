import EthInapproximability.CurrentPaper.SourceClausePrefixSharedCore

namespace EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixSharedGateN

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceBooleanEncoding

theorem gateN_final {n q : ℕ} (v : Fin n) (s : Fin 2)
    (savedBits outputBits countBits : List Bool) :
    SourceClauseRowGate.finalBank (0 : Fin 1) (vertexFrame v)
      v.val 2 s.val n s.val v.val (width 2 q + 1) true
      savedBits outputBits countBits PrefixSharedCore.gateN =
        List.replicate n true := by
  rw [SourceClauseRowGate.finalBank, show PrefixSharedCore.gateN =
    SourceClauseRowGate.gateEmbedding (.inl 0) by rfl, bank_at]
  rw [SourceClauseGateSlotAddress.finalBank, bank_outside]
  · simp [SourceClauseGateSlotAddress.transferred,
      BitMachineBroadcast.copied,
      SourceClauseGateSlotAddress.offsetDone,
      SourceClauseGateSlotAddress.offsetOutput,
      SourceClauseGateSlotAddress.offsetSource,
      SourceClauseGateSlotAddress.temp,
      SourceClauseGateSlotAddress.targets,
      SourceClauseGateSlotAddress.affineOffset,
      MatrixAddressMachine.cfg]
  · intro ⟨x, h⟩; cases h

end EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixSharedGateN
