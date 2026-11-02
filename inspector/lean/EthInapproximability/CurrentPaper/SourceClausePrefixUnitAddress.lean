import EthInapproximability.CurrentPaper.SourceClauseBooleanPrefix
import EthInapproximability.CurrentPaper.SourceClauseGateSlotAddress

/-!
Physical prefix-chain unit address from unary `n`, clause ordinal, width and
position. This stops before any gate output and supplies no target binary
address. The downstream unit writer and clean shared bank are separate.
-/

namespace EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixUnitAddress

open Turing BitMachineEncoding BitMachineStackEmbedding

abbrev Stack := SourceClauseGateSlotAddress.Stack

noncomputable def initial (n ordinal w ell : ℕ) : Stack → List Bool :=
  SourceClauseGateSlotAddress.initial n 2 ell ordinal w [] [] [] []

noncomputable def offsetDone (n ordinal w ell : ℕ) : Stack → List Bool :=
  SourceClauseGateSlotAddress.offsetDone n 2 ell ordinal w [] [] [] []

noncomputable def transferred (n ordinal w ell : ℕ) : Stack → List Bool :=
  SourceClauseGateSlotAddress.transferred n 2 ell ordinal w [] [] [] []

noncomputable def finalBank (n ordinal w ell : ℕ) : Stack → List Bool :=
  bank SourceClauseGateSlotAddress.gateEmbedding
    (transferred n ordinal w ell)
    (SourceClauseGateAffineAddress.addressed ordinal w (2 * n + ell)
      [] [] [] [])

noncomputable def affineProgram (l : SourceLabelAddressMachine.Label) :=
  stackStmt SourceClauseGateSlotAddress.gateEmbedding
    (SourceClauseGateAffineAddress.addressProgram l)

noncomputable def program :=
  BitMachineRawSequence.program
    (BitMachineRawSequence.program SourceClauseGateSlotAddress.offsetProgram
      SourceClauseGateSlotAddress.copyProgram
      SourceClauseGateSlotAddress.CopyLabel.scan false ((), none))
    affineProgram
    (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)
    (false, ((), none))
    (false, (SourceLabelAddressMachine.counter.initial, none))

theorem affine_run (n ordinal w ell : ℕ) :
    ∃ T ≤ MatrixAddressMachine.exactTime ordinal w (2 * n + ell) +
      UnaryBinaryEncoding.coefficient * (ordinal * w + (2 * n + ell) + 1) ^ 2 + 1,
      ((advance affineProgram)^[T])
        (⟨some (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer),
          (false, (SourceLabelAddressMachine.counter.initial, none)),
          transferred n ordinal w ell⟩) =
        ⟨none, (false, (SourceLabelAddressMachine.counter.initial, none)),
          finalBank n ordinal w ell⟩ := by
  obtain ⟨T, hT, hr⟩ :=
    SourceClauseGateAffineAddress.address_run ordinal w (2 * n + ell) [] [] [] []
  have hlift := BitMachineStackRun.run SourceClauseGateSlotAddress.gateEmbedding
    (transferred n ordinal w ell)
    SourceClauseGateAffineAddress.addressProgram
    (⟨some (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer),
      (false, (SourceLabelAddressMachine.counter.initial, none)),
      SourceClauseGateAffineAddress.initial ordinal w (2 * n + ell) [] [] [] []⟩) T
  rw [hr] at hlift
  simp only [stackCfg] at hlift
  have hbank := SourceClauseGateSlotAddress.affine_initial
    n 2 ell ordinal w [] [] [] []
  rw [show n * 2 + ell = 2 * n + ell by omega] at hbank
  dsimp only [transferred] at hlift
  rw [hbank] at hlift
  refine ⟨T, hT, ?_⟩
  simpa only [affineProgram, transferred, finalBank] using hlift

noncomputable def cost (n ordinal w ell : ℕ) : ℕ :=
  MatrixAddressMachine.exactTime n 2 ell +
  (2 * (2 * n + ell) + 3) + 1 +
  MatrixAddressMachine.exactTime ordinal w (2 * n + ell) +
  UnaryBinaryEncoding.coefficient * (ordinal * w + (2 * n + ell) + 1) ^ 2 + 2

theorem run (n ordinal w ell : ℕ) :
    ∃ T ≤ cost n ordinal w ell,
      ((advance program)^[T])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)),
          ((false, ((), none)),
            (false, (SourceLabelAddressMachine.counter.initial, none))),
          initial n ordinal w ell⟩) =
        ⟨none,
          ((false, ((), none)),
            (false, (SourceLabelAddressMachine.counter.initial, none))),
          finalBank n ordinal w ell⟩ := by
  let c := 2 * n + ell
  have ho := SourceClauseGateSlotAddress.offset_run
    n 2 ell ordinal w [] [] [] []
  have hc := SourceClauseGateSlotAddress.copy_run
    n 2 ell ordinal w [] [] [] []
  have hc' : ((advance SourceClauseGateSlotAddress.copyProgram)^[2 * c + 3])
      (⟨some SourceClauseGateSlotAddress.CopyLabel.scan, ((), none),
        offsetDone n ordinal w ell⟩) =
      ⟨none, ((), none), transferred n ordinal w ell⟩ := by
    simpa only [c, offsetDone, transferred, Nat.mul_comm n 2] using hc
  obtain ⟨T₁, hT₁, h₁⟩ := BitMachineRawSequence.runs
    SourceClauseGateSlotAddress.offsetProgram
    SourceClauseGateSlotAddress.copyProgram
    MatrixAddressMachine.Label.outer
    SourceClauseGateSlotAddress.CopyLabel.scan
    false false ((), none) ((), none)
    (initial n ordinal w ell)
    (offsetDone n ordinal w ell)
    (transferred n ordinal w ell)
    (MatrixAddressMachine.exactTime n 2 ell) (2 * c + 3)
    ho hc'
  obtain ⟨T₂, hT₂, h₂⟩ := affine_run n ordinal w ell
  obtain ⟨T, hT, hr⟩ := BitMachineRawSequence.runs
    (BitMachineRawSequence.program SourceClauseGateSlotAddress.offsetProgram
      SourceClauseGateSlotAddress.copyProgram
      SourceClauseGateSlotAddress.CopyLabel.scan false ((), none))
    affineProgram
    (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)
    (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)
    (false, ((), none)) (false, ((), none))
    (false, (SourceLabelAddressMachine.counter.initial, none))
    (false, (SourceLabelAddressMachine.counter.initial, none))
    (initial n ordinal w ell) (transferred n ordinal w ell)
    (finalBank n ordinal w ell) T₁ T₂ h₁ h₂
  exact ⟨T, by dsimp [cost, c] at *; omega, hr⟩

noncomputable def binarySource : Stack :=
  SourceClauseGateSlotAddress.gateEmbedding
    SourceClauseGateAffineAddress.addressSource

theorem final_binary (n ordinal w ell : ℕ) :
    finalBank n ordinal w ell binarySource =
      (ordinal * w + (2 * n + ell)).bits := by
  rw [finalBank, binarySource, bank_at]
  simp [SourceClauseGateAffineAddress.addressed,
    SourceClauseGateAffineAddress.addressSource,
    SourceLabelAddressMachine.outputs, SourceLabelAddressMachine.ambient,
    SourceUnaryBinaryCall.final_bank]

end EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixUnitAddress
