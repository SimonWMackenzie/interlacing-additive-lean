import EthInapproximability.CurrentPaper.SourceClausePrefixUnitAddress

/-!
Generic prefix-chain unit address from unary `n,a`, clause ordinal, width and
position. Locked v8 Section 6 Boolean alphabet encoding. The existing controller
is reused literally; alphabet two was only a restriction of the former run theorem. This stops before any gate output and supplies no target binary
address. The downstream unit writer and clean shared bank are separate.
-/

namespace EthInapproximability.CurrentPaper.SourceGenericUnitAddress

open Turing BitMachineEncoding BitMachineStackEmbedding

abbrev Stack := SourceClauseGateSlotAddress.Stack

noncomputable def initial (n a ordinal w ell : ℕ) : Stack → List Bool :=
  SourceClauseGateSlotAddress.initial n a ell ordinal w [] [] [] []

noncomputable def offsetDone (n a ordinal w ell : ℕ) : Stack → List Bool :=
  SourceClauseGateSlotAddress.offsetDone n a ell ordinal w [] [] [] []

noncomputable def transferred (n a ordinal w ell : ℕ) : Stack → List Bool :=
  SourceClauseGateSlotAddress.transferred n a ell ordinal w [] [] [] []

noncomputable def finalBank (n a ordinal w ell : ℕ) : Stack → List Bool :=
  bank SourceClauseGateSlotAddress.gateEmbedding
    (transferred n a ordinal w ell)
    (SourceClauseGateAffineAddress.addressed ordinal w (n * a + ell)
      [] [] [] [])

/-- Exactly the existing alphabet-independent controller, with no new code. -/
noncomputable abbrev affineProgram :=
  SourceBooleanPrefix.PrefixUnitAddress.affineProgram

noncomputable abbrev program :=
  SourceBooleanPrefix.PrefixUnitAddress.program

theorem affine_run (n a ordinal w ell : ℕ) :
    ∃ T ≤ MatrixAddressMachine.exactTime ordinal w (n * a + ell) +
      UnaryBinaryEncoding.coefficient * (ordinal * w + (n * a + ell) + 1) ^ 2 + 1,
      ((advance affineProgram)^[T])
        (⟨some (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer),
          (false, (SourceLabelAddressMachine.counter.initial, none)),
          transferred n a ordinal w ell⟩) =
        ⟨none, (false, (SourceLabelAddressMachine.counter.initial, none)),
          finalBank n a ordinal w ell⟩ := by
  obtain ⟨T, hT, hr⟩ :=
    SourceClauseGateAffineAddress.address_run ordinal w (n * a + ell) [] [] [] []
  have hlift := BitMachineStackRun.run SourceClauseGateSlotAddress.gateEmbedding
    (transferred n a ordinal w ell)
    SourceClauseGateAffineAddress.addressProgram
    (⟨some (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer),
      (false, (SourceLabelAddressMachine.counter.initial, none)),
      SourceClauseGateAffineAddress.initial ordinal w (n * a + ell) [] [] [] []⟩) T
  rw [hr] at hlift
  simp only [stackCfg] at hlift
  have hbank := SourceClauseGateSlotAddress.affine_initial
    n a ell ordinal w [] [] [] []
  dsimp only [transferred] at hlift
  rw [hbank] at hlift
  refine ⟨T, hT, ?_⟩
  simpa only [affineProgram, transferred, finalBank] using hlift

noncomputable def cost (n a ordinal w ell : ℕ) : ℕ :=
  MatrixAddressMachine.exactTime n a ell +
  (2 * (n * a + ell) + 3) + 1 +
  MatrixAddressMachine.exactTime ordinal w (n * a + ell) +
  UnaryBinaryEncoding.coefficient * (ordinal * w + (n * a + ell) + 1) ^ 2 + 2

theorem run (n a ordinal w ell : ℕ) :
    ∃ T ≤ cost n a ordinal w ell,
      ((advance program)^[T])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)),
          ((false, ((), none)),
            (false, (SourceLabelAddressMachine.counter.initial, none))),
          initial n a ordinal w ell⟩) =
        ⟨none,
          ((false, ((), none)),
            (false, (SourceLabelAddressMachine.counter.initial, none))),
          finalBank n a ordinal w ell⟩ := by
  let c := n * a + ell
  have ho := SourceClauseGateSlotAddress.offset_run
    n a ell ordinal w [] [] [] []
  have hc := SourceClauseGateSlotAddress.copy_run
    n a ell ordinal w [] [] [] []
  have hc' : ((advance SourceClauseGateSlotAddress.copyProgram)^[2 * c + 3])
      (⟨some SourceClauseGateSlotAddress.CopyLabel.scan, ((), none),
        offsetDone n a ordinal w ell⟩) =
      ⟨none, ((), none), transferred n a ordinal w ell⟩ := by
    simpa only [c, offsetDone, transferred] using hc
  obtain ⟨T₁, hT₁, h₁⟩ := BitMachineRawSequence.runs
    SourceClauseGateSlotAddress.offsetProgram
    SourceClauseGateSlotAddress.copyProgram
    MatrixAddressMachine.Label.outer
    SourceClauseGateSlotAddress.CopyLabel.scan
    false false ((), none) ((), none)
    (initial n a ordinal w ell)
    (offsetDone n a ordinal w ell)
    (transferred n a ordinal w ell)
    (MatrixAddressMachine.exactTime n a ell) (2 * c + 3)
    ho hc'
  obtain ⟨T₂, hT₂, h₂⟩ := affine_run n a ordinal w ell
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
    (initial n a ordinal w ell) (transferred n a ordinal w ell)
    (finalBank n a ordinal w ell) T₁ T₂ h₁ h₂
  exact ⟨T, by dsimp [cost, c] at *; omega, hr⟩

noncomputable def binarySource : Stack :=
  SourceClauseGateSlotAddress.gateEmbedding
    SourceClauseGateAffineAddress.addressSource

theorem final_binary (n a ordinal w ell : ℕ) :
    finalBank n a ordinal w ell binarySource =
      (ordinal * w + (n * a + ell)).bits := by
  rw [finalBank, binarySource, bank_at]
  simp [SourceClauseGateAffineAddress.addressed,
    SourceClauseGateAffineAddress.addressSource,
    SourceLabelAddressMachine.outputs, SourceLabelAddressMachine.ambient,
    SourceUnaryBinaryCall.final_bank]

end EthInapproximability.CurrentPaper.SourceGenericUnitAddress
