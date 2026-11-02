import EthInapproximability.CurrentPaper.MatrixWeightedActualPhysicalStep

/-! Lane owner:b-weighted-level-5, unit 2, segment 1 (1c-c-outer), piece A.

Closed form of the OUTER region (`MatrixTableInterlaceOuterJoin.Stack`) of the
admitted physical-step start `ProtectedFullBankBridgeScratch.actualPhysicalStart`:
`emptyOuter (outerReady B r rows cols b c s lam f)` holds unary `lam` in the
outer-width machine input cell, unary `b`, `c`, `s` in the restoration-width
machine input cells 0, 1, 2, and is BLANK in every other cell (the first
block, both size headers, both writer headers and the source word are exactly
the six cells blanked by `emptyInner`/`emptyOuter`). Its control is one fixed
constant. No machine claim is made in this file. -/

namespace EthInapproximability.CurrentPaper.OuterStartBank

open Turing BitMachineEncoding BitMachineComposition
open MatrixTableInterlaceProtectedBridge

noncomputable section

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

/-- The OStack region of the physical-step start, in closed form. -/
def outerTarget (b c s lam : ℕ) : OStack → List Bool :=
  Sum.elim (MatrixOuterWidthMachine.startCfg lam).stk
    (Sum.elim (MatrixRestorationWidthMachine.startCfg b c s 0).stk (fun _ => []))

/-- The fixed control of the outer start (independent of every parameter). -/
def outerVar : MatrixTableInterlaceOuterJoin.Control :=
  (emptyOuter (outerReady 0 0 0 0 0 0 0 0 (fun _ _ => false))).var

theorem emptyOuter_var (B r rows cols b c s lam : ℕ) (f : Fin rows → Fin cols → Bool) :
    (emptyOuter (outerReady B r rows cols b c s lam f)).var = outerVar := by
  unfold outerVar
  change (outerReady B r rows cols b c s lam f).var =
    (outerReady 0 0 0 0 0 0 0 0 (fun _ _ => false)).var
  simp only [outerReady, MatrixTableInterlaceOuterJoin.outerFrame,
    liftCfg,
    MatrixTableInterlaceOuterJoin.emptyInner,
    MatrixTableInterlaceOuterJoin.readyInner,
    MatrixTableInterlaceScalarJoin.restorationFrame,
    MatrixTableInterlaceScalarJoin.emptyDouble,
    MatrixTableInterlaceDouble.firstFrame,
    MatrixTableInterlaceDouble.secondPrepared,
    MatrixTableInterlaceDouble.firstPrepared,
    MatrixTableInterlaceFirstTranspose.firstFrame,
    MatrixTableInterlaceFirstRestoration.combinedFrame,
    MatrixTableInterlaceCombined.bridgeCfg,
    MatrixTableInterlaceCombined.cfg,
    MatrixOuterWidthMachine.startCfg, BitMachine.Machine.init,
    MatrixRestorationWidthMachine.startCfg, BitMachineComposition.leftCfg,
    MatrixRestorationWidthMachine.productStart, renameCfg,
    MatrixRestorationWidthMachineProduct.cfg]

theorem combined_blank (r rows cols : ℕ) (w : List Bool)
    (k : MatrixTableInterlaceCombined.Stack)
    (h0 : k ≠ .inl 0) (h1 : k ≠ .inl 1) (h2 : k ≠ .inl 2)
    (h3 : k ≠ .inr (.inl (.inl 0))) (h4 : k ≠ .inr (.inl (.inl 7)))
    (h5 : k ≠ .inr (.inl (.inl 17))) :
    (MatrixTableInterlaceCombined.bridgeCfg MatrixTableInterlaceCombined.start (2^r)
      rows cols w [] [] [] [] []).stk k = [] := by
  rcases k with m | ((m | m) | e)
  · fin_cases m <;>
      simp_all [MatrixTableInterlaceCombined.bridgeCfg, MatrixTableInterlaceCombined.cfg,
        MatrixTableInterlaceCombined.sizeBank, MatrixTableInterlaceSize.cfg]
  · fin_cases m <;>
      simp_all [MatrixTableInterlaceCombined.bridgeCfg, MatrixTableInterlaceCombined.cfg,
        MatrixTableInterlaceCombined.writerData, MatrixTableWriter.Data.contents,
        MatrixTableWriter.Data.cell, MatrixTableInterlace.persistentBank]
  · fin_cases m <;>
      simp [MatrixTableInterlaceCombined.bridgeCfg, MatrixTableInterlaceCombined.cfg,
        MatrixTableInterlaceCombined.writerData, MatrixTableWriter.Data.contents,
        MatrixTableWriter.Data.cell]
  · cases e <;>
      simp [MatrixTableInterlaceCombined.bridgeCfg, MatrixTableInterlaceCombined.cfg,
        MatrixTableInterlaceCombined.writerData, MatrixTableWriter.Data.contents,
        MatrixTableWriter.Data.foreign]

theorem emptyOuter_stk (B r rows cols b c s lam : ℕ) (f : Fin rows → Fin cols → Bool) :
    (emptyOuter (outerReady B r rows cols b c s lam f)).stk = outerTarget b c s lam := by
  funext k
  by_cases h₁ : k = oSizeRows
  · subst k; rw [emptyOuter_sizeRows]; rfl
  by_cases h₂ : k = oSizeCols
  · subst k; rw [emptyOuter_sizeCols]; rfl
  by_cases h₃ : k = oWriterRows
  · subst k; rw [emptyOuter_writerRows]; rfl
  by_cases h₄ : k = oWriterCols
  · subst k; rw [emptyOuter_writerCols]; rfl
  by_cases h₅ : k = oWriterSource
  · subst k; rw [emptyOuter_writerSource]; rfl
  rw [ProtectedFullBankBridgeScratch.emptyOuter_other _ k h₁ h₂ h₃ h₄ h₅]
  rcases k with k | (k | k)
  · simp [outerReady, MatrixTableInterlaceOuterJoin.outerFrame, liftCfg, outerTarget]
  · simp only [outerReady, MatrixTableInterlaceOuterJoin.outerFrame,
      MatrixTableInterlaceOuterJoin.emptyInner,
      MatrixTableInterlaceOuterJoin.readyInner,
      MatrixTableInterlaceScalarJoin.restorationFrame,
      liftCfg, MatrixTableInterlaceOuterJoin.firstSlot,
      Function.update_apply, Sum.inl_ne_inr, Sum.elim_inl,
      Sum.elim_inr, if_false, outerTarget, reduceCtorEq]
  · rcases k with j | (j | j)
    · rcases j with (cc | rw) | t
      · by_cases hc0 : cc = .inl 0
        · subst cc
          simpa only [outerReady, firstCombinedO,
            MatrixTableInterlaceOuterJoin.outerFrame,
            liftCfg, Sum.elim_inr] using
            (MatrixTableInterlaceOuterJoin.emptyInner_first B r rows cols b c s f)
        · have hc1 : cc ≠ .inl 1 := by
            intro h; subst h; exact h₁ rfl
          have hc2 : cc ≠ .inl 2 := by
            intro h; subst h; exact h₂ rfl
          have hc3 : cc ≠ .inr (.inl (.inl 0)) := by
            intro h; subst h; exact h₃ rfl
          have hc4 : cc ≠ .inr (.inl (.inl 7)) := by
            intro h; subst h; exact h₄ rfl
          have hc5 : cc ≠ .inr (.inl (.inl 17)) := by
            intro h; subst h; exact h₅ rfl
          have e := MatrixTableInterlaceProtectedBridge.outerReady_first_bank
            B r rows cols b c s lam f cc hc0
          change (outerReady B r rows cols b c s lam f).stk (firstCombinedO cc) = []
          rw [e]
          exact combined_blank r rows cols _ cc hc0 hc1 hc2 hc3 hc4 hc5
      · simp only [outerReady,
          MatrixTableInterlaceOuterJoin.outerFrame,
          MatrixTableInterlaceOuterJoin.emptyInner,
          MatrixTableInterlaceOuterJoin.readyInner,
          MatrixTableInterlaceScalarJoin.restorationFrame,
          MatrixTableInterlaceScalarJoin.emptyDouble,
          MatrixTableInterlaceDouble.firstFrame,
          MatrixTableInterlaceDouble.firstPrepared,
          MatrixTableInterlaceFirstTranspose.firstFrame,
          MatrixTableInterlaceFirstRestoration.combinedFrame,
          liftCfg,
          MatrixTableInterlaceOuterJoin.firstSlot,
          MatrixTableInterlaceOuterJoin.firstBlock,
          Function.update_apply, Sum.elim_inr, Sum.elim_inl,
          Sum.inl_ne_inr, if_false, outerTarget, reduceCtorEq,
          MatrixTableInterlaceFirstRestoration.emptyRowBank, ite_self]
      · simp only [outerReady,
          MatrixTableInterlaceOuterJoin.outerFrame,
          MatrixTableInterlaceOuterJoin.emptyInner,
          MatrixTableInterlaceOuterJoin.readyInner,
          MatrixTableInterlaceScalarJoin.restorationFrame,
          MatrixTableInterlaceScalarJoin.emptyDouble,
          MatrixTableInterlaceDouble.firstFrame,
          MatrixTableInterlaceDouble.firstPrepared,
          MatrixTableInterlaceFirstTranspose.firstFrame,
          liftCfg,
          MatrixTableInterlaceOuterJoin.firstSlot,
          MatrixTableInterlaceOuterJoin.firstBlock,
          Function.update_apply, Sum.elim_inr, Sum.elim_inl,
          Sum.inl_ne_inr, if_false, outerTarget, reduceCtorEq,
          MatrixTableInterlaceFirstTranspose.emptyTransposeBank, ite_self]
    · simp only [outerReady,
        MatrixTableInterlaceOuterJoin.outerFrame,
        MatrixTableInterlaceOuterJoin.emptyInner,
        MatrixTableInterlaceOuterJoin.readyInner,
        MatrixTableInterlaceScalarJoin.restorationFrame,
        MatrixTableInterlaceScalarJoin.emptyDouble,
        MatrixTableInterlaceDouble.firstFrame,
        liftCfg,
        MatrixTableInterlaceOuterJoin.firstSlot,
        MatrixTableInterlaceOuterJoin.firstBlock,
        Function.update_apply, Sum.elim_inr, Sum.elim_inl,
        outerTarget, reduceCtorEq,
        MatrixTableInterlaceDouble.initialForeign, ite_self]
    · simp only [outerReady,
        MatrixTableInterlaceOuterJoin.outerFrame,
        MatrixTableInterlaceOuterJoin.emptyInner,
        MatrixTableInterlaceOuterJoin.readyInner,
        MatrixTableInterlaceScalarJoin.restorationFrame,
        MatrixTableInterlaceScalarJoin.emptyDouble,
        MatrixTableInterlaceDouble.firstFrame,
        liftCfg,
        MatrixTableInterlaceOuterJoin.firstSlot,
        MatrixTableInterlaceOuterJoin.firstBlock,
        Function.update_apply, Sum.elim_inr, Sum.elim_inl,
        outerTarget, reduceCtorEq,
        MatrixTableInterlaceDouble.initialForeign, ite_self]
      try (fin_cases j <;> rfl)

variable {VG EG : Type} [Fintype VG] [DecidableEq VG] [Fintype EG] [DecidableEq EG]

/-- The outer region of the admitted physical start at any level, in closed form. -/
theorem actualPhysicalStart_outer
    (G : EthInapproximability.ParameterizedNP.GuardedSourceGraph.EndpointGraph VG EG)
    (sc b y level : ℕ) (M : Iteration.Matrix) (o : OStack) :
    (ProtectedFullBankBridgeScratch.actualPhysicalStart G sc b y level M).stk (.inr o) =
      outerTarget b sc
        (Parameters.bins (Iteration.stepParameters G sc b y level M))
        (Parameters.scale (Iteration.stepParameters G sc b y level M)) o := by
  unfold ProtectedFullBankBridgeScratch.actualPhysicalStart
  change (emptyOuter _).stk o = _
  rw [emptyOuter_stk]
  rfl

/-- The writer region of the admitted physical start is the admitted writer start. -/
theorem actualPhysicalStart_writer
    (G : EthInapproximability.ParameterizedNP.GuardedSourceGraph.EndpointGraph VG EG)
    (sc b y level : ℕ) (M : Iteration.Matrix) (w : WStack) :
    (ProtectedFullBankBridgeScratch.actualPhysicalStart G sc b y level M).stk (.inl w) =
      (ProtectedFullBankBridgeScratch.actualWriterStart G sc b y level M).stk w := rfl

theorem actualPhysicalStart_label
    (G : EthInapproximability.ParameterizedNP.GuardedSourceGraph.EndpointGraph VG EG)
    (sc b y level : ℕ) (M : Iteration.Matrix) :
    (ProtectedFullBankBridgeScratch.actualPhysicalStart G sc b y level M).l =
      some MatrixTableInterlaceProtectedBridge.start := rfl

theorem actualPhysicalStart_var
    (G : EthInapproximability.ParameterizedNP.GuardedSourceGraph.EndpointGraph VG EG)
    (sc b y level : ℕ) (M : Iteration.Matrix) :
    (ProtectedFullBankBridgeScratch.actualPhysicalStart G sc b y level M).var =
      ((MatrixWeightedOrderPreparation.initial, MatrixWeightedOrderWriter.writerInitial),
        (outerVar, none)) := by
  unfold ProtectedFullBankBridgeScratch.actualPhysicalStart writerFrame
  dsimp only [liftCfg]
  rw [emptyOuter_var]
  rfl

#print axioms emptyOuter_var
#print axioms combined_blank
#print axioms emptyOuter_stk
#print axioms actualPhysicalStart_outer
#print axioms actualPhysicalStart_writer
#print axioms actualPhysicalStart_label
#print axioms actualPhysicalStart_var

end
end EthInapproximability.CurrentPaper.OuterStartBank
