import EthInapproximability.CurrentPaper.MatrixStage4RowGraphMachine
import EthInapproximability.CurrentPaper.MatrixStage4TemplateBitMachine

/-!
# Segment 2: the admitted branch start controls are address-independent

Lane owner:b-stage4-entry-program-3 (Paper B, unit 2, map item 3).

A fixed per-address controller can only load a FIXED finite control. These
theorems show that the start label and start control of both admitted
branch configurations are the same for every address (column code, row,
item, source row, output accumulator): the template one is literally the
constant `initial`/`start`; the item one is independent of `code`, `i`, `x`
and `out` (the admitted `graphSeed_control_independent` covers `i`, `x` only).
-/

set_option maxRecDepth 16384

namespace EthInapproximability.CurrentPaper.ItemControl

open Construction MatrixStage4Codes MatrixStage4Digits MatrixMaterialization

theorem item_control {a s q L nv nb rx cy : ℕ} (hs : 0 < s)
    (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (R : Fin rx → Fin cy → Bool)
    (code code' : Fin (cols a s q cy)) (i j : Fin (nv + nb)) (x y : Fin rx)
    (out out' : List Bool) :
    (MatrixStage4RowGraphMachine.rowFrame
      (MatrixStage4RowGraphMachine.graphSeed hs vectors R code i x out)
      (MatrixStage4RowGraphMachine.itemRowInput (s := s) (L := L) order i x)).var =
    (MatrixStage4RowGraphMachine.rowFrame
      (MatrixStage4RowGraphMachine.graphSeed hs vectors R code' j y out')
      (MatrixStage4RowGraphMachine.itemRowInput (s := s) (L := L) order j y)).var := by
  simp only [MatrixStage4RowGraphMachine.rowFrame, MatrixStage4RowGraphMachine.graphSeed,
    BitMachineEncoding.renameCfg, BitMachineComposition.liftCfg, Equiv.refl_apply,
    MatrixStage4AlignmentVectorGraph.alignmentFrame,
    MatrixStage4AlignmentVectorGraph.pendingGraphControl,
    MatrixStage4AlignmentVectorGraph.graphInput, MatrixStage4VectorGraphSource.vectorFrame,
    MatrixStage4VectorGraphSource.pending, MatrixStage4VectorGraphSource.sourceTarget,
    MatrixStage4VectorGraphSource.sourceTargetSeed, MatrixStage4GraphTailSource.chooseFrame,
    MatrixStage4PowerTailRead.powerFrame, MatrixStage4TailSourceRead.tailFrame,
    MatrixStage4TailSourceRead.tailInput, MatrixStage4TailFromOrdinal.splitFrame,
    MatrixStage4SelectedPower.cutFrame, MatrixStage4VectorGraphSource.vectorInput,
    MatrixStage4VectorFlagRank.lookupFrame, MatrixStage4OrdinalCopyAlignment.copyFrame,
    MatrixStage4OrdinalCopyAlignment.alignmentInput, MatrixStage4AlignmentFromOrdinal.splitFrame,
    MatrixStage4RowGraphMachine.itemRowInput, MatrixStage4RowMachine.cfg, BitMachineCopy.cfg,
    MatrixUnaryDivision.cfg, MatrixTableLookup.cfg, MatrixUnaryCut.cfg]

theorem item_label {a s q L nv nb rx cy : ℕ} (hs : 0 < s)
    (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (R : Fin rx → Fin cy → Bool)
    (code : Fin (cols a s q cy)) (i : Fin (nv + nb)) (x : Fin rx) (out : List Bool) :
    (MatrixStage4RowGraphMachine.rowFrame
      (MatrixStage4RowGraphMachine.graphSeed hs vectors R code i x out)
      (MatrixStage4RowGraphMachine.itemRowInput (s := s) (L := L) order i x)).l =
      some MatrixStage4RowGraphMachine.rowStart := rfl

theorem template_control {a s q L rx cy : ℕ} (R : Fin rx → Fin cy → Bool)
    (family : SecondFamily a q L (Fin rx))
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L) :
    (MatrixStage4TemplateBitMachine.actualSource R family code p ell).var =
      MatrixStage4TemplateBitMachine.initial ∧
    (MatrixStage4TemplateBitMachine.actualSource R family code p ell).l =
      some MatrixStage4TemplateBitMachine.start :=
  ⟨rfl, rfl⟩

#print axioms item_control
#print axioms item_label
#print axioms template_control

end EthInapproximability.CurrentPaper.ItemControl
