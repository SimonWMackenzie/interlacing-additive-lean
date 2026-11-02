import EthInapproximability.CurrentPaper.EntryClockPolyAtoms

/-!
# Segment 1: the admitted per-entry clock `tableT` is a uniform polynomial in the level size

Lane owner:b-entry-clock-1 (Paper B, unit 2, CP-EFFECTIVE). Pure arithmetic about the
admitted clocks; no machine is built.

* `template_poly`: the admitted template per-address clock
  `EntryRunsRaw.templateAddrBound` (which contains the admitted
  `MatrixStage4TemplateBitMachine.actualBound`) is `PolyIn` the instance size, uniformly
  over all instances and all template addresses.
* `item_poly`: the same for `EntryRunsRaw.itemAddrBound` (which contains the admitted
  `MatrixStage4RowGraphMachine.graphBudget` through `ItemEntry.itemBound`).
* `tableT_poly`: ONE pair of absolute constants `K D` with
  `tableT ≤ K * (Inst.U + 1)^D` for every instance.
* `writer_poly`: the same for the admitted writer clock
  `MatrixTableWriter.writerBound (rows ..) (cols ..) tableT + (2 * (rows * cols) + 2) + 1`,
  which is literally owner-6's `tailBound` shape.
-/

namespace EthInapproximability.CurrentPaper.EntryClockPoly

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open Construction MatrixStage4Codes MatrixStage4Digits MatrixMaterialization

/-- A template address of an instance. -/
structure TA where
  I : Inst
  code : Fin (cols I.a I.s I.q I.cy)
  p : Fin I.s
  ell : Fin I.L

/-- An item address of an instance. -/
structure IA where
  I : Inst
  code : Fin (cols I.a I.s I.q I.cy)
  i : Fin (I.nv + I.nb)
  x : Fin I.rx

abbrev TA.U (t : TA) : ℕ := t.I.U
abbrev IA.U (t : IA) : ℕ := t.I.U

theorem TA.hc (t : TA) : 0 < cols t.I.a t.I.s t.I.q t.I.cy :=
  Nat.lt_of_le_of_lt (Nat.zero_le _) t.code.isLt
theorem IA.hc (t : IA) : 0 < cols t.I.a t.I.s t.I.q t.I.cy :=
  Nat.lt_of_le_of_lt (Nat.zero_le _) t.code.isLt

open Lean Meta Elab Tactic in
/-- Succeeds iff the goal is `PolyIn _ (fun _ => c ..)` with head constant `c`. -/
elab "poly_head " n:ident : tactic => withMainContext do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  let some (_, _, f) := t.app3? ``PolyIn | throwError "poly_head: not PolyIn"
  let .lam _ _ body _ := f | throwError "poly_head: not a lambda"
  let some c := body.getAppFn.constName? | throwError "poly_head: no head constant"
  let name ← realizeGlobalConstNoOverloadWithInfo n
  unless c == name do throwError "poly_head: head mismatch"

/-- One step of the uniform-polynomial decomposition, with the atoms of index map `φ`. -/
macro "poly_step " φ:term:max hc:term:max : tactic => `(tactic| first
  | (poly_head EntryFull.itemSeedLen
     refine PolyIn.mono (fun _ => itemSeedLen_le _ _ _ _) ?_)
  | (poly_head EntryFull.templateSeedLen
     refine PolyIn.mono (fun _ => templateSeedLen_le _ _ _ _) ?_)
  | with_reducible apply PolyIn.add
  | with_reducible apply PolyIn.mul
  | with_reducible apply PolyIn.pow
  | with_reducible apply PolyIn.max
  | with_reducible refine PolyIn.div _ ?_
  | with_reducible refine PolyIn.mod _ ?_
  | with_reducible refine PolyIn.sub _ ?_
  | with_reducible refine PolyIn.mono (fun _ => totalTime_le _ _) ?_
  | with_reducible refine PolyIn.mono (fun _ => powerBound_le _ _) ?_
  | with_reducible refine PolyIn.mono (fun _ => timeBudget_le _ _ _ _) ?_
  | with_reducible refine PolyIn.mono (fun _ => selectorBudget_le _ _) ?_
  | with_reducible refine PolyIn.mono (fun _ => selectorDigit_le _ _) ?_
  | with_reducible refine PolyIn.mono (fun _ => activeRank_le _ _ _) ?_
  | with_reducible refine PolyIn.mono (fun _ => Nat.le_of_lt (Fin.isLt _)) ?_
  | with_reducible exact PolyIn.const _
  | with_reducible exact at_cols $φ $hc
  | with_reducible exact at_s $φ $hc
  | with_reducible exact at_L $φ $hc
  | with_reducible exact at_rx $φ $hc
  | with_reducible exact at_nv $φ $hc
  | with_reducible exact at_nb $φ $hc
  | with_reducible exact at_fl $φ $hc
  | with_reducible exact at_qOne $φ $hc
  | with_reducible exact at_q $φ $hc
  | with_reducible exact at_cy $φ $hc
  | with_reducible exact at_binBase $φ $hc
  | with_reducible exact at_wordBase $φ $hc
  | with_reducible exact at_cyPowFL $φ $hc
  | with_reducible exact at_binPowS $φ $hc
  | with_reducible exact at_cyPow1 $φ $hc
  | with_reducible exact at_rows $φ $hc
  | with_reducible exact at_binPowSub $φ $hc _
  | with_reducible exact at_cyPowFLSub $φ $hc _
  | with_reducible exact at_cyPowSub $φ $hc _
  | (simp only [MatrixStage4FamilyData.fieldTable_length, rowMajor_length, List.length_nil])
  | dsimp only)

theorem template_poly :
    PolyIn TA.U (fun t => EntryRunsRaw.templateAddrBound t.I.R t.I.family (rowMajor t.I.vectors)
      t.code t.p t.ell) := by
  simp only [EntryRunsRaw.templateAddrBound, TemplateSeeding.templateCost, TemplateSeeding.cost1,
    TemplateSeeding.cost3, TemplateSeeding.cost5, EntryStride.strideBound,
    TemplateEntry.actualWords, MatrixStage4TemplateBitMachine.actualBound,
    MatrixStage4TemplateRowConnector.actualBound, MatrixStage4TemplateFirstConnector.actualBound,
    MatrixStage4TemplateFieldDecode.exactBound, MatrixStage4TemplateFieldGather.exactBound,
    MatrixStage4TemplateFieldStart.exactBound, MatrixStage4TemplateEntryMachine.columnTime,
    MatrixStage4TemplateEntryMachine.selectedAlpha, MatrixAddressMachine.exactTime,
    MatrixStage4FirstDigitMachine.digitBound, MatrixStage4TemplateRowField.decodeBound,
    MatrixStage4TemplateRowField.gatherBound, MatrixStage4FamilyData.fieldTable_length,
    rowMajor_length, List.length_nil]
  repeat' (poly_step TA.I TA.hc)

theorem item_poly :
    PolyIn IA.U (fun t => EntryRunsRaw.itemAddrBound t.I.R t.I.hs t.I.family t.I.order
      t.I.vectors t.I.cap t.code t.i t.x) := by
  simp only [EntryRunsRaw.itemAddrBound, ItemSeeding.seedCost, TemplateEntry.actualWords,
    ItemEntry.itemBound, MatrixStage4RowGraphMachine.graphBudget,
    MatrixStage4TailSourceRead.tailBudget, rowMajor_length]
  repeat' (poly_step IA.I IA.hc)

/-- ONE pair of absolute constants bounds the admitted per-entry clock `tableT` of every
instance by a polynomial in the instance size. -/
theorem tableT_poly : PolyIn Inst.U (fun I =>
    EntryRunsRaw.tableT I.R I.hs I.family I.order I.vectors I.cap) := by
  obtain ⟨K1, D1, h1⟩ := template_poly
  obtain ⟨K2, D2, h2⟩ := item_poly
  refine ⟨K1 + K2, D1 + D2, fun I => ?_⟩
  have hX : 1 ≤ I.U + 1 := Nat.le_add_left 1 _
  have e1 : K1 * (I.U + 1) ^ D1 ≤ (K1 + K2) * (I.U + 1) ^ (D1 + D2) :=
    Nat.mul_le_mul (Nat.le_add_right _ _) (Nat.pow_le_pow_right hX (Nat.le_add_right _ _))
  have e2 : K2 * (I.U + 1) ^ D2 ≤ (K1 + K2) * (I.U + 1) ^ (D1 + D2) :=
    Nat.mul_le_mul (Nat.le_add_left _ _) (Nat.pow_le_pow_right hX (Nat.le_add_left _ _))
  unfold EntryRunsRaw.tableT
  apply Finset.sup_le
  intro rc _
  unfold EntryRunsRaw.addrBound
  cases h : rawRowEquiv I.s I.L I.nv I.nb I.order
      ((rowCode I.s I.L I.nv I.nb I.rx I.order).symm rc.1) with
  | inl pe =>
    simp only [Sum.elim_inl]
    exact (h1 ⟨I, rc.2, pe.1, pe.2⟩).trans e1
  | inr ix =>
    simp only [Sum.elim_inr]
    exact (h2 ⟨I, rc.2, ix.1, ix.2⟩).trans e2

/-- The admitted writer clock at the table clock (owner-6's `tailBound` shape). -/
theorem writer_poly : PolyIn Inst.U (fun I =>
    MatrixTableWriter.writerBound (rows I.s I.L I.nv I.nb I.rx) (cols I.a I.s I.q I.cy)
        (EntryRunsRaw.tableT I.R I.hs I.family I.order I.vectors I.cap) +
      (2 * (rows I.s I.L I.nv I.nb I.rx * cols I.a I.s I.q I.cy) + 2) + 1) := by
  have hr : PolyIn Inst.U (fun I => rows I.s I.L I.nv I.nb I.rx) := by
    unfold rows
    refine PolyIn.add (PolyIn.mul ?_ ?_) (PolyIn.mul (PolyIn.add ?_ ?_) ?_) <;>
      exact PolyIn.of_le (fun I => by unfold Inst.U; omega)
  have hc : PolyIn Inst.U (fun I => cols I.a I.s I.q I.cy) :=
    PolyIn.of_le (fun I => by unfold Inst.U; omega)
  unfold MatrixTableWriter.writerBound
  exact PolyIn.add (PolyIn.add (PolyIn.add (PolyIn.mul hr (PolyIn.add (PolyIn.add
    (PolyIn.mul hc (PolyIn.add tableT_poly (PolyIn.const 2))) (PolyIn.mul (PolyIn.const 4) hc))
    (PolyIn.const 8))) (PolyIn.const 5)) (PolyIn.add (PolyIn.mul (PolyIn.const 2)
    (PolyIn.mul hr hc)) (PolyIn.const 2))) (PolyIn.const 1)

#print axioms template_poly
#print axioms item_poly
#print axioms tableT_poly
#print axioms writer_poly

end EthInapproximability.CurrentPaper.EntryClockPoly
