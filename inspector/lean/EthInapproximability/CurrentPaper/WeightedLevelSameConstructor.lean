import EthInapproximability.CurrentPaper.MatrixWeightedActualPhysicalStep

/-! Lane owner:b-weighted-level-2, unit 2, segment 3 (map item 6, first half):
the one-level same-constructor identity, stated honestly.

The admitted physical step (`ProtectedFullBankBridgeScratch.actual_physical_step_run`)
ends in `actualPhysicalOutput = rowMajor (fun x z => (Iteration.step …).entry
(physicalToStepRow x) (physicalToStepCol z))`; its source says this is "not a
same-index equality". This module identifies that word as the row-major word
of `Iteration.number (Iteration.rawOutput G c b y lvl M) physRowNumbering
physColNumbering`: the SAME constructor `Iteration.rawOutput` of the SAME step
(same `G, c, b, y, lvl, M`), with the physical numbering (the base-row/column
permutations `rowPermutation`/`columnPermutation` composed with
`Iteration.nRowNumbering`/`nColNumbering`) in place of Iteration's chosen
`outputRowNumbering`/`outputColNumbering`. Communication cost `D`,
robustness, the `LambdaGE` profile and both dimensions agree with
`Iteration.step`, by the admitted numbering invariances.

NOT claimed: `physicalLevel = Iteration.step` (false in general: the two
numberings differ by the physical base permutations), nor any k-round
identity with `Iteration.run`; see CHECKPOINT.md. -/

namespace EthInapproximability.CurrentPaper.WeightedLevelSameConstructor

open NPCC Workspace.Types.CommComplexity Workspace.Types.Interlace
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open PostProtectedInterlaceScratch

noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

attribute [local irreducible] Iteration.nRowNumbering Iteration.nColNumbering
attribute [local irreducible] Iteration.outputRowNumbering Iteration.outputColNumbering
attribute [local irreducible] Iteration.rawOutput GraphVectors.vertexCount
  GraphVectors.auxiliaryCount

variable {VG EG : Type} [Fintype VG] [DecidableEq VG]
  [Fintype EG] [DecidableEq EG]
variable (G : EndpointGraph VG EG) (c b y lvl : ℕ) (M : Iteration.Matrix)

/-- The physical output row numbering, as a numbering of Iteration's own
output-row carrier. -/
def physRowNumbering : Iteration.Numbering (Iteration.OutputRow G c b y lvl M) :=
  ⟨(physicalOutputRowNumbering G c b y lvl M).size,
    (physicalOutputRowNumbering G c b y lvl M).equiv.trans
      (outputRowEquiv G c b y lvl M)⟩

def physColNumbering : Iteration.Numbering (Iteration.OutputCol G c b y lvl M) :=
  ⟨(physicalOutputColNumbering G c b y lvl M).size,
    (physicalOutputColNumbering G c b y lvl M).equiv.trans
      (outputColEquiv G c b y lvl M)⟩

/-- The level the physical machine produces: Iteration's constructor
`rawOutput`, numbered physically. -/
def physicalLevel : Iteration.Matrix :=
  Iteration.number (Iteration.rawOutput G c b y lvl M)
    (physRowNumbering G c b y lvl M) (physColNumbering G c b y lvl M)

theorem physicalLevel_entry
    (x : Fin (physicalLevel G c b y lvl M).rows)
    (z : Fin (physicalLevel G c b y lvl M).columns) :
    (physicalLevel G c b y lvl M).entry x z =
      (Iteration.step G c b y lvl M).entry
        (physicalToStepRow G c b y lvl M x) (physicalToStepCol G c b y lvl M z) := by
  rw [Iteration.step_entry]
  simp only [physicalToStepRow, physicalToStepCol, Equiv.apply_symm_apply]
  rw [← outputRowEquiv_apply, ← outputColEquiv_apply]
  rfl

/-- The admitted physical output word is exactly the row-major word of the
physically numbered level. -/
theorem physical_output_eq :
    ProtectedFullBankBridgeScratch.actualPhysicalOutput G c b y lvl M =
      MatrixMaterialization.rowMajor (physicalLevel G c b y lvl M).entry := by
  unfold ProtectedFullBankBridgeScratch.actualPhysicalOutput
  apply congrArg MatrixMaterialization.rowMajor
  funext x z
  exact (physicalLevel_entry G c b y lvl M x z).symm

theorem physicalLevel_cost :
    D (physicalLevel G c b y lvl M).entry = D (Iteration.step G c b y lvl M).entry :=
  (Iteration.number_cost _ _ _).trans (Iteration.step_cost G c b y lvl M).symm

theorem physicalLevel_robust (r : ℕ) :
    IsRobustAt (physicalLevel G c b y lvl M).entry r ↔
      IsRobustAt (Iteration.step G c b y lvl M).entry r :=
  (Iteration.number_robust _ _ _ r).trans
    (Iteration.number_robust (Iteration.rawOutput G c b y lvl M)
      (Iteration.outputRowNumbering G c b y lvl M)
      (Iteration.outputColNumbering G c b y lvl M) r).symm

theorem physicalLevel_lambda (p : ℕ) (u w : ℝ) :
    LambdaGE (physicalLevel G c b y lvl M).entry p u w =
      LambdaGE (Iteration.step G c b y lvl M).entry p u w :=
  (Iteration.number_lambda _ _ _ p u w).trans
    (Iteration.number_lambda (Iteration.rawOutput G c b y lvl M)
      (Iteration.outputRowNumbering G c b y lvl M)
      (Iteration.outputColNumbering G c b y lvl M) p u w).symm

theorem physicalLevel_rows :
    (physicalLevel G c b y lvl M).rows = (Iteration.step G c b y lvl M).rows := by
  have h1 := Fintype.card_congr (physRowNumbering G c b y lvl M).equiv
  have h2 := Fintype.card_congr (Iteration.outputRowNumbering G c b y lvl M).equiv
  simp only [Fintype.card_fin] at h1 h2
  exact h1.trans h2.symm

theorem physicalLevel_columns :
    (physicalLevel G c b y lvl M).columns = (Iteration.step G c b y lvl M).columns := by
  have h1 := Fintype.card_congr (physColNumbering G c b y lvl M).equiv
  have h2 := Fintype.card_congr (Iteration.outputColNumbering G c b y lvl M).equiv
  simp only [Fintype.card_fin] at h1 h2
  exact h1.trans h2.symm

/-- One level, same constructor, one output-sensitive clock (the admitted
`actualPhysicalBudget`): from the admitted start bank the physical program
halts with the row-major word of the physically numbered level, whose cost,
robustness, `LambdaGE` profile and dimensions equal those of
`Iteration.step` for the SAME `(G, c, b, y, lvl, M)`. -/
theorem physical_level_same_constructor :
    (∃ t ≤ ProtectedFullBankBridgeScratch.actualPhysicalBudget G c b y lvl M,
      ∃ z : MatrixTableInterlaceProtectedBridge.Config,
        MatrixTableInterlaceProtectedBridge.run t
          (ProtectedFullBankBridgeScratch.actualPhysicalStart G c b y lvl M) = z ∧
        z.l = none ∧
        z.stk (.inr MatrixTableInterlaceOuterJoin.secondOutput) =
          MatrixMaterialization.rowMajor (physicalLevel G c b y lvl M).entry) ∧
    D (physicalLevel G c b y lvl M).entry = D (Iteration.step G c b y lvl M).entry ∧
    (IsRobustAt (physicalLevel G c b y lvl M).entry b ↔
      IsRobustAt (Iteration.step G c b y lvl M).entry b) ∧
    LambdaGE (physicalLevel G c b y lvl M).entry 1 (2 ^ (-(b : ℝ))) (3 / 5) =
      LambdaGE (Iteration.step G c b y lvl M).entry 1 (2 ^ (-(b : ℝ))) (3 / 5) ∧
    (physicalLevel G c b y lvl M).rows = (Iteration.step G c b y lvl M).rows ∧
    (physicalLevel G c b y lvl M).columns = (Iteration.step G c b y lvl M).columns := by
  obtain ⟨t, ht, z, hz, hl, ho⟩ :=
    ProtectedFullBankBridgeScratch.actual_physical_step_run G c b y lvl M
  exact ⟨⟨t, ht, z, hz, hl, ho.trans (physical_output_eq G c b y lvl M)⟩,
    physicalLevel_cost G c b y lvl M, physicalLevel_robust G c b y lvl M b,
    physicalLevel_lambda G c b y lvl M 1 _ _, physicalLevel_rows G c b y lvl M,
    physicalLevel_columns G c b y lvl M⟩

#print axioms physicalLevel_entry
#print axioms physical_output_eq
#print axioms physical_level_same_constructor

end
end EthInapproximability.CurrentPaper.WeightedLevelSameConstructor
