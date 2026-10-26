import EthInapproximability.CurrentPaper.MatrixWeightedNumberedWriter
import EthInapproximability.CurrentPaper.MatrixTableInterlaceLevelCodes
import EthInapproximability.CurrentPaper.MatrixTableInterlaceDouble

/-!
Frozen current-paper v8 Section 5 and Appendix B. The physical protected
writer numbers rows/columns in copy-major order; `Iteration.step` uses its
own type-first numbering. This is a semantic conjugacy of the *following*
two restorations, with no claim that the proof-side permutation is computed
by the writer or by the interlace machine.
-/

namespace EthInapproximability.CurrentPaper.PostProtectedInterlaceScratch

open EthInapproximability.ParameterizedNP.GuardedSourceGraph NPCC
open MatrixWeightedOrdinalConjugacy MatrixWeightedNumberedWriter

noncomputable section

set_option maxHeartbeats 1000000
attribute [local irreducible] Iteration.nRowNumbering Iteration.nColNumbering
attribute [local irreducible] Iteration.outputRowNumbering Iteration.outputColNumbering

variable {VG EG : Type} [Fintype VG] [DecidableEq VG]
  [Fintype EG] [DecidableEq EG]
variable (G : EndpointGraph VG EG) (sourceConstant b y level : ℕ)
  (M : Iteration.Matrix)

private abbrev physRows := Fintype.card (Iteration.NRow G sourceConstant b y level M)
private abbrev physCols := Fintype.card (Iteration.NCol G sourceConstant b y level M)
private abbrev firstBlocks := 2 ^ Iteration.rq G sourceConstant b y level M
private abbrev secondBlocks := 2 ^ Iteration.rQ G sourceConstant b y level M

/-- Row coordinates after both transpositions: the second restoration's
tuple contains a first-restoration column, so the base *row* permutation
is applied in every tuple coordinate. -/
def outputRowRelabel
    (u : Fin (secondBlocks G sourceConstant b y level M) →
      (Fin (firstBlocks G sourceConstant b y level M) ×
        Fin (physRows G sourceConstant b y level M))) :
    Iteration.OutputRow G sourceConstant b y level M :=
  fun j => ((u j).1,
    (Iteration.nRowNumbering G sourceConstant b y level M).equiv
      (rowPermutation G sourceConstant b y level M (u j).2))

/-- Column coordinates after both transpositions: the first-restoration
tuple contains a base column, so the base *column* permutation is applied
pointwise in that tuple. -/
def outputColRelabel
    (u : Fin (secondBlocks G sourceConstant b y level M) ×
      (Fin (firstBlocks G sourceConstant b y level M) →
        Fin (physCols G sourceConstant b y level M))) :
    Iteration.OutputCol G sourceConstant b y level M :=
  (u.1, fun j =>
    (Iteration.nColNumbering G sourceConstant b y level M).equiv
      (columnPermutation G sourceConstant b y level M (u.2 j)))

/-- The row carrier map is an equivalence. Its first coordinate is the
outer interlace selector; the base-row permutation acts inside every tuple
value, as required by the two transposes. -/
def outputRowEquiv :
    (Fin (secondBlocks G sourceConstant b y level M) →
      (Fin (firstBlocks G sourceConstant b y level M) ×
        Fin (physRows G sourceConstant b y level M))) ≃
      Iteration.OutputRow G sourceConstant b y level M :=
  Equiv.piCongrRight fun _ =>
    Equiv.prodCongr (Equiv.refl _)
      ((rowPermutation G sourceConstant b y level M).trans
        (Iteration.nRowNumbering G sourceConstant b y level M).equiv)

/-- The column carrier map is an equivalence. Its first coordinate is the
outer selector; base-column relabelling acts pointwise in the inner tuple. -/
def outputColEquiv :
    (Fin (secondBlocks G sourceConstant b y level M) ×
      (Fin (firstBlocks G sourceConstant b y level M) →
        Fin (physCols G sourceConstant b y level M))) ≃
      Iteration.OutputCol G sourceConstant b y level M :=
  Equiv.prodCongr (Equiv.refl _)
    (Equiv.piCongrRight fun _ =>
      (columnPermutation G sourceConstant b y level M).trans
        (Iteration.nColNumbering G sourceConstant b y level M).equiv)

theorem outputRowEquiv_apply
    (u : Fin (secondBlocks G sourceConstant b y level M) →
      (Fin (firstBlocks G sourceConstant b y level M) ×
        Fin (physRows G sourceConstant b y level M))) :
    outputRowEquiv G sourceConstant b y level M u =
      outputRowRelabel G sourceConstant b y level M u := rfl

theorem outputColEquiv_apply
    (u : Fin (secondBlocks G sourceConstant b y level M) ×
      (Fin (firstBlocks G sourceConstant b y level M) →
        Fin (physCols G sourceConstant b y level M))) :
    outputColEquiv G sourceConstant b y level M u =
      outputColRelabel G sourceConstant b y level M u := rfl

/-- Exact actual-input conjugacy through both following restorations. -/
theorem actual_double_restoration_conjugacy
    (u : Fin (secondBlocks G sourceConstant b y level M) →
      (Fin (firstBlocks G sourceConstant b y level M) ×
        Fin (physRows G sourceConstant b y level M)))
    (v : Fin (secondBlocks G sourceConstant b y level M) ×
      (Fin (firstBlocks G sourceConstant b y level M) →
        Fin (physCols G sourceConstant b y level M))) :
    Restoration.output
      (Restoration.output
        (physicalNumberedEntry G sourceConstant b y level M)
        (Iteration.rq G sourceConstant b y level M))
      (Iteration.rQ G sourceConstant b y level M) u v =
      Iteration.rawOutput G sourceConstant b y level M
        (outputRowRelabel G sourceConstant b y level M u)
        (outputColRelabel G sourceConstant b y level M v) := by
  rcases v with ⟨j,γ⟩
  rcases hpair : u j with ⟨i,x⟩
  simp only [Restoration.output_apply, Iteration.rawOutput,
    Iteration.aligned, outputRowRelabel, outputColRelabel,
    hpair, physicalNumberedEntry, Iteration.number]

/-- Consequently the two physical post-protection restorations have exactly
the communication cost of the intended one-level typed raw output. -/
theorem actual_double_restoration_D :
    Workspace.Types.CommComplexity.D
      (Restoration.output
        (Restoration.output
          (physicalNumberedEntry G sourceConstant b y level M)
          (Iteration.rq G sourceConstant b y level M))
        (Iteration.rQ G sourceConstant b y level M)) =
      Workspace.Types.CommComplexity.D
        (Iteration.rawOutput G sourceConstant b y level M) := by
  have heq : Restoration.output
      (Restoration.output
        (physicalNumberedEntry G sourceConstant b y level M)
        (Iteration.rq G sourceConstant b y level M))
      (Iteration.rQ G sourceConstant b y level M) =
    fun u v => Iteration.rawOutput G sourceConstant b y level M
      (outputRowEquiv G sourceConstant b y level M u)
      (outputColEquiv G sourceConstant b y level M v) := by
    funext u v
    simpa only [outputRowEquiv_apply, outputColEquiv_apply] using
      actual_double_restoration_conjugacy G sourceConstant b y level M u v
  rw [heq]
  exact D_equiv_invariance _
    (outputRowEquiv G sourceConstant b y level M)
    (outputColEquiv G sourceConstant b y level M)

/-- The numerical row and column enumerations used by the literal double
interlace machine on the physical protected table. -/
def physicalOutputRowNumbering : Iteration.Numbering
    (Fin (secondBlocks G sourceConstant b y level M) →
      (Fin (firstBlocks G sourceConstant b y level M) ×
        Fin (physRows G sourceConstant b y level M))) :=
  ((Iteration.Numbering.fin (firstBlocks G sourceConstant b y level M)).prod
    (Iteration.Numbering.fin (physRows G sourceConstant b y level M))).tuple
      (secondBlocks G sourceConstant b y level M)

def physicalOutputColNumbering : Iteration.Numbering
    (Fin (secondBlocks G sourceConstant b y level M) ×
      (Fin (firstBlocks G sourceConstant b y level M) →
        Fin (physCols G sourceConstant b y level M))) :=
  (Iteration.Numbering.fin (secondBlocks G sourceConstant b y level M)).prod
    ((Iteration.Numbering.fin (physCols G sourceConstant b y level M)).tuple
      (firstBlocks G sourceConstant b y level M))

private theorem numeric_second_result (rows cols r R : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (x : Fin ((MatrixTableInterlaceDouble.firstRowsCount r rows) ^ (2 ^ R)))
    (z : Fin ((2 ^ R) * (MatrixTableInterlaceDouble.firstColsCount r cols))) :
    MatrixTableInterlaceDouble.secondResult R r rows cols f x z =
      Restoration.output (Restoration.output f r) R
        (((((Iteration.Numbering.fin (2 ^ r)).prod
          (Iteration.Numbering.fin rows)).tuple (2 ^ R))).equiv x)
        (((Iteration.Numbering.fin (2 ^ R)).prod
          ((Iteration.Numbering.fin cols).tuple (2 ^ r))).equiv z) := by
  have h := MatrixTableInterlaceLevelCodes.secondRestoration_numeric f
    (Iteration.Numbering.fin rows) (Iteration.Numbering.fin cols) r R x z
  simpa only [MatrixTableInterlaceDouble.secondResult,
    MatrixTableInterlaceDouble.firstResult,
    MatrixTableInterlaceDouble.firstRowsCount,
    MatrixTableInterlaceDouble.firstColsCount,
    MatrixTableInterlaceLevelCodes.numericSource,
    Iteration.Numbering.fin, Equiv.refl_apply] using h.symm

/-- Every cell written by the physical two-restoration controller is the
actual `Iteration.rawOutput` cell at the explicitly lifted carrier coordinates.
The physical numeric indices are not asserted equal to the target indices. -/
theorem physical_secondResult_entry
    (x : Fin ((MatrixTableInterlaceDouble.firstRowsCount
      (Iteration.rq G sourceConstant b y level M)
      (physRows G sourceConstant b y level M)) ^
        (secondBlocks G sourceConstant b y level M)))
    (z : Fin ((secondBlocks G sourceConstant b y level M) *
      (MatrixTableInterlaceDouble.firstColsCount
        (Iteration.rq G sourceConstant b y level M)
        (physCols G sourceConstant b y level M)))) :
    MatrixTableInterlaceDouble.secondResult
      (Iteration.rQ G sourceConstant b y level M)
      (Iteration.rq G sourceConstant b y level M)
      (physRows G sourceConstant b y level M)
      (physCols G sourceConstant b y level M)
      (physicalNumberedEntry G sourceConstant b y level M) x z =
    Iteration.rawOutput G sourceConstant b y level M
      (outputRowRelabel G sourceConstant b y level M
        ((physicalOutputRowNumbering G sourceConstant b y level M).equiv x))
      (outputColRelabel G sourceConstant b y level M
        ((physicalOutputColNumbering G sourceConstant b y level M).equiv z)) := by
  have hcore :
      Restoration.output
        (Restoration.output
          (physicalNumberedEntry G sourceConstant b y level M)
          (Iteration.rq G sourceConstant b y level M))
        (Iteration.rQ G sourceConstant b y level M)
        ((physicalOutputRowNumbering G sourceConstant b y level M).equiv x)
        ((physicalOutputColNumbering G sourceConstant b y level M).equiv z) =
      MatrixTableInterlaceDouble.secondResult
        (Iteration.rQ G sourceConstant b y level M)
        (Iteration.rq G sourceConstant b y level M)
        (physRows G sourceConstant b y level M)
        (physCols G sourceConstant b y level M)
        (physicalNumberedEntry G sourceConstant b y level M) x z := by
    simpa only [physicalOutputRowNumbering, physicalOutputColNumbering] using
      (numeric_second_result
        (physRows G sourceConstant b y level M)
        (physCols G sourceConstant b y level M)
        (Iteration.rq G sourceConstant b y level M)
        (Iteration.rQ G sourceConstant b y level M)
        (physicalNumberedEntry G sourceConstant b y level M) x z).symm
  exact hcore.symm.trans (actual_double_restoration_conjugacy
    G sourceConstant b y level M _ _)

/-- The target `Iteration.step` row ordinal corresponding to a physical
two-restoration row ordinal. This map is proof-side, not a writer routine. -/
def physicalToStepRow
    (x : Fin ((MatrixTableInterlaceDouble.firstRowsCount
      (Iteration.rq G sourceConstant b y level M)
      (physRows G sourceConstant b y level M)) ^
        (secondBlocks G sourceConstant b y level M))) :
    Fin (Iteration.step G sourceConstant b y level M).rows :=
  (Iteration.outputRowNumbering G sourceConstant b y level M).equiv.symm
    (outputRowRelabel G sourceConstant b y level M
      ((physicalOutputRowNumbering G sourceConstant b y level M).equiv x))

/-- The target `Iteration.step` column ordinal corresponding to a physical
two-restoration column ordinal. -/
def physicalToStepCol
    (z : Fin ((secondBlocks G sourceConstant b y level M) *
      (MatrixTableInterlaceDouble.firstColsCount
        (Iteration.rq G sourceConstant b y level M)
        (physCols G sourceConstant b y level M)))) :
    Fin (Iteration.step G sourceConstant b y level M).columns :=
  (Iteration.outputColNumbering G sourceConstant b y level M).equiv.symm
  (outputColRelabel G sourceConstant b y level M
      ((physicalOutputColNumbering G sourceConstant b y level M).equiv z))

/-- Both physical numeric carrier maps are genuine bijections. Their
existence is mathematical; no runtime implementation is charged here. -/
def physicalToStepRowEquiv :
    Fin ((MatrixTableInterlaceDouble.firstRowsCount
      (Iteration.rq G sourceConstant b y level M)
      (physRows G sourceConstant b y level M)) ^
        (secondBlocks G sourceConstant b y level M)) ≃
      Fin (Iteration.step G sourceConstant b y level M).rows :=
  ((physicalOutputRowNumbering G sourceConstant b y level M).equiv.trans
    (outputRowEquiv G sourceConstant b y level M)).trans
      (Iteration.outputRowNumbering G sourceConstant b y level M).equiv.symm

def physicalToStepColEquiv :
    Fin ((secondBlocks G sourceConstant b y level M) *
      (MatrixTableInterlaceDouble.firstColsCount
        (Iteration.rq G sourceConstant b y level M)
        (physCols G sourceConstant b y level M))) ≃
      Fin (Iteration.step G sourceConstant b y level M).columns :=
  ((physicalOutputColNumbering G sourceConstant b y level M).equiv.trans
    (outputColEquiv G sourceConstant b y level M)).trans
      (Iteration.outputColNumbering G sourceConstant b y level M).equiv.symm

/-- The actual second physical interlace table, fed the protected word's
semantic entry function, is the paper's next-stage matrix after explicit
finite row/column relabelling. It is not a same-index equality. -/
theorem physical_secondResult_step_entry
    (x : Fin ((MatrixTableInterlaceDouble.firstRowsCount
      (Iteration.rq G sourceConstant b y level M)
      (physRows G sourceConstant b y level M)) ^
        (secondBlocks G sourceConstant b y level M)))
    (z : Fin ((secondBlocks G sourceConstant b y level M) *
      (MatrixTableInterlaceDouble.firstColsCount
        (Iteration.rq G sourceConstant b y level M)
        (physCols G sourceConstant b y level M)))) :
    MatrixTableInterlaceDouble.secondResult
      (Iteration.rQ G sourceConstant b y level M)
      (Iteration.rq G sourceConstant b y level M)
      (physRows G sourceConstant b y level M)
      (physCols G sourceConstant b y level M)
      (physicalNumberedEntry G sourceConstant b y level M) x z =
      (Iteration.step G sourceConstant b y level M).entry
        (physicalToStepRow G sourceConstant b y level M x)
        (physicalToStepCol G sourceConstant b y level M z) := by
  rw [physical_secondResult_entry, Iteration.step_entry]
  simp only [physicalToStepRow, physicalToStepCol, Equiv.apply_symm_apply]


end
end EthInapproximability.CurrentPaper.PostProtectedInterlaceScratch
