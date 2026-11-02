import CurrentAdditive.DeterministicEndpointAssembly
import CurrentAdditive.DeterministicIndexedSuccessor
import Paper2.RestrictionProfiles
import NPCC.Complexity

/-!
The actual indexed construction changes its finite row and column carrier types
at every step.  A dependent stage retains those carrier types, their original
positive rational laws, and the literal Boolean matrix; it can nevertheless
be the one fixed `State` type used by `DeterministicIteration.Construction`.
This file proves only the semantic numbering and table-presentation bridge.
The Code_D runtime and the NO successor obstruction are separate obligations.
-/

namespace CurrentAdditive.IndexedStagePresentation

open Paper2 Workspace.Types.CommComplexity
open CurrentAdditive.DeterministicIteration
open CurrentAdditive.DeterministicEndpointAssembly

universe u v

/-- A complete finite stage with its actual labels and input laws.  The size
field charges at least the Boolean entries; additional charges for labels and
rational weights may be included by the executable constructor. -/
structure Stage (N : ℕ) where
  Row : Type u
  Col : Type u
  rowFinite : Fintype Row
  colFinite : Fintype Col
  rowDecEq : DecidableEq Row
  colDecEq : DecidableEq Col
  rowLaw : @PositiveRationalLaw Row rowFinite
  colLaw : @PositiveRationalLaw Col colFinite
  matrix : Row → Col → Bool
  encodingSize : ℕ
  entries_le_encoding : Fintype.card Row * Fintype.card Col ≤ encodingSize
  public_side : N ≤ max (Fintype.card Row) (Fintype.card Col)
  stepClock : ℕ

attribute [instance] Stage.rowFinite Stage.colFinite Stage.rowDecEq Stage.colDecEq

def rows {N : ℕ} (R : Stage N) : ℕ := Fintype.card R.Row
def cols {N : ℕ} (R : Stage N) : ℕ := Fintype.card R.Col

/-- Numerical presentation of precisely the original indexed matrix. -/
noncomputable def table {N : ℕ} (R : Stage N) :
    Fin (rows R) → Fin (cols R) → Bool :=
  fun i j => R.matrix ((Fintype.equivFin R.Row).symm i)
    ((Fintype.equivFin R.Col).symm j)

theorem table_cost {N : ℕ} (R : Stage N) : D (table R) = D R.matrix := by
  exact NPCC.D_equiv_invariance R.matrix
    (Fintype.equivFin R.Row).symm (Fintype.equivFin R.Col).symm

theorem rows_pos {N : ℕ} (R : Stage N) : 0 < rows R := by
  exact Fintype.card_pos_iff.mpr R.rowLaw.nonempty

theorem cols_pos {N : ℕ} (R : Stage N) : 0 < cols R := by
  exact Fintype.card_pos_iff.mpr R.colLaw.nonempty

/-- One semantic construction on the fixed dependent carrier.  Its step will
be instantiated with the literal `Sources.successor`; no future-cost claim is
stored in this definition. -/
noncomputable def construction {Graph : Type v} (N : ℕ)
    (seed : Graph → Stage N) (step : Graph → Stage N → Stage N)
    (valid : Graph → Stage N → Prop) (ρ : ℝ) :
    Construction Graph (Stage N) where
  seed := seed
  step := step
  cost := fun R => D R.matrix
  valid := valid
  profile := fun _ R => RestrictionProfile R.matrix
    R.rowLaw.toFiniteLaw R.colLaw.toFiniteLaw ρ (D R.matrix : ℤ)
  size := Stage.encodingSize
  stepTime := Stage.stepClock

/-- The endpoint's table data for every stage of the same construction. -/
noncomputable def presentation {Graph : Type v} (N : ℕ)
    (seed : Graph → Stage N) (step : Graph → Stage N → Stage N)
    (valid : Graph → Stage N → Prop) (ρ : ℝ) :
    TablePresentation (construction N seed step valid ρ) N where
  rows := rows
  cols := cols
  table := table
  rows_pos := rows_pos
  cols_pos := cols_pos
  exact_cost := table_cost
  entries_le_encoding := Stage.entries_le_encoding
  public_side := Stage.public_side

#print axioms table_cost
#print axioms presentation

end CurrentAdditive.IndexedStagePresentation
