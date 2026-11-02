import CurrentAdditive.ExecutableCodeSource

/-! Explicit rational alphabet tables feed each of the three source calls. -/

namespace CurrentAdditive.ExecutableCodeSource

open Paper2 SequentialCode SequentialSourceCode SequentialFeatureCoverage
  CurrentAdditive.DeterministicIndexedMatrix

/-- The actual finite input table for `Code_D`. Its entries are retained as
array positions; a table may list a symbol more than once, provided its total
point mass agrees with the given law. -/
structure AlphabetTable (Y : Type) [Fintype Y] [DecidableEq Y]
    (μ : PositiveRationalLaw Y) where
  entries : Array (Y × ℚ)
  positive : SourcePositive entries
  normalized : sourceMass entries = 1
  covers : ∀ y : Y, y ∈ (entries.map Prod.fst).toList
  pointMass : ∀ y, alphabetPointMass entries y = μ.weight y

def fromTable {Y : Type} [Fintype Y] [DecidableEq Y]
    (D q : Nat) (μ : PositiveRationalLaw Y)
    (table : AlphabetTable Y μ) : CodeSource D q Y μ :=
  fromAlphabet D q μ table.entries table.positive table.normalized
    table.covers table.pointMass

theorem fromTable_label_bound {Y : Type} [Fintype Y] [DecidableEq Y]
    (D q : Nat) (μ : PositiveRationalLaw Y)
    (table : AlphabetTable Y μ) :
    Fintype.card (fromTable D q μ table).Label ≤
      (1 + q * table.entries.size) ^ D :=
  fromAlphabet_label_bound D q μ table.entries table.positive
    table.normalized table.covers table.pointMass

/-- The outer table is supplied after the Γ call because its alphabet contains
Γ's indexed labels, not merely their decoded words. -/
noncomputable def sourcesFromTables {X Y : Type}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (D q₁ q₂ s : Nat) [NeZero q₁] [NeZero q₂] [NeZero s]
    (μX : PositiveRationalLaw X) (μY : PositiveRationalLaw Y)
    (gammaTable : AlphabetTable Y μY)
    (innerTable : AlphabetTable (Fin q₁ × X)
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX))
    (outerTable : AlphabetTable
      (Fin q₂ × (fromTable D (q₁ + s + 1) μY gammaTable).Label)
      ((PositiveRationalLaw.uniform (Fin q₂)).prod
        (fromTable D (q₁ + s + 1) μY gammaTable).law)) :
    Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY :=
  let gamma := fromTable D (q₁ + s + 1) μY gammaTable
  {
    gamma := gamma
    inner := fromTable D q₂ _ innerTable
    outer := fromTable D s _ outerTable
  }

#print axioms fromTable
#print axioms fromTable_label_bound
#print axioms sourcesFromTables

end CurrentAdditive.ExecutableCodeSource
