import CurrentAdditive.ProductAlphabetTables

/-! The three actual source tables from only the two supplied base-law tables. -/

namespace CurrentAdditive.ExecutableCodeSource

open Paper2 CurrentAdditive.DeterministicIndexedMatrix

noncomputable def gammaFromBase {Y : Type}
    [Fintype Y] [DecidableEq Y]
    (D q₁ s : Nat) (μY : PositiveRationalLaw Y)
    (baseY : AlphabetTable Y μY) :
    CodeSource D (q₁ + s + 1) Y μY :=
  fromTable D (q₁ + s + 1) μY baseY

noncomputable def innerTableFromBase {X : Type}
    [Fintype X] [DecidableEq X]
    (q₁ : Nat) [NeZero q₁]
    (μX : PositiveRationalLaw X) (baseX : AlphabetTable X μX) :
    AlphabetTable (Fin q₁ × X)
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX) :=
  productTable (PositiveRationalLaw.uniform (Fin q₁)) μX
    (uniformFinTable q₁) baseX

noncomputable def gammaIndexTable {Y : Type}
    [Fintype Y] [DecidableEq Y]
    (D q₁ s : Nat) (μY : PositiveRationalLaw Y)
    (baseY : AlphabetTable Y μY) :
    AlphabetTable (gammaFromBase D q₁ s μY baseY).Label
      (gammaFromBase D q₁ s μY baseY).law :=
  finAlphabetTable _ (gammaFromBase D q₁ s μY baseY).law

noncomputable def outerTableFromBase {Y : Type}
    [Fintype Y] [DecidableEq Y]
    (D q₁ q₂ s : Nat) [NeZero q₂]
    (μY : PositiveRationalLaw Y) (baseY : AlphabetTable Y μY) :
    AlphabetTable (Fin q₂ × (gammaFromBase D q₁ s μY baseY).Label)
      ((PositiveRationalLaw.uniform (Fin q₂)).prod
        (gammaFromBase D q₁ s μY baseY).law) :=
  productTable (PositiveRationalLaw.uniform (Fin q₂))
    (gammaFromBase D q₁ s μY baseY).law
    (uniformFinTable q₂) (gammaIndexTable D q₁ s μY baseY)

noncomputable def sourcesFromBaseTables {X Y : Type}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (D q₁ q₂ s : Nat) [NeZero q₁] [NeZero q₂] [NeZero s]
    (μX : PositiveRationalLaw X) (μY : PositiveRationalLaw Y)
    (baseX : AlphabetTable X μX) (baseY : AlphabetTable Y μY) :
    Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY :=
  sourcesFromTables D q₁ q₂ s μX μY baseY
    (innerTableFromBase q₁ μX baseX)
    (outerTableFromBase D q₁ q₂ s μY baseY)

#print axioms sourcesFromBaseTables
#print axioms innerTableFromBase
#print axioms outerTableFromBase

end CurrentAdditive.ExecutableCodeSource
