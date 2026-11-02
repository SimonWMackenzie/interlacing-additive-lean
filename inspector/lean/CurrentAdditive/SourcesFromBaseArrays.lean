import CurrentAdditive.AlphabetTableSize

/-! Complete, positive indexed input arrays are the only table inputs. -/

namespace CurrentAdditive.ExecutableCodeSource

open Paper2 SequentialCode SequentialSourceCode SequentialFeatureCoverage
  CurrentAdditive.DeterministicIndexedMatrix

def baseTableOfArray {A : Type} [Fintype A] [DecidableEq A]
    (μ : PositiveRationalLaw A) (entries : Array (A × ℚ))
    (hpositive : SourcePositive entries)
    (hmass : sourceMass entries = 1)
    (hcover : ∀ a : A, a ∈ (entries.map Prod.fst).toList)
    (hpoint : ∀ a : A, alphabetPointMass entries a = μ.weight a) :
    AlphabetTable A μ :=
  ⟨entries, hpositive, hmass, hcover, hpoint⟩

/-- The final deterministic source bundle is assembled from two explicit
base-law arrays. Each derived alphabet is the literal finite Cartesian array
constructed by `finEntries` and `appendWeighted`. -/
noncomputable def sourcesFromBaseArrays {X Y : Type}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (D q₁ q₂ s : Nat) [NeZero q₁] [NeZero q₂] [NeZero s]
    (μX : PositiveRationalLaw X) (μY : PositiveRationalLaw Y)
    (baseX : Array (X × ℚ)) (baseY : Array (Y × ℚ))
    (hXpositive : SourcePositive baseX)
    (hXmass : sourceMass baseX = 1)
    (hXcover : ∀ x : X, x ∈ (baseX.map Prod.fst).toList)
    (hXpoint : ∀ x : X, alphabetPointMass baseX x = μX.weight x)
    (hYpositive : SourcePositive baseY)
    (hYmass : sourceMass baseY = 1)
    (hYcover : ∀ y : Y, y ∈ (baseY.map Prod.fst).toList)
    (hYpoint : ∀ y : Y, alphabetPointMass baseY y = μY.weight y) :
    Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY :=
  sourcesFromBaseTables D q₁ q₂ s μX μY
    (baseTableOfArray μX baseX hXpositive hXmass hXcover hXpoint)
    (baseTableOfArray μY baseY hYpositive hYmass hYcover hYpoint)

theorem gammaFromBase_label_bound {Y : Type}
    [Fintype Y] [DecidableEq Y]
    (D q₁ s : Nat) (μY : PositiveRationalLaw Y)
    (baseY : AlphabetTable Y μY) :
    Fintype.card (gammaFromBase D q₁ s μY baseY).Label ≤
      (1 + (q₁ + s + 1) * baseY.entries.size) ^ D := by
  exact fromTable_label_bound D (q₁ + s + 1) μY baseY

theorem outerTableFromBase_size_bound {Y : Type}
    [Fintype Y] [DecidableEq Y]
    (D q₁ q₂ s : Nat) [NeZero q₂]
    (μY : PositiveRationalLaw Y) (baseY : AlphabetTable Y μY) :
    (outerTableFromBase D q₁ q₂ s μY baseY).entries.size ≤
      q₂ * (1 + (q₁ + s + 1) * baseY.entries.size) ^ D := by
  rw [outerTableFromBase_size]
  exact Nat.mul_le_mul_left q₂ (gammaFromBase_label_bound D q₁ s μY baseY)

#print axioms baseTableOfArray
#print axioms sourcesFromBaseArrays
#print axioms gammaFromBase_label_bound
#print axioms outerTableFromBase_size_bound

end CurrentAdditive.ExecutableCodeSource
