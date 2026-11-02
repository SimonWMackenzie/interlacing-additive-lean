import CurrentAdditive.SourcesFromBaseTables

/-! Exact entry arrays and lengths for the generated source alphabets. -/

namespace CurrentAdditive.ExecutableCodeSource

open Paper2 SequentialCode CurrentAdditive.DeterministicIndexedMatrix

theorem innerTableFromBase_entries {X : Type}
    [Fintype X] [DecidableEq X]
    (q₁ : Nat) [NeZero q₁]
    (μX : PositiveRationalLaw X) (baseX : AlphabetTable X μX) :
    (innerTableFromBase q₁ μX baseX).entries =
      appendWeighted (uniformFinEntries q₁) baseX.entries := by
  simp [innerTableFromBase, productTable, uniformFinTable_entries]

theorem innerTableFromBase_size {X : Type}
    [Fintype X] [DecidableEq X]
    (q₁ : Nat) [NeZero q₁]
    (μX : PositiveRationalLaw X) (baseX : AlphabetTable X μX) :
    (innerTableFromBase q₁ μX baseX).entries.size =
      q₁ * baseX.entries.size := by
  rw [innerTableFromBase_entries, appendWeighted_size, uniformFinEntries_size]

theorem gammaIndexTable_entries {Y : Type}
    [Fintype Y] [DecidableEq Y]
    (D q₁ s : Nat) (μY : PositiveRationalLaw Y)
    (baseY : AlphabetTable Y μY) :
    (gammaIndexTable D q₁ s μY baseY).entries =
      finEntries _ (gammaFromBase D q₁ s μY baseY).law.weight := by
  rfl

theorem gammaIndexTable_size {Y : Type}
    [Fintype Y] [DecidableEq Y]
    (D q₁ s : Nat) (μY : PositiveRationalLaw Y)
    (baseY : AlphabetTable Y μY) :
    (gammaIndexTable D q₁ s μY baseY).entries.size =
      Fintype.card (gammaFromBase D q₁ s μY baseY).Label := by
  unfold gammaIndexTable finAlphabetTable finEntries
  dsimp [gammaFromBase, fromTable, fromAlphabet]
  simp
  exact (Fintype.card_fin _).symm

theorem outerTableFromBase_entries {Y : Type}
    [Fintype Y] [DecidableEq Y]
    (D q₁ q₂ s : Nat) [NeZero q₂]
    (μY : PositiveRationalLaw Y) (baseY : AlphabetTable Y μY) :
    (outerTableFromBase D q₁ q₂ s μY baseY).entries =
      appendWeighted (uniformFinEntries q₂)
        (finEntries _ (gammaFromBase D q₁ s μY baseY).law.weight) := by
  simp [outerTableFromBase, productTable, uniformFinTable_entries,
    gammaIndexTable_entries]
  rfl

theorem outerTableFromBase_size {Y : Type}
    [Fintype Y] [DecidableEq Y]
    (D q₁ q₂ s : Nat) [NeZero q₂]
    (μY : PositiveRationalLaw Y) (baseY : AlphabetTable Y μY) :
    (outerTableFromBase D q₁ q₂ s μY baseY).entries.size =
      q₂ * Fintype.card (gammaFromBase D q₁ s μY baseY).Label := by
  simp [outerTableFromBase, productTable, appendWeighted_size,
    uniformFinTable_entries, uniformFinEntries_size, gammaIndexTable_size]

#print axioms innerTableFromBase_entries
#print axioms innerTableFromBase_size
#print axioms gammaIndexTable_size
#print axioms outerTableFromBase_entries
#print axioms outerTableFromBase_size

end CurrentAdditive.ExecutableCodeSource
