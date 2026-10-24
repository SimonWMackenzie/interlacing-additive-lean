import EthInapproximability.CurrentPaper.EntryPrepBudget

/-!
# Segment 5 (budget, workspace sizes of the two R6 recomputes)

Lane owner:b-stage4-entry-program-6. Cardinalities of the admitted recompute
stacks, against the known-blank budget of `P6Budget` (424 cells besides the
level writer, of which 19 hold the `cw` targets):

* `card_LS : Fintype.card WeightedLevelColumnSave.Stack = 260`,
  `card_prime : Fintype.card PrimeFromWords.Stack = 28`; `FamilyRowBody.Cell`
  (28 constructors-with-arity: 7 + 4 + 11 + 4 + 2) and `EntryFamilyAssembly.X`
  (5 constructors) have no `Fintype` instance, so the `ACell` count
  `28 + 28 + 5 = 61` enters `family_workspace_fits` as literals read off the
  inductive definitions (NOT a checked cardinality);
* `card_Z2 : Fintype.card VectorsFromGraphQ.Z2 = 137`.
-/

namespace EthInapproximability.CurrentPaper.EntryPrepBudget

set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

theorem card_LS : Fintype.card WeightedLevelColumnSave.Stack = 260 := by
  simp only [Fintype.card_sum, Fintype.card_fin]
  decide

theorem card_prime : Fintype.card PrimeFromWords.Stack = 28 := by
  simp only [Fintype.card_sum, Fintype.card_fin]
  decide

theorem card_Z2 : Fintype.card VectorsFromGraphQ.Z2 = 137 := by
  simp only [Fintype.card_sum, Fintype.card_fin, card_extra]
  decide

open scoped Classical in
/-- The level-controller re-run stack `LS ⊕ ACell` (with `|ACell| = 28 + 28 + 5`
read off the definitions) plus the 19 `cw` cells fits into the known-blank cells
besides the level writer. -/
theorem family_workspace_fits :
    Fintype.card WeightedLevelColumnSave.Stack + (28 + Fintype.card PrimeFromWords.Stack + 5) + 19 ≤
      Fintype.card BlankIdx - (Finset.univ.filter (fun k : Fin 64 => k ∉ WeightedLevel0Clean.keepW)).card := by
  rw [budget_without_writer, card_LS, card_prime]
  decide

open scoped Classical in
theorem vectors_workspace_fits :
    Fintype.card VectorsFromGraphQ.Z2 + 19 ≤
      Fintype.card BlankIdx - (Finset.univ.filter (fun k : Fin 64 => k ∉ WeightedLevel0Clean.keepW)).card := by
  rw [budget_without_writer, card_Z2]
  decide

#print axioms card_LS
#print axioms card_prime
#print axioms card_Z2
#print axioms family_workspace_fits
#print axioms vectors_workspace_fits

end EthInapproximability.CurrentPaper.EntryPrepBudget
