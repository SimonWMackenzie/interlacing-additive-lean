import EthInapproximability.CurrentPaper.EntryRunsRaw
import EthInapproximability.CurrentPaper.OuterLevel0Full

/-!
# Segment 6 (fit): known-blank cells of the level-0 prep exit bank

Lane owner:b-stage4-entry-program-5 (Paper B, unit 2, map item 3).

At the prep exit `OuterLevel0Prep.exitBank G n c (G4 (level0RowsBank M G n c F Q P))`:
* every scalar/writer-region cell outside `WeightedLevel0Clean.keepS` is blank
  (`exit_blank_scalar`), and every fresh scale cell and the copy temporary are
  blank (`exit_blank_fresh`, `exit_blank_tmp`);
* those regions have `253 - 23 = 230` and `75` cells (`card_scalar`,
  `card_keepS`, `card_fresh`), so `EntryRunsRaw.K + 3 + 7 + 2 = 248` tail
  cells fit into known-blank cells (`tail_fits`): the stack does NOT need a
  widening for the raw-table tail.
-/

namespace EthInapproximability.CurrentPaper.EntryExitBlank

set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Ready OuterLevel0Prep

variable (Mm : BitMachine.Machine)
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The scalar-region cell `x` as a cell of the level stack. -/
def scalarCell (x : WeightedScalarComplete.Stack) : HStack := .inl (.inl (.inl x))

theorem exit_blank_scalar (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool)
    (x : WeightedScalarComplete.Stack) (hx : x ∉ keepS) :
    exitBank G n c (G4 (level0RowsBank Mm G n c F Q P)) (scalarCell x) = [] := by
  show BitMachineClearBank.cleared cells2 (G3 (level0RowsBank Mm G n c F Q P))
    (Sum.inl (Sum.inl x)) = []
  rw [BitMachineClearBank.cleared_foreign _ _ _ (by
    intro i hi
    fin_cases i <;> cases hi)]
  show Function.update (G2 (level0RowsBank Mm G n c F Q P)) dstC _ (Sum.inl (Sum.inl x)) = _
  rw [Function.update_of_ne (by intro h; cases h)]
  show Function.update (G1 (level0RowsBank Mm G n c F Q P)) dstR _ (Sum.inl (Sum.inl x)) = _
  rw [Function.update_of_ne (by intro h; cases h)]
  exact clean_scalar _ x hx

theorem exit_blank_fresh (G : EndpointGraph V E) (n c : ℕ) (L : GStack → List Bool)
    (y : SStack) : exitBank G n c L (fresh y) = [] := rfl

theorem exit_blank_tmp (G : EndpointGraph V E) (n c : ℕ) (L : GStack → List Bool) :
    exitBank G n c L tmpH = [] := rfl

theorem card_scalar : Fintype.card WeightedScalarComplete.Stack = 253 := by
  simp only [Fintype.card_sum, Fintype.card_fin]
  decide

theorem card_keepS : keepS.card = 23 := by
  simp only [keepS, Finset.card_map]
  decide

theorem card_fresh : Fintype.card SStack = 73 := by
  simp only [Fintype.card_sum, Fintype.card_fin]
  decide

open scoped Classical in
theorem card_compl_keepS : (keepSᶜ).card = 230 := by
  rw [Finset.card_compl, card_scalar, card_keepS]

/-- The tail's own cells (bank, index/answer cells, writer administration, two
transfer cells) fit into the known-blank cells of the prep exit
(the complement of `keepS` in the scalar region, plus the fresh scale region). -/
theorem tail_fits :
    EntryRunsRaw.K + 3 + 7 + 2 ≤
      (Fintype.card WeightedScalarComplete.Stack - keepS.card) + Fintype.card SStack := by
  rw [card_scalar, card_keepS, card_fresh]
  have hK : EntryRunsRaw.K = 236 := by
    simp only [EntryRunsRaw.K, Fintype.card_sum, Fintype.card_fin]
  rw [hK]
  decide

#print axioms exit_blank_scalar
#print axioms card_scalar
#print axioms card_keepS
#print axioms card_fresh
#print axioms card_compl_keepS
#print axioms tail_fits

end EthInapproximability.CurrentPaper.EntryExitBlank
