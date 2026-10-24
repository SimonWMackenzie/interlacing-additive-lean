import EthInapproximability.CurrentPaper.EntryExitBlank
import EthInapproximability.CurrentPaper.EntryFamilyLevel
import EthInapproximability.CurrentPaper.VectorsFromGraphQ

/-!
# Segment 5/6 (budget): the complete known-blank region of the level-0 prep exit

Lane owner:b-stage4-entry-program-6 (Paper B, unit 2, map item 3).

Owner-5 (`EntryExitBlank`) and its read-back counted only the cleared scalar
cells outside `keepS` and the fresh scale cells (262 cells after removing the
41 blank level-writer cells). The admitted prep exit bank
`OuterLevel0Prep.exitBank G n c (G4 (level0RowsBank …))` has MORE cells known
blank, all by the admitted definitions:

* the 143 cells of the double-interlace region `DStack` of the bridge's
  outer join (`OuterStartBank.outerTarget` is `fun _ => []` there): `exit_blank_dstack`;
* the seven `save` cells of the level controller (cleared by the admitted
  `WeightedLevel0Clean.clearCells`): `exit_blank_save`;
* the master `N` (cleared): `exit_blank_N`;
* the two rows/cols source masters `nat 3 0`, `nat 3 1` (cleared by `cells2`):
  `exit_blank_src`;
* the three writer index cells `Fin 3` and the five writer administration cells
  other than `rows`, `cols` (never written by the ready phase): `exit_blank_admin`,
  `exit_blank_extra`.

With owner-5's `exit_blank_scalar`, `exit_blank_fresh`, `exit_blank_tmp`:
`blankCell : BlankIdx ↪ HStack` (`blankCell_inj`) is ONE injective family of
cells all blank at the prep exit (`exit_blank_all`), of cardinality
`230 + 73 + 1 + 143 + 7 + 1 + 2 + 3 + 5 = 465` (`card_blankIdx`); removing the
41 blank level-writer cells (the tail's own `Fin 64` IS the level writer) leaves
424 cells, not 262 (`budget_without_writer`).

Also recorded (exact scope, for the root's R6 plan):
* `family_rerun_conflict`: the admitted `EntryFamilyLevel.level_family_tables`
  requires 22 writer cells blank; exactly eight of them (7, 8, 9, 15, 17, 18,
  27, 28) are KEPT nonblank at the prep exit, so the level controller cannot be
  re-run in place on the level's own scalar region without first moving them.
* `seed_rows`, `seed_cols`, `seed_entry`, `seed_word_length`: the level-0 matrix
  `(seedState b).matrix` has `2 ^ width b` rows and `width b` columns
  (`width b = 2 ^ clog 2 (64 (b + 1))`, `b = sourceDepth n`) and entry
  `testBit x (width b - 1 - y)`: its row-major word depends on `n` and has
  length `2 ^ width b * width b`. It is NOT a fixed push program; no admitted
  producer exists.
-/

namespace EthInapproximability.CurrentPaper.EntryPrepBudget

set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Ready OuterLevel0Prep

variable (Mm : BitMachine.Machine)
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

abbrev DStack := MatrixTableInterlaceScalarJoin.DStack

/-- The double-interlace cell `d` of the bridge's outer join, as a global cell. -/
def dCell (d : DStack) : HStack := .inr (.inl (.inr (.inr d)))
/-- The level controller's `save` cell `j`. -/
def saveCell (j : Fin 7) : HStack := .inl (.inl (.inr (.inl j)))
/-- The rows/cols source master `nat 3 i`. -/
def srcCell (i : Fin 2) : HStack := .inl (.inl (mc (.nat 3 i.val)))
/-- Writer index cell `i` of the ready phase. -/
def adminCell (i : Fin 3) : HStack := .inl (.inr (.inl i))
/-- Writer administration cell `e` of the ready phase. -/
def extraCell (e : MatrixTableWriter.Extra) : HStack := .inl (.inr (.inr e))

theorem exit_blank_dstack (G : EndpointGraph V E) (n c : ℕ) (L : GStack → List Bool)
    (d : DStack) : exitBank G n c L (dCell d) = [] := rfl

theorem exit_blank_save (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool)
    (j : Fin 7) :
    exitBank G n c (G4 (level0RowsBank Mm G n c F Q P)) (saveCell j) = [] := by
  show BitMachineClearBank.cleared cells2 (G3 (level0RowsBank Mm G n c F Q P))
    (Sum.inl (Sum.inr (Sum.inl j))) = []
  rw [BitMachineClearBank.cleared_foreign _ _ _ (by
    intro i hi
    fin_cases i <;> cases hi)]
  show Function.update (G2 (level0RowsBank Mm G n c F Q P)) dstC _
    (Sum.inl (Sum.inr (Sum.inl j))) = _
  rw [Function.update_of_ne (by intro h; cases h)]
  show Function.update (G1 (level0RowsBank Mm G n c F Q P)) dstR _
    (Sum.inl (Sum.inr (Sum.inl j))) = _
  rw [Function.update_of_ne (by intro h; cases h)]
  exact clean_save _ j

theorem exit_blank_N (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool) :
    exitBank G n c (G4 (level0RowsBank Mm G n c F Q P)) (mcell .N) = [] := by
  show BitMachineClearBank.cleared cells2 (G3 (level0RowsBank Mm G n c F Q P))
    (Sum.inl (mc .N)) = []
  rw [BitMachineClearBank.cleared_foreign _ _ _ (by
    intro i hi
    fin_cases i <;> cases hi)]
  show Function.update (G2 (level0RowsBank Mm G n c F Q P)) dstC _ (Sum.inl (mc .N)) = _
  rw [Function.update_of_ne (by intro h; cases h)]
  show Function.update (G1 (level0RowsBank Mm G n c F Q P)) dstR _ (Sum.inl (mc .N)) = _
  rw [Function.update_of_ne (by intro h; cases h)]
  exact clean_N _

theorem exit_blank_src (G : EndpointGraph V E) (n c : ℕ) (L : CStack → List Bool)
    (i : Fin 2) : exitBank G n c (G4 L) (srcCell i) = [] := by
  show BitMachineClearBank.cleared cells2 (G3 L) (Sum.inl (mc (.nat 3 i.val))) = []
  fin_cases i
  · exact BitMachineClearBank.cleared_bank cells2 (G3 L) 0
  · exact BitMachineClearBank.cleared_bank cells2 (G3 L) 1

theorem exit_blank_admin (G : EndpointGraph V E) (n c : ℕ) (L : CStack → List Bool)
    (i : Fin 3) : exitBank G n c (G4 L) (adminCell i) = [] := by
  show BitMachineClearBank.cleared cells2 (G3 L) (Sum.inr (Sum.inl i)) = []
  rw [BitMachineClearBank.cleared_foreign _ _ _ (by
    intro j hj
    fin_cases j <;> cases hj)]
  show Function.update (G2 L) dstC _ (Sum.inr (Sum.inl i)) = _
  rw [Function.update_of_ne (by intro h; cases h)]
  show Function.update (G1 L) dstR _ (Sum.inr (Sum.inl i)) = _
  rw [Function.update_of_ne (by intro h; cases h)]
  rfl

theorem exit_blank_extra (G : EndpointGraph V E) (n c : ℕ) (L : CStack → List Bool)
    (e : MatrixTableWriter.Extra) (hr : e ≠ .rows) (hc : e ≠ .cols) :
    exitBank G n c (G4 L) (extraCell e) = [] := by
  show BitMachineClearBank.cleared cells2 (G3 L) (Sum.inr (Sum.inr e)) = []
  rw [BitMachineClearBank.cleared_foreign _ _ _ (by
    intro j hj
    fin_cases j <;> cases hj)]
  show Function.update (G2 L) dstC _ (Sum.inr (Sum.inr e)) = _
  rw [Function.update_of_ne (by
    intro h
    exact hc (Sum.inr.inj (Sum.inr.inj h)))]
  show Function.update (G1 L) dstR _ (Sum.inr (Sum.inr e)) = _
  rw [Function.update_of_ne (by
    intro h
    exact hr (Sum.inr.inj (Sum.inr.inj h)))]
  rfl

/-! ## One injective family of known-blank cells -/

/-- The administration cells other than `rows`, `cols`. -/
abbrev ExtraFree := {e : MatrixTableWriter.Extra // e ≠ .rows ∧ e ≠ .cols}

/-- Index of the known-blank cells: cleared scalar cells, fresh scale cells, the
copy temporary, the double-interlace region, the save region, `N`, the two
source masters, the three writer index cells, the five free administration cells. -/
abbrev BlankIdx :=
  {x : WeightedScalarComplete.Stack // x ∉ keepS} ⊕ (SStack ⊕ (Unit ⊕ (DStack ⊕
    (Fin 7 ⊕ (Unit ⊕ (Fin 2 ⊕ (Fin 3 ⊕ ExtraFree)))))))

def blankMap : BlankIdx → HStack
  | .inl x => EntryExitBlank.scalarCell x.1
  | .inr (.inl y) => fresh y
  | .inr (.inr (.inl _)) => tmpH
  | .inr (.inr (.inr (.inl d))) => dCell d
  | .inr (.inr (.inr (.inr (.inl j)))) => saveCell j
  | .inr (.inr (.inr (.inr (.inr (.inl _))))) => mcell .N
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl i)))))) => srcCell i
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl i))))))) => adminCell i
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr e))))))) => extraCell e.1

theorem blankMap_inj : Function.Injective blankMap := by
  intro a b h
  rcases a with x | y | u | d | j | u | i | i | e <;>
  rcases b with x' | y' | u' | d' | j' | u' | i' | i' | e' <;>
  first
    | (cases h; done)
    | skip
  all_goals simp only [blankMap, EntryExitBlank.scalarCell, fresh, tmpH, dCell, saveCell,
      mcell, srcCell, adminCell, extraCell, mc, Sum.inl.injEq, Sum.inr.injEq] at h
  all_goals first
    | (subst h; rfl)
    | (cases u; cases u'; rfl)
    | exact congrArg Sum.inl (Subtype.ext h)
    | exact congrArg (fun e => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inr (Sum.inr e)))))))) (Subtype.ext h)
    | (have h' := WeightedRawWords.Aux.nat.inj h
       exact congrArg (fun i => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inl i))))))) (Fin.ext h'.2))


/-- `blankCell`: the injective family of known-blank cells. -/
def blankCell : BlankIdx ↪ HStack := ⟨blankMap, blankMap_inj⟩

theorem exit_blank_all (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool)
    (z : BlankIdx) :
    exitBank G n c (G4 (level0RowsBank Mm G n c F Q P)) (blankCell z) = [] := by
  rcases z with x | y | u | d | j | u | i | i | e
  · exact EntryExitBlank.exit_blank_scalar Mm G n c F Q P x.1 x.2
  · exact EntryExitBlank.exit_blank_fresh G n c _ y
  · exact EntryExitBlank.exit_blank_tmp G n c _
  · exact exit_blank_dstack G n c _ d
  · exact exit_blank_save Mm G n c F Q P j
  · exact exit_blank_N Mm G n c F Q P
  · exact exit_blank_src G n c _ i
  · exact exit_blank_admin G n c _ i
  · exact exit_blank_extra G n c _ e.1 e.2.1 e.2.2

theorem card_extra : Fintype.card MatrixTableWriter.Extra = 7 := by decide

theorem card_extraFree : Fintype.card ExtraFree = 5 := by decide

theorem card_dstack : Fintype.card DStack = 143 := by
  simp only [DStack, MatrixTableInterlaceScalarJoin.DStack, Fintype.card_sum, Fintype.card_fin,
    card_extra]

open scoped Classical in
theorem card_blankIdx : Fintype.card BlankIdx = 465 := by
  have h1 : Fintype.card {x : WeightedScalarComplete.Stack // x ∉ keepS} = 230 := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe, EntryExitBlank.card_scalar,
      EntryExitBlank.card_keepS]
  rw [Fintype.card_sum, h1, Fintype.card_sum, EntryExitBlank.card_fresh, Fintype.card_sum,
    Fintype.card_unit, Fintype.card_sum, card_dstack, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_sum, Fintype.card_unit, Fintype.card_sum, Fintype.card_fin, Fintype.card_sum,
    Fintype.card_fin, card_extraFree]

/-- The level-writer cells outside `keepW` (41 of them) are among the cleared scalar
cells; the tail's own writer `Fin 64` occupies them. What remains for the tail's other
cells and for every recompute: 424 cells. -/
theorem card_writer_outside_keep : (Finset.univ.filter (fun k : Fin 64 => k ∉ keepW)).card = 41 := by
  decide

open scoped Classical in
theorem budget_without_writer :
    Fintype.card BlankIdx - (Finset.univ.filter (fun k : Fin 64 => k ∉ keepW)).card = 424 := by
  rw [card_blankIdx, card_writer_outside_keep]

/-! ## The in-place obstruction for re-running the level controller -/

/-- The writer cells `EntryFamilyLevel.level_family_tables` requires blank (hypotheses
`h17 … h60`, in order). -/
def familyReqBlank : Finset (Fin 64) :=
  {17, 62, 27, 63, 28, 61, 7, 8, 9, 10, 11, 12, 13, 14, 15, 18, 54, 55, 56, 57, 58, 60}

theorem family_rerun_conflict : familyReqBlank ∩ keepW = {7, 8, 9, 15, 17, 18, 27, 28} := by
  decide

/-! ## The level-0 matrix word -/

theorem seed_rows (b : ℕ) : (Iteration.seedMatrix b).rows = 2 ^ IndexSeed.width b := rfl

theorem seed_cols (b : ℕ) : (Iteration.seedMatrix b).columns = IndexSeed.width b := rfl

theorem seed_word_length (b : ℕ) :
    (MatrixMaterialization.rowMajor (Iteration.seedMatrix b).entry).length =
      2 ^ IndexSeed.width b * IndexSeed.width b := by
  rw [MatrixMaterialization.rowMajor_length]
  rfl

theorem seed_word_length_lower (b : ℕ) :
    2 ^ (64 * (b + 1)) ≤
      (MatrixMaterialization.rowMajor (Iteration.seedMatrix b).entry).length := by
  rw [seed_word_length]
  have hw := IndexSeed.width_lower b
  have hpos : 1 ≤ IndexSeed.width b := le_trans (by omega) hw
  calc 2 ^ (64 * (b + 1)) ≤ 2 ^ IndexSeed.width b := Nat.pow_le_pow_right (by decide) hw
    _ = 2 ^ IndexSeed.width b * 1 := (Nat.mul_one _).symm
    _ ≤ 2 ^ IndexSeed.width b * IndexSeed.width b := Nat.mul_le_mul_left _ hpos

#print axioms exit_blank_dstack
#print axioms exit_blank_save
#print axioms exit_blank_N
#print axioms exit_blank_src
#print axioms exit_blank_admin
#print axioms exit_blank_extra
#print axioms blankMap_inj
#print axioms exit_blank_all
#print axioms card_dstack
#print axioms card_blankIdx
#print axioms budget_without_writer
#print axioms family_rerun_conflict
#print axioms seed_rows
#print axioms seed_cols
#print axioms seed_word_length
#print axioms seed_word_length_lower

end EthInapproximability.CurrentPaper.EntryPrepBudget
