import EthInapproximability.CurrentPaper.EntryTailEmbed
import EthInapproximability.CurrentPaper.LevelJPrep

/-!
# Level-j entry lane, piece 0: the level-`j` prep exit bank facts

Lane owner:b-entry-levelj-1 (Paper B, unit 2, CP-ITER). Level-`j` analogues, at an
ARBITRARY level state `(b, yb, lv, Mx)` and master region `mS`, of the level-0 facts the
entry chain reads off the prep exit bank:

* `exit_blank_all_j`: every `EntryPrepBudget.blankCell z` is blank in
  `exitBankJ G c b yb lv Mx (G4 L)` for EVERY row bank `L` (the proofs of owner-5
  `EntryExitBlank` / owner-6 `EntryPrepBudget` are generic in the row bank; restated for
  `LevelJPrep.exitBankJ`, which has the same `Sum.elim` shape as `OuterLevel0Prep.exitBank`);
* `exit_blank_nw_j`: the same for `EntryTailEmbed.nwMap`;
* `exit_writer_cell_j`, `exit_writer_words_j`: at the admitted level-`j` exit bank
  (`LevelJReady.ready_writer_j`, `ready_writer22_j`), writers 29, 26, 27, 17, 28, 16 hold
  the common words `binB, wordB, cy, rx, s, sL` of `EntryLevelWords.levelWords` at the
  level state, writer 21 the table width, writer 22 is blank (owner-5
  `EntryLevelWords.exit_writer_words` with the level-0 terms replaced).
-/

namespace EthInapproximability.CurrentPaper.EntryLevelJBank

set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Ready OuterLevel0Prep
open LevelJRows LevelJPersist LevelJReady LevelJPrep EntryPrepBudget EntryLayout
open Construction MatrixStage4Codes MatrixStage4Digits MatrixMaterialization

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The level-`j` prep exit bank (the start bank of `RoundP.Writer22SpecJ` on `HStack`). -/
noncomputable abbrev S0J (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix)
    (mS : WeightedRawWords.Aux → List Bool) (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool) :
    HStack → List Bool :=
  exitBankJ G c b yb lv Mx (G4 (levelRowsBankJ G c b yb lv Mx mS F Q P))

/-- The level-`j` writer-22 word (the word of `RoundP.S22J`). -/
abbrev word22J (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix) : List Bool :=
  (ProtectedFullBankBridgeScratch.actualD G c b yb lv Mx).rawBits

/-- The level-`j` matrix word (what cell 55 holds at the physical run). -/
def matWord (Mx : Iteration.Matrix) : List Bool := rowMajor Mx.entry

/-- The common words at the level state. -/
abbrev wJ (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix) : Words :=
  EntryLevelWords.levelWords G c b yb lv Mx

theorem exit_blank_scalar_j (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix)
    (L : CStack → List Bool) (x : WeightedScalarComplete.Stack) (hx : x ∉ keepS) :
    exitBankJ G c b yb lv Mx (G4 L) (EntryExitBlank.scalarCell x) = [] := by
  show BitMachineClearBank.cleared cells2 (G3 L) (Sum.inl (Sum.inl x)) = []
  rw [BitMachineClearBank.cleared_foreign _ _ _ (by
    intro i hi
    fin_cases i <;> cases hi)]
  show Function.update (G2 L) dstC _ (Sum.inl (Sum.inl x)) = _
  rw [Function.update_of_ne (by intro h; cases h)]
  show Function.update (G1 L) dstR _ (Sum.inl (Sum.inl x)) = _
  rw [Function.update_of_ne (by intro h; cases h)]
  exact clean_scalar _ x hx

theorem exit_blank_save_j (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix)
    (L : CStack → List Bool) (j : Fin 7) :
    exitBankJ G c b yb lv Mx (G4 L) (saveCell j) = [] := by
  show BitMachineClearBank.cleared cells2 (G3 L) (Sum.inl (Sum.inr (Sum.inl j))) = []
  rw [BitMachineClearBank.cleared_foreign _ _ _ (by
    intro i hi
    fin_cases i <;> cases hi)]
  show Function.update (G2 L) dstC _ (Sum.inl (Sum.inr (Sum.inl j))) = _
  rw [Function.update_of_ne (by intro h; cases h)]
  show Function.update (G1 L) dstR _ (Sum.inl (Sum.inr (Sum.inl j))) = _
  rw [Function.update_of_ne (by intro h; cases h)]
  exact clean_save _ j

theorem exit_blank_N_j (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix)
    (L : CStack → List Bool) :
    exitBankJ G c b yb lv Mx (G4 L) (mcell .N) = [] := by
  show BitMachineClearBank.cleared cells2 (G3 L) (Sum.inl (mc .N)) = []
  rw [BitMachineClearBank.cleared_foreign _ _ _ (by
    intro i hi
    fin_cases i <;> cases hi)]
  show Function.update (G2 L) dstC _ (Sum.inl (mc .N)) = _
  rw [Function.update_of_ne (by intro h; cases h)]
  show Function.update (G1 L) dstR _ (Sum.inl (mc .N)) = _
  rw [Function.update_of_ne (by intro h; cases h)]
  exact clean_N _

theorem exit_blank_src_j (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix)
    (L : CStack → List Bool) (i : Fin 2) :
    exitBankJ G c b yb lv Mx (G4 L) (srcCell i) = [] := by
  show BitMachineClearBank.cleared cells2 (G3 L) (Sum.inl (mc (.nat 3 i.val))) = []
  fin_cases i
  · exact BitMachineClearBank.cleared_bank cells2 (G3 L) 0
  · exact BitMachineClearBank.cleared_bank cells2 (G3 L) 1

theorem exit_blank_admin_j (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix)
    (L : CStack → List Bool) (i : Fin 3) :
    exitBankJ G c b yb lv Mx (G4 L) (adminCell i) = [] := by
  show BitMachineClearBank.cleared cells2 (G3 L) (Sum.inr (Sum.inl i)) = []
  rw [BitMachineClearBank.cleared_foreign _ _ _ (by
    intro j hj
    fin_cases j <;> cases hj)]
  show Function.update (G2 L) dstC _ (Sum.inr (Sum.inl i)) = _
  rw [Function.update_of_ne (by intro h; cases h)]
  show Function.update (G1 L) dstR _ (Sum.inr (Sum.inl i)) = _
  rw [Function.update_of_ne (by intro h; cases h)]
  rfl

theorem exit_blank_extra_j (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix)
    (L : CStack → List Bool) (e : MatrixTableWriter.Extra) (hr : e ≠ .rows) (hc : e ≠ .cols) :
    exitBankJ G c b yb lv Mx (G4 L) (extraCell e) = [] := by
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

/-- Every known-blank cell of owner-6's family is blank at the level-`j` prep exit. -/
theorem exit_blank_all_j (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix)
    (L : CStack → List Bool) (z : BlankIdx) :
    exitBankJ G c b yb lv Mx (G4 L) (blankCell z) = [] := by
  rcases z with x | y | u | d | j | u | i | i | e
  · exact exit_blank_scalar_j G c b yb lv Mx L x.1 x.2
  · rfl
  · rfl
  · rfl
  · exact exit_blank_save_j G c b yb lv Mx L j
  · exact exit_blank_N_j G c b yb lv Mx L
  · exact exit_blank_src_j G c b yb lv Mx L i
  · exact exit_blank_admin_j G c b yb lv Mx L i
  · exact exit_blank_extra_j G c b yb lv Mx L e.1 e.2.1 e.2.2

theorem exit_blank_nw_j (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix)
    (L : CStack → List Bool) (z : EntryTailEmbed.NWIdx) :
    exitBankJ G c b yb lv Mx (G4 L) (EntryTailEmbed.nwMap z) = [] :=
  exit_blank_all_j G c b yb lv Mx L (EntryTailEmbed.toBlank z)

/-- The named matrix-word cell `oCell` is blank at the level-`j` prep exit. -/
theorem exit_blank_oCell_j (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix)
    (L : CStack → List Bool) :
    exitBankJ G c b yb lv Mx (G4 L) EntrySeedSpec.oCell = [] :=
  exit_blank_all_j G c b yb lv Mx L EntrySeedSpec.zO

theorem exit_writer_cell_j (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix)
    (mS : WeightedRawWords.Aux → List Bool)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool)
    (hf : levelFactsJ G c b yb lv Mx mS F Q P) (k : Fin 64)
    (hk : ∀ j, MatrixWeightedOrderPreparation.slots j ≠ k) (hk22 : k ≠ 22) :
    S0J G c b yb lv Mx mS F Q P (wcell k) =
      MatrixWeightedEntryController.persistentBank
        (ProtectedFullBankBridgeScratch.actualD G c b yb lv Mx) k := by
  have hw : (Sum.inl (Sum.inl k) : MatrixWeightedOrderWriter.Stack) ≠
      Sum.inl (Sum.inl 22) := by
    intro h
    exact hk22 (Sum.inl.inj (Sum.inl.inj h))
  have h := ready_writer_j G c b yb lv Mx mS F Q P hf (.inl (.inl k)) hw
  show G4 (levelRowsBankJ G c b yb lv Mx mS F Q P) (wEmb (.inl (.inl k))) = _
  rw [h]
  show MatrixWeightedOrderPreparation.sourceBank _ _ _ _ k = _
  exact WeightedLevel0Target.sb_other _ _ _ _ k hk

theorem exit_writer_words_j (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix)
    (mS : WeightedRawWords.Aux → List Bool)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool)
    (hf : levelFactsJ G c b yb lv Mx mS F Q P) :
    let S := S0J G c b yb lv Mx mS F Q P
    S (wcell 29) = rep (wJ G c b yb lv Mx).binB ∧
    S (wcell 26) = rep (wJ G c b yb lv Mx).wordB ∧
    S (wcell 27) = rep (wJ G c b yb lv Mx).cy ∧
    S (wcell 17) = rep (wJ G c b yb lv Mx).rx ∧
    S (wcell 28) = rep (wJ G c b yb lv Mx).s ∧
    S (wcell 16) = rep (wJ G c b yb lv Mx).sL ∧
    S (wcell 21) = rep (cols (Iteration.a G c b yb lv Mx) (Iteration.s G c b yb lv Mx)
      (Iteration.q₂ G c b yb lv Mx) Mx.columns) ∧
    S (wcell 22) = [] := by
  dsimp only
  have pb : ∀ (d : MatrixWeightedEntryController.Input),
      MatrixWeightedEntryController.persistentBank d 29 = List.replicate d.binBase true ∧
      MatrixWeightedEntryController.persistentBank d 26 = List.replicate d.wordBase true ∧
      MatrixWeightedEntryController.persistentBank d 27 = List.replicate d.cy true ∧
      MatrixWeightedEntryController.persistentBank d 17 = List.replicate d.rx true ∧
      MatrixWeightedEntryController.persistentBank d 28 = List.replicate d.s true ∧
      MatrixWeightedEntryController.persistentBank d 16 =
        List.replicate d.stagePrefixRows true ∧
      MatrixWeightedEntryController.persistentBank d 21 = List.replicate d.rawWidth true := by
    intro d
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [MatrixWeightedEntryController.persistentBank]
  obtain ⟨p29, p26, p27, p17, p28, p16, p21⟩ :=
    pb (ProtectedFullBankBridgeScratch.actualD G c b yb lv Mx)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [exit_writer_cell_j G c b yb lv Mx mS F Q P hf 29 (by decide) (by decide), p29]; rfl
  · rw [exit_writer_cell_j G c b yb lv Mx mS F Q P hf 26 (by decide) (by decide), p26]; rfl
  · rw [exit_writer_cell_j G c b yb lv Mx mS F Q P hf 27 (by decide) (by decide), p27]; rfl
  · rw [exit_writer_cell_j G c b yb lv Mx mS F Q P hf 17 (by decide) (by decide), p17]; rfl
  · rw [exit_writer_cell_j G c b yb lv Mx mS F Q P hf 28 (by decide) (by decide), p28]; rfl
  · rw [exit_writer_cell_j G c b yb lv Mx mS F Q P hf 16 (by decide) (by decide), p16]; rfl
  · rw [exit_writer_cell_j G c b yb lv Mx mS F Q P hf 21 (by decide) (by decide), p21]; rfl
  · exact ready_writer22_j G c b yb lv Mx mS F Q P

#print axioms exit_blank_all_j
#print axioms exit_blank_nw_j
#print axioms exit_blank_oCell_j
#print axioms exit_writer_cell_j
#print axioms exit_writer_words_j

end EthInapproximability.CurrentPaper.EntryLevelJBank
