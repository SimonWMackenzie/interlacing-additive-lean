import EthInapproximability.CurrentPaper.EntryRunsRaw
import EthInapproximability.CurrentPaper.OuterLevel0Full
import EthInapproximability.CurrentPaper.WeightedLevel0Target

/-!
# Segments 5/6 (partial): the actual level parameters and the level exit bank

Lane owner:b-stage4-entry-program-5 (Paper B, unit 2, map item 3).

* `levelWords`: the 19 common words at the ACTUAL level parameters (the same
  `a, s, q, L, nv, nb, family, order, vectors` as the admitted
  `ProtectedFullBankBridgeScratch.actualD`), `R = M.entry`.
* `level_raw_table_writer22`: `raw_table_writer22_actual` at those parameters;
  the word written into writer 22 is LITERALLY `(actualD …).rawBits`, the
  value `OuterLevel0Full.Writer22Spec` demands (same object, no conversion).
* `exit_writer_words`: at the level-0 prep exit bank
  `OuterLevel0Prep.exitBank G n c (G4 (level0RowsBank M G n c F Q P))`,
  writer cells 29, 26, 27, 17, 28, 16 hold EXACTLY the common words
  `binB, wordB, cy, rx, s, sL` of `levelWords` at level 0, writer 21 holds the
  unary table width `cols a s q cy`, and writer 22 is blank.

NOT claimed: the program that prepares the remaining common words and the
unary raw row count, nor its embedding into the level stack (see CHECKPOINT).
-/

set_option maxRecDepth 16384

namespace EthInapproximability.CurrentPaper.EntryLevelWords

open Turing BitMachineEncoding BitMachineStackEmbedding EntryLayout
open Construction MatrixStage4Codes MatrixStage4Digits MatrixMaterialization
open EthInapproximability.ParameterizedNP.GuardedSourceGraph

variable {VG EG : Type} [Fintype VG] [DecidableEq VG] [Fintype EG] [DecidableEq EG]

/-- The 19 common words at the actual level parameters. -/
def levelWords (G : EndpointGraph VG EG) (c b y lvl : ℕ) (M : Iteration.Matrix) : Words :=
  TemplateEntry.actualWords (Iteration.a G c b y lvl M) (Iteration.s G c b y lvl M)
    (Iteration.q₂ G c b y lvl M) (Iteration.labels G c b y lvl M) M.columns M.rows M.entry
    (Iteration.secondFamily G c b y lvl M)
    (rowMajor (GraphVectors.vectors G (Iteration.s G c b y lvl M)))

/-- The raw Stage-4 table producer at the actual level parameters: writer 22
receives exactly the admitted `(actualD …).rawBits`. -/
theorem level_raw_table_writer22 (G : EndpointGraph VG EG) (c b y lvl : ℕ)
    (M : Iteration.Matrix) (W : Fin 64 → List Bool) (hblank : W 22 = []) :
    let a := Iteration.a G c b y lvl M
    let s := Iteration.s G c b y lvl M
    let q := Iteration.q₂ G c b y lvl M
    let L := Iteration.labels G c b y lvl M
    let nv := GraphVectors.vertexCount VG s
    let nb := GraphVectors.auxiliaryCount s
    let hs : 0 < s := lt_of_lt_of_le (by decide : 0 < 4)
      (Iteration.bins_ge_four G c b y lvl M)
    let order := GraphVectors.itemOrder G s
    let cap := GraphVectors.supportCap G
      (le_trans (by decide : 3 ≤ 4) (Iteration.bins_ge_four G c b y lvl M))
    let bank := EntryRunsRaw.cellBank (levelWords G c b y lvl M)
    let T := EntryRunsRaw.tableT M.entry hs (Iteration.secondFamily G c b y lvl M) order
      (GraphVectors.vectors G s) cap
    let word := (ProtectedFullBankBridgeScratch.actualD G c b y lvl M).rawBits
    ∃ t ≤ MatrixTableWriter.writerBound (rows s L nv nb M.rows) (cols a s q M.columns) T +
        (2 * (rows s L nv nb M.rows * cols a s q M.columns) + 2) + 1,
      ((advance (RawTableTail.program EntryRunsRaw.csProgram EntryRunsRaw.startLabel
          EntryRunsRaw.startControl))^[t])
        (⟨some RawTableTail.startLabel, RawTableTail.startControl EntryRunsRaw.startControl,
          RawTableTail.startBank bank (rows s L nv nb M.rows) (cols a s q M.columns) W⟩ :
          TM2.Cfg (fun _ : RawTableTail.Stack EntryRunsRaw.K => Bool) _ _) =
        ⟨none, ((EntryRunsRaw.startControl, none), none),
          RawTableTail.exitBank bank (rows s L nv nb M.rows) (cols a s q M.columns) W word⟩ ∧
      RawTableTail.exitBank bank (rows s L nv nb M.rows) (cols a s q M.columns) W word
          (Sum.inr (Sum.inl 22)) = word ∧
      (∀ k : Fin 64, k ≠ 22 →
        RawTableTail.exitBank bank (rows s L nv nb M.rows) (cols a s q M.columns) W word
          (Sum.inr (Sum.inl k)) = W k) ∧
      (∀ k : Fin EntryRunsRaw.K,
        RawTableTail.exitBank bank (rows s L nv nb M.rows) (cols a s q M.columns) W word
          (Sum.inl (Sum.inl (Sum.inl k))) = bank k) := by
  intro a s q L nv nb hs order cap bank T word
  exact EntryRunsRaw.raw_table_writer22_actual M.entry hs
    (Iteration.secondFamily G c b y lvl M) order (GraphVectors.vectors G s) cap W hblank

#print axioms level_raw_table_writer22

section exit

open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Ready OuterLevel0Prep

variable (Mm : BitMachine.Machine)
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The level-0 parameters `(b, y, lvl, M)` of the prep exit. -/
abbrev w0 (G : EndpointGraph V E) (n c : ℕ) : Words :=
  levelWords G c (EffectiveIteration.sourceDepth n)
    (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
    (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix

theorem exit_writer_cell (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool)
    (hf : level0Facts Mm G n c F Q P) (k : Fin 64)
    (hk : ∀ j, MatrixWeightedOrderPreparation.slots j ≠ k) (hk22 : k ≠ 22) :
    exitBank G n c (G4 (level0RowsBank Mm G n c F Q P)) (wcell k) =
      MatrixWeightedEntryController.persistentBank
        (ProtectedFullBankBridgeScratch.actualD G c (EffectiveIteration.sourceDepth n)
          (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
          (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix) k := by
  have hw : (Sum.inl (Sum.inl k) : MatrixWeightedOrderWriter.Stack) ≠
      Sum.inl (Sum.inl 22) := by
    intro h
    exact hk22 (Sum.inl.inj (Sum.inl.inj h))
  have h := ready_writer Mm G n c F Q P hf (.inl (.inl k)) hw
  show G4 (level0RowsBank Mm G n c F Q P) (wEmb (.inl (.inl k))) = _
  rw [h]
  show MatrixWeightedOrderPreparation.sourceBank _ _ _ _ k = _
  exact WeightedLevel0Target.sb_other _ _ _ _ k hk

theorem exit_writer_words (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool)
    (hf : level0Facts Mm G n c F Q P) :
    let S := exitBank G n c (G4 (level0RowsBank Mm G n c F Q P))
    let M := (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix
    let b := EffectiveIteration.sourceDepth n
    let y := (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget
    S (wcell 29) = rep (w0 G n c).binB ∧
    S (wcell 26) = rep (w0 G n c).wordB ∧
    S (wcell 27) = rep (w0 G n c).cy ∧
    S (wcell 17) = rep (w0 G n c).rx ∧
    S (wcell 28) = rep (w0 G n c).s ∧
    S (wcell 16) = rep (w0 G n c).sL ∧
    S (wcell 21) = rep (cols (Iteration.a G c b y 0 M) (Iteration.s G c b y 0 M)
      (Iteration.q₂ G c b y 0 M) M.columns) ∧
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
  obtain ⟨p29, p26, p27, p17, p28, p16, p21⟩ := pb (ProtectedFullBankBridgeScratch.actualD G c
    (EffectiveIteration.sourceDepth n) (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
    (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [exit_writer_cell Mm G n c F Q P hf 29 (by decide) (by decide), p29]; rfl
  · rw [exit_writer_cell Mm G n c F Q P hf 26 (by decide) (by decide), p26]; rfl
  · rw [exit_writer_cell Mm G n c F Q P hf 27 (by decide) (by decide), p27]; rfl
  · rw [exit_writer_cell Mm G n c F Q P hf 17 (by decide) (by decide), p17]; rfl
  · rw [exit_writer_cell Mm G n c F Q P hf 28 (by decide) (by decide), p28]; rfl
  · rw [exit_writer_cell Mm G n c F Q P hf 16 (by decide) (by decide), p16]; rfl
  · rw [exit_writer_cell Mm G n c F Q P hf 21 (by decide) (by decide), p21]; rfl
  · exact ready_writer22 Mm G n c F Q P

#print axioms exit_writer_cell
#print axioms exit_writer_words

end exit

end EthInapproximability.CurrentPaper.EntryLevelWords
