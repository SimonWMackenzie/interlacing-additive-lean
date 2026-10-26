import EthInapproximability.CurrentPaper.EntryLevelJBank
import EthInapproximability.CurrentPaper.EntryTailClear
import EthInapproximability.CurrentPaper.EntryLevelDerived

/-!
# Level-j entry lane, segment 2: the embedded tail and the charged clear at level `j`

Lane owner:b-entry-levelj-1 (Paper B, unit 2, CP-ITER). The level-`j` analogues of owner-6
`EntryTailEmbed.embedded_tail` and `EntryTailClear.clear_region` / `writer22_from_of_prep`,
at an ARBITRARY level state `(b, yb, lv, Mx)` with master region `mS`, on the admitted
level-`j` prep exit bank `exitBankJ … (G4 (levelRowsBankJ …))` (`EntryLevelJBank.S0J`).

The programs are owner-6's, reused BY EXACT NAME (`EntryTailEmbed.tailProgram`,
`EntryTailClear.clearProgram`, `EntryTailClear.tailClear`, the cell maps `tailEmb`,
`regionCells`, `nwMap`). Only the bank facts change:

* `embedded_tail_j`: `EntryLevelWords.level_raw_table_writer22` at the level-`j` parameters
  `(c, b, yb, lv, Mx)` — the word written into writer 22 is LITERALLY
  `(ProtectedFullBankBridgeScratch.actualD G c b yb lv Mx).rawBits`, the word of
  `RoundP.S22J` — run through `tailEmb` with the level writer as its writer bank
  (writer 22 blank by `LevelJReady.ready_writer22_j`);
* `clear_region_j`: the admitted pop clear of the tail region returns every region cell to
  its level-`j` exit value (blank, `exit_blank_nw_j`), leaving writer 22 = the table word;
* `writer22_from_of_prepJ`: from the single preparation interface `PrepSpecJ W` (from the
  level-`j` exit bank with the matrix word in `oCell` to the tail's start bank), the program
  `W ; tailClear` halts on `update S0J w22 word22J` (= `RoundP.S22J` on `HStack`).
-/

namespace EthInapproximability.CurrentPaper.EntryTailJ

set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Ready OuterLevel0Prep
open LevelJRows LevelJPersist LevelJReady LevelJPrep
open EntryPrepBudget EntryTailEmbed EntryTailClear EntryLevelJBank
open Construction MatrixStage4Codes MatrixStage4Digits MatrixMaterialization

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The level-`j` table input record (owner-5 `EntryLevelDerived.d0` at the level state). -/
abbrev d0J (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix) :=
  ProtectedFullBankBridgeScratch.actualD G c b yb lv Mx

theorem level_derived_values_j (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix) :
    let d := d0J G c b yb lv Mx
    let w := wJ G c b yb lv Mx
    DerivedScalars.rep (d.s - 1) = EntryLayout.rep w.sM1 ∧
    DerivedScalars.rep (d.cy ^ (d.s + 1)) = EntryLayout.rep w.cyPow1 ∧
    DerivedScalars.rep (d.binBase ^ d.s) = EntryLayout.rep w.binPowS ∧
    DerivedScalars.rep (d.stagePrefixRows + (d.nv + d.nb) * d.rx) =
      EntryLayout.rep (rows w.s w.L d.nv d.nb w.rx) := by
  intro d w
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The level writer bank of the level-`j` prep exit. -/
noncomputable def WlvlJ (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix)
    (mS : WeightedRawWords.Aux → List Bool)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool) :
    Fin 64 → List Bool :=
  fun k => S0J G c b yb lv Mx mS F Q P (wcell k)

/-- The fixed common-word bank of the level-`j` table. -/
noncomputable abbrev bnkJ (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix) :=
  EntryRunsRaw.cellBank (EntryLevelWords.levelWords G c b yb lv Mx)

/-- The level-`j` table dimensions. -/
abbrev r0J (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix) : ℕ :=
  rows (Iteration.s G c b yb lv Mx) (Iteration.labels G c b yb lv Mx)
    (GraphVectors.vertexCount V (Iteration.s G c b yb lv Mx))
    (GraphVectors.auxiliaryCount (Iteration.s G c b yb lv Mx)) Mx.rows
abbrev c0J (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix) : ℕ :=
  cols (Iteration.a G c b yb lv Mx) (Iteration.s G c b yb lv Mx)
    (Iteration.q₂ G c b yb lv Mx) Mx.columns

/-- The tail clock at level `j` (literally the bound of `embedded_tail_j`). -/
noncomputable def tailBoundJ (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix) : ℕ :=
  MatrixTableWriter.writerBound (r0J G c b yb lv Mx) (c0J G c b yb lv Mx)
      (EntryRunsRaw.tableT Mx.entry
        (lt_of_lt_of_le (by decide : 0 < 4) (Iteration.bins_ge_four G c b yb lv Mx))
        (Iteration.secondFamily G c b yb lv Mx)
        (GraphVectors.itemOrder G (Iteration.s G c b yb lv Mx))
        (GraphVectors.vectors G (Iteration.s G c b yb lv Mx))
        (GraphVectors.supportCap G
          (le_trans (by decide : 3 ≤ 4) (Iteration.bins_ge_four G c b yb lv Mx)))) +
    (2 * (r0J G c b yb lv Mx * c0J G c b yb lv Mx) + 2) + 1

/-- The tail's start bank on the level stack, at level `j`. -/
noncomputable def tailStartJ (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix)
    (mS : WeightedRawWords.Aux → List Bool)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool) :
    HStack → List Bool :=
  bank tailEmb (S0J G c b yb lv Mx mS F Q P)
    (RawTableTail.startBank (bnkJ G c b yb lv Mx) (r0J G c b yb lv Mx) (c0J G c b yb lv Mx)
      (WlvlJ G c b yb lv Mx mS F Q P))

theorem embedded_tail_j (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix)
    (mS : WeightedRawWords.Aux → List Bool)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool)
    (hf : levelFactsJ G c b yb lv Mx mS F Q P) :
    ∃ t ≤ tailBoundJ G c b yb lv Mx,
      ((advance tailProgram)^[t])
        (⟨some RawTableTail.startLabel, RawTableTail.startControl EntryRunsRaw.startControl,
          tailStartJ G c b yb lv Mx mS F Q P⟩ :
          TM2.Cfg (fun _ : HStack => Bool) _ _) =
        ⟨none, ((EntryRunsRaw.startControl, none), none),
          bank tailEmb (S0J G c b yb lv Mx mS F Q P)
            (RawTableTail.exitBank (bnkJ G c b yb lv Mx) (r0J G c b yb lv Mx)
              (c0J G c b yb lv Mx) (WlvlJ G c b yb lv Mx mS F Q P) (word22J G c b yb lv Mx))⟩ := by
  have hW22 : WlvlJ G c b yb lv Mx mS F Q P 22 = [] :=
    (exit_writer_words_j G c b yb lv Mx mS F Q P hf).2.2.2.2.2.2.2
  obtain ⟨t, ht, hr, -⟩ := EntryLevelWords.level_raw_table_writer22 G c b yb lv Mx
    (WlvlJ G c b yb lv Mx mS F Q P) hW22
  refine ⟨t, ht, ?_⟩
  have := BitMachineStackRun.run tailEmb (S0J G c b yb lv Mx mS F Q P)
    (RawTableTail.program EntryRunsRaw.csProgram EntryRunsRaw.startLabel EntryRunsRaw.startControl)
    ⟨some RawTableTail.startLabel, RawTableTail.startControl EntryRunsRaw.startControl,
      RawTableTail.startBank (bnkJ G c b yb lv Mx) (r0J G c b yb lv Mx) (c0J G c b yb lv Mx)
        (WlvlJ G c b yb lv Mx mS F Q P)⟩ t
  rw [hr] at this
  exact this

/-- The clear clock at level `j`. -/
noncomputable def clearBoundJ (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix) : ℕ :=
  (∑ i : Fin nR, (RawTableTail.exitBank (bnkJ G c b yb lv Mx) (r0J G c b yb lv Mx)
    (c0J G c b yb lv Mx) (fun _ => [])
    (word22J G c b yb lv Mx) (regTail ((Fintype.equivFin Region).symm i))).length) + nR + 2

theorem clear_region_j (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix)
    (mS : WeightedRawWords.Aux → List Bool)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool) :
    let S := S0J G c b yb lv Mx mS F Q P
    let X := bank tailEmb S (RawTableTail.exitBank (bnkJ G c b yb lv Mx) (r0J G c b yb lv Mx)
      (c0J G c b yb lv Mx) (WlvlJ G c b yb lv Mx mS F Q P) (word22J G c b yb lv Mx))
    ((advance clearProgram)^[clearBoundJ G c b yb lv Mx])
        (⟨some 0, ((), none), X⟩ : TM2.Cfg (fun _ : HStack => Bool) _ _) =
      ⟨none, ((), none), Function.update S OuterLevel0Full.w22 (word22J G c b yb lv Mx)⟩ := by
  intro S X
  have hterm : ∀ i : Fin nR,
      (RawTableTail.exitBank (bnkJ G c b yb lv Mx) (r0J G c b yb lv Mx) (c0J G c b yb lv Mx)
        (fun _ => [])
        (word22J G c b yb lv Mx) (regTail ((Fintype.equivFin Region).symm i))).length =
      (X (regionCells i)).length := by
    intro i
    show _ = (bank tailEmb S _ (nwMap (regionEmb ((Fintype.equivFin Region).symm i)))).length
    rw [← tailEmb_regTail, bank_at, exit_region_indep _ _ _ _ (WlvlJ G c b yb lv Mx mS F Q P)]
  have hsum : clearBoundJ G c b yb lv Mx = (∑ i, (X (regionCells i)).length) + nR + 2 := by
    unfold clearBoundJ
    rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  have key : BitMachineClearBank.cleared regionCells X =
      Function.update S OuterLevel0Full.w22 (word22J G c b yb lv Mx) := by
    funext x
    by_cases hx : ∃ i, regionCells i = x
    · obtain ⟨i, rfl⟩ := hx
      rw [BitMachineClearBank.cleared_bank, w22_eq,
        Function.update_of_ne (show regionCells i ≠ wcell 22 from nwMap_ne_wcell _ _)]
      exact (exit_blank_nw_j G c b yb lv Mx _ _).symm
    · rw [BitMachineClearBank.cleared_foreign _ _ _ (fun i hi => hx ⟨i, hi⟩)]
      by_cases hy : ∃ y, tailEmb y = x
      · obtain ⟨y, rfl⟩ := hy
        rcases y with a | k | i
        · exact absurd ⟨Fintype.equivFin Region (.inl a), by
            simp [regionCells]; rfl⟩ hx
        · show bank tailEmb S _ (tailEmb (.inr (.inl k))) = _
          rw [bank_at]
          show Function.update (WlvlJ G c b yb lv Mx mS F Q P) 22 (word22J G c b yb lv Mx) k = _
          by_cases hk : k = 22
          · subst hk
            rw [Function.update_self, w22_eq]
            show _ = Function.update S (wcell 22) _ (wcell 22)
            rw [Function.update_self]
          · rw [Function.update_of_ne hk, w22_eq]
            rw [Function.update_of_ne (show tailEmb (.inr (.inl k)) ≠ wcell 22 from fun h =>
              hk (wc_inj (Sum.inl.inj (Sum.inl.inj h))))]
            rfl
        · exact absurd ⟨Fintype.equivFin Region (.inr i), by
            simp [regionCells]; rfl⟩ hx
      · simp only [not_exists] at hy
        show bank tailEmb S (RawTableTail.exitBank _ _ _ _ _) x = _
        rw [bank_outside _ _ _ _ (by rintro ⟨y, hy'⟩; exact hy y hy')]
        rw [Function.update_of_ne (by
          intro h
          rw [w22_eq] at h
          exact hy (.inr (.inl 22)) h.symm)]
  rw [hsum, show clearProgram = WeightedRawWords.clearProgram regionCells from rfl,
    WeightedRawWords.clear_run regionCells regionCells_inj X, key]

/-- The level-`j` prep exit bank with the matrix word in the named cell `oCell`. -/
noncomputable def S0J' (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix)
    (mS : WeightedRawWords.Aux → List Bool)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool) :
    HStack → List Bool :=
  Function.update (S0J G c b yb lv Mx mS F Q P) EntrySeedSpec.oCell (matWord Mx)

/-- The level-`j` preparation interface (owner-6 `PrepSpec` at level `j`). -/
def PrepSpecJ {LW VW : Type} (W : LW → TM2.Stmt (fun _ : HStack => Bool) LW VW) (w₀ : LW)
    (v₀ : VW) (T : ℕ) (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix)
    (mS : WeightedRawWords.Aux → List Bool) : Prop :=
  ∀ (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool),
    levelFactsJ G c b yb lv Mx mS F Q P →
    ∃ t ≤ T, ∃ v₁ : VW,
      ((advance W)^[t]) ⟨some w₀, v₀, S0J' G c b yb lv Mx mS F Q P⟩ =
        ⟨none, v₁, tailStartJ G c b yb lv Mx mS F Q P⟩

/-- The level-`j` writer-22 interface on `HStack` (owner-6 `Writer22From zO` at level `j`):
from the exit bank with the matrix word in `oCell`, halt on `RoundP.S22J`'s bank. -/
def Writer22FromJ {LW VW : Type} (W : LW → TM2.Stmt (fun _ : HStack => Bool) LW VW) (w₀ : LW)
    (v₀ : VW) (T : ℕ) (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix)
    (mS : WeightedRawWords.Aux → List Bool) : Prop :=
  ∀ (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool),
    levelFactsJ G c b yb lv Mx mS F Q P →
    ∃ t ≤ T, ∃ v₁ : VW,
      ((advance W)^[t]) ⟨some w₀, v₀, S0J' G c b yb lv Mx mS F Q P⟩ =
        ⟨none, v₁, Function.update (S0J G c b yb lv Mx mS F Q P) OuterLevel0Full.w22
          (word22J G c b yb lv Mx)⟩

theorem writer22_from_of_prepJ (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix)
    (mS : WeightedRawWords.Aux → List Bool) {LW VW : Type}
    (W : LW → TM2.Stmt (fun _ : HStack => Bool) LW VW) (w₀ : LW) (v₀ : VW) (T : ℕ)
    (hP : PrepSpecJ W w₀ v₀ T G c b yb lv Mx mS) :
    Writer22FromJ
      (BitMachineRawSequence.program W tailClear
        (BitMachineRawSequence.leftLabel RawTableTail.startLabel) v₀
        (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool))))
      (BitMachineRawSequence.leftLabel w₀)
      (v₀, (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool))))
      (T + (tailBoundJ G c b yb lv Mx + clearBoundJ G c b yb lv Mx + 1) + 1) G c b yb lv Mx mS := by
  intro F Q P hf
  obtain ⟨tp, htp, vp, hp⟩ := hP F Q P hf
  obtain ⟨tt, htt, ht⟩ := embedded_tail_j G c b yb lv Mx mS F Q P hf
  have hc := clear_region_j G c b yb lv Mx mS F Q P
  obtain ⟨u, hu, hr⟩ := BitMachineRawSequence.runs tailProgram clearProgram
    RawTableTail.startLabel (0 : Fin (nR + 2))
    (RawTableTail.startControl EntryRunsRaw.startControl) ((EntryRunsRaw.startControl, none), none)
    ((), none) ((), none)
    (tailStartJ G c b yb lv Mx mS F Q P) _ _ tt (clearBoundJ G c b yb lv Mx) ht hc
  obtain ⟨t, ht2, hr2⟩ := BitMachineRawSequence.runs W tailClear w₀
    (BitMachineRawSequence.leftLabel RawTableTail.startLabel) v₀ vp
    (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool)))
    (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool)))
    _ _ _ tp u hp hr
  refine ⟨t, ?_, (v₀, (RawTableTail.startControl EntryRunsRaw.startControl, ((), none))), ?_⟩
  · omega
  · exact hr2

#print axioms level_derived_values_j
#print axioms embedded_tail_j
#print axioms clear_region_j
#print axioms writer22_from_of_prepJ

end EthInapproximability.CurrentPaper.EntryTailJ
