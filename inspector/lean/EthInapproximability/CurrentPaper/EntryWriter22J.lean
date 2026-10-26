import EthInapproximability.CurrentPaper.EntryPrepFinal4J
import EthInapproximability.CurrentPaper.RoundP
import EthInapproximability.CurrentPaper.KShell

/-!
# Level-`j` writer 22 on the round stack `H4` from ONE premise `Family4SpecJ`

Lane owner:b-entry-levelj-1 (Paper B, unit 2, CP-ITER), segments 1 (cell-55 part) and 3.

ONE fixed program `writerJ W w₀ v₀` on `H4` (independent of `G, c, b, y, j, Mx`):

1. `copy55`: a charged copy (owner-4 `CopyFill`, temp = fresh cell 54, blank in `Dmw`) of the
   previous round's output word from the fresh cell `.inr 55` into the entry-program cell
   `oCell` (lifted `HStack` cell); cost `2 |mw| + 2`, plus the handoff. This replaces level 0's
   seed-table producer: at level `j` the matrix word is READ from cell 55, not produced.
2. `lift4 (bodyJ W w₀ v₀)`: owner-7's `prepProg4 W` (copies / derived scalars / vectors /
   power word / label division / the family program `W`) then owner-6's `tailClear`, at level
   `j` by the generated level-`j` lemmas (`prep_of_family4_j`) and this lane's
   `writer22_from_of_prepJ`; the fresh region (in particular cell 55) is untouched
   (`lift4_run`).

`writer22J_of_family4`: `Family4SpecJ W …` (+ the master fact `mS .Gw = graph bytes`) gives
`RoundP.Writer22SpecJ (writerJ W w₀ v₀) … (matWord Mx)`, the admitted per-level premise with
`mw = rowMajor Mx.entry`.
`kshell_hW_of_family4`: at the physical run (`yP`, `MP`, `mSj (mb1 M G n c)`, cell 55 =
`rowMajor (physRun j).matrix.entry`) the hypothesis `hW` of the admitted `KShell.shell_run` holds
for the fixed program `writerJ W w₀ v₀`, from `Family4SpecJ` at each level `1 ≤ j < k` and one
`T22` majorizing the explicit per-level clock; `hGw` is discharged by the admitted
`Level0Install.base1` and `StepP.mSj_ne`.
-/

namespace EthInapproximability.CurrentPaper.EntryWriter22J

set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000
set_option maxRecDepth 16384

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Ready OuterLevel0Prep
open EntryPrepBudget EntryTailEmbed EntryTailClear EntryPrepCopy EntryPrepVec
open EntryLevelJBank EntryTailJ LevelJRows LevelJPersist LevelJReady LevelJPrep EntryPrepCopyJ EntryPrepVecJ
open Level0DimsRound (H4 iH4 ext4 lift4 lift4_run)
open Level0CostRound (H2 ext)
open LevelJRound (Dmw Dmw_other)

/-! ## The charged copy cell 55 -> `oCell` -/

noncomputable def src55 : H4 := Sum.inr 55
noncomputable def tmp54 : H4 := Sum.inr 54
noncomputable def oCell4 : H4 := Sum.inl (Sum.inl EntrySeedSpec.oCell)

theorem oCell4_eq : oCell4 = iH4 EntrySeedSpec.oCell := rfl

noncomputable def jobs55 : List (H4 × List H4) := [(src55, [oCell4])]

theorem good55 : CopyFill.Good tmp54 jobs55 where
  src_not_dst := by simp [jobs55, src55, oCell4]
  dst_nodup := by simp [jobs55]
  src_temp := by simp [jobs55, src55, tmp54]
  temp_dst := by simp [jobs55, tmp54, oCell4]

noncomputable def copy55 := MultiMove.program (jobs55.map CopyFill.toJob) tmp54

theorem ext4_update (S : HStack → List Bool) (D : Fin 57 → List Bool) (x : HStack) (w : List Bool) :
    Function.update (ext4 S D) (Sum.inl (Sum.inl x)) w = ext4 (Function.update S x w) D := by
  funext y
  rcases y with (y | y) | y
  · by_cases h : y = x
    · subst h
      rw [Function.update_self]
      show w = Function.update S y w y
      rw [Function.update_self]
    · rw [Function.update_of_ne (by intro e; exact h (Sum.inl.inj (Sum.inl.inj e)))]
      show S y = Function.update S x w y
      rw [Function.update_of_ne h]
  · rw [Function.update_of_ne (by intro e; cases e)]
    rfl
  · rw [Function.update_of_ne (by intro e; cases e)]
    rfl

theorem copy55_run (X : HStack → List Bool) (mw : List Bool) (hX : X EntrySeedSpec.oCell = []) :
    ((advance copy55)^[((2 * mw.length + 2) + 0) + 1])
      (⟨some (MultiMove.startLabel (jobs55.map CopyFill.toJob)), MultiMove.initial, ext4 X (Dmw mw)⟩ :
        TM2.Cfg (fun _ : H4 => Bool) _ _) =
      ⟨none, MultiMove.initial, ext4 (Function.update X EntrySeedSpec.oCell mw) (Dmw mw)⟩ := by
  have e55 : ext4 X (Dmw mw) src55 = mw := by
    show Dmw mw 55 = mw
    unfold Dmw
    rw [Function.update_self]
  have e54 : ext4 X (Dmw mw) tmp54 = [] := Dmw_other mw 54 (by decide)
  have eo : ext4 X (Dmw mw) oCell4 = [] := hX
  have h := CopyFill.run tmp54 jobs55 good55 (ext4 X (Dmw mw)) e54 (by
    simp only [jobs55, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    exact eo)
  have hc : CopyFill.fillCost jobs55 (ext4 X (Dmw mw)) = (2 * mw.length + 2) + 0 := by
    simp only [CopyFill.fillCost, jobs55, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, e55]
  have hx : CopyFill.fill jobs55 (ext4 X (Dmw mw)) =
      ext4 (Function.update X EntrySeedSpec.oCell mw) (Dmw mw) := by
    rw [← ext4_update]
    funext y
    simp only [jobs55, CopyFill.fill, List.mem_cons, List.not_mem_nil, or_false]
    by_cases h : y = oCell4
    · rw [if_pos h, h, e55]
      show mw = Function.update (ext4 X (Dmw mw)) oCell4 mw oCell4
      rw [Function.update_self]
    · rw [if_neg h]
      show ext4 X (Dmw mw) y = Function.update (ext4 X (Dmw mw)) oCell4 mw y
      rw [Function.update_of_ne h]
  rw [hc, hx] at h
  exact h

/-! ## The fixed level-`j` writer program -/

/-- The `HStack` body: owner-7 `prepProg4 W` then owner-6 `tailClear`. -/
noncomputable def bodyJ {LW VW : Type} (W : LW → TM2.Stmt (fun _ : HStack => Bool) LW VW)
    (w₀ : LW) (v₀ : VW) :=
  BitMachineRawSequence.program (prepProg4 W w₀ v₀) tailClear
    (BitMachineRawSequence.leftLabel RawTableTail.startLabel)
    (prepInit ((MultiMove.initial, false), v₀))
    (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool)))

/-- ONE fixed program on `H4`: `copy55 ; lift4 (prepProg4 W ; tailClear)`. -/
noncomputable def writerJ {LW VW : Type} (W : LW → TM2.Stmt (fun _ : HStack => Bool) LW VW)
    (w₀ : LW) (v₀ : VW) :=
  BitMachineRawSequence.program copy55 (lift4 (bodyJ W w₀ v₀))
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (MultiMove.startLabel (copyJobs.map CopyFill.toJob)))))
    MultiMove.initial
    (prepInit ((MultiMove.initial, false), v₀),
      (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool))))

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The explicit level-`j` writer clock (copy + handoff + body + handoff). -/
noncomputable def writerBound_j (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix)
    (T : ℕ) : ℕ :=
  (((2 * (matWord Mx).length + 2) + 0) + 1) +
    (prepBound_j G c b yb lv Mx (labBound_j G c b yb lv Mx T) +
      (tailBoundJ G c b yb lv Mx + clearBoundJ G c b yb lv Mx + 1) + 1) + 1

theorem writer22J_of_family4 (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix)
    (mS : WeightedRawWords.Aux → List Bool)
    (hGw : mS .Gw = EncodedGraph.encode (EncodedETHSource.serializeGraph G)) {LW VW : Type}
    (W : LW → TM2.Stmt (fun _ : HStack => Bool) LW VW) (w₀ : LW) (v₀ : VW) (T : ℕ)
    (hF : Family4SpecJ W w₀ v₀ T G c b yb lv Mx mS) :
    RoundP.Writer22SpecJ (writerJ W w₀ v₀)
      (BitMachineRawSequence.leftLabel (MultiMove.startLabel (jobs55.map CopyFill.toJob)))
      (MultiMove.initial, (prepInit ((MultiMove.initial, false), v₀),
        (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool)))))
      (writerBound_j G c b yb lv Mx T) G c b yb lv Mx mS (matWord Mx) := by
  intro F Q P hf
  have hB := writer22_from_of_prepJ G c b yb lv Mx mS _ _ _ _
    (prep_of_family4_j G c b yb lv Mx mS hGw W w₀ v₀ T hF)
  obtain ⟨t2, ht2, v₂, h2⟩ := hB F Q P hf
  have h2' := lift4_run (bodyJ W w₀ v₀) _ _ _ _ _ _ (Dmw (matWord Mx)) t2 h2
  have h1 : ((advance copy55)^[((2 * (matWord Mx).length + 2) + 0) + 1])
      (⟨some (MultiMove.startLabel (jobs55.map CopyFill.toJob)), MultiMove.initial,
        ext4 (S0J G c b yb lv Mx mS F Q P) (Dmw (matWord Mx))⟩ : TM2.Cfg (fun _ : H4 => Bool) _ _) =
      ⟨none, MultiMove.initial, ext4 (S0J' G c b yb lv Mx mS F Q P) (Dmw (matWord Mx))⟩ :=
    copy55_run (S0J G c b yb lv Mx mS F Q P) (matWord Mx)
      (exit_blank_oCell_j G c b yb lv Mx (levelRowsBankJ G c b yb lv Mx mS F Q P))
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs copy55 (lift4 (bodyJ W w₀ v₀)) _ _ _ _ _ _
    _ _ _ _ _ h1 h2'
  refine ⟨t, ?_, _, hr⟩
  unfold writerBound_j
  omega

/-! ## Discharging `KShell.shell_run`'s `hW` -/

theorem mSj_Gw (M : BitMachine.Machine) (G : EndpointGraph V E) (n c j : ℕ) :
    StepP.mSj (Level0Install.mb1 M G n c) G c (EffectiveIteration.sourceDepth n) j .Gw =
      EncodedGraph.encode (EncodedETHSource.serializeGraph G) := by
  rw [StepP.mSj_ne _ _ _ _ _ _ (by intro h; cases h)]
  exact (Level0Install.base1 M G n c).2.2.2.2.2.2

theorem kshell_hW_of_family4 (M : BitMachine.Machine) (G : EndpointGraph V E) (n c k : ℕ)
    {LW VW : Type} (W : LW → TM2.Stmt (fun _ : HStack => Bool) LW VW) (w₀ : LW) (v₀ : VW)
    (TF T22 : ℕ)
    (hF : ∀ j, 1 ≤ j → j < k →
      Family4SpecJ W w₀ v₀ TF G c (EffectiveIteration.sourceDepth n)
        (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
        (StepP.MP G c (EffectiveIteration.sourceDepth n) j)
        (StepP.mSj (Level0Install.mb1 M G n c) G c (EffectiveIteration.sourceDepth n) j))
    (hT : ∀ j, 1 ≤ j → j < k →
      writerBound_j G c (EffectiveIteration.sourceDepth n)
        (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
        (StepP.MP G c (EffectiveIteration.sourceDepth n) j) TF ≤ T22) :
    ∀ j, 1 ≤ j → j < k →
      RoundP.Writer22SpecJ (writerJ W w₀ v₀)
        (BitMachineRawSequence.leftLabel (MultiMove.startLabel (jobs55.map CopyFill.toJob)))
        (MultiMove.initial, (prepInit ((MultiMove.initial, false), v₀),
          (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool)))))
        T22 G c (EffectiveIteration.sourceDepth n)
        (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
        (StepP.MP G c (EffectiveIteration.sourceDepth n) j)
        (StepP.mSj (Level0Install.mb1 M G n c) G c (EffectiveIteration.sourceDepth n) j)
        (MatrixMaterialization.rowMajor
          (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
            (Iteration.seedState (EffectiveIteration.sourceDepth n)) j).matrix.entry) := by
  intro j hj1 hjk F Q P hf
  obtain ⟨t, ht, v, h⟩ := writer22J_of_family4 G c (EffectiveIteration.sourceDepth n)
    (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
    (StepP.MP G c (EffectiveIteration.sourceDepth n) j)
    (StepP.mSj (Level0Install.mb1 M G n c) G c (EffectiveIteration.sourceDepth n) j)
    (mSj_Gw M G n c j) W w₀ v₀ TF (hF j hj1 hjk) F Q P hf
  exact ⟨t, le_trans ht (hT j hj1 hjk), v, h⟩

#print axioms ext4_update
#print axioms copy55_run
#print axioms writer22J_of_family4
#print axioms mSj_Gw
#print axioms kshell_hW_of_family4

end EthInapproximability.CurrentPaper.EntryWriter22J
