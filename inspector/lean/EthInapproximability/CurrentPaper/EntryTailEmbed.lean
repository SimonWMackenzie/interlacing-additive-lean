import EthInapproximability.CurrentPaper.EntrySeedSpec

/-!
# Segment 6: the raw-table tail embedded in the level stack

Lane owner:b-stage4-entry-program-6 (Paper B, unit 2, map item 3).

* `NWIdx`: the known-blank cells of the prep exit that are NOT level-writer cells
  (scalar cells outside the writer image, fresh scale cells, the copy temporary, the
  double-interlace region, the save region, `N`, the source masters, the writer index
  cells, the free administration cells); `nwMap` is injective (`nwMap_inj`), avoids every
  writer cell (`nwMap_ne_wcell`) and every image is blank at the prep exit
  (`exit_blank_nw`); `card_NWIdx = 424`.
* `tailEmb : RawTableTail.Stack EntryRunsRaw.K ↪ HStack`: the tail's own writer `Fin 64`
  goes to the level writer (`wcell k`), its 248 other cells to `NWIdx` cells through ONE
  fixed classical embedding (`regionEmb`, chosen from `card 248 ≤ 424`).
* `embedded_tail`: the admitted tail (owner-5 `level_raw_table_writer22` at the level-0
  parameters) runs on the level stack with the level writer as its writer bank `W`, from
  the bank `bank tailEmb S0 (startBank …)` to `bank tailEmb S0 (exitBank …)` within the
  tail clock. The start bank is the prep exit bank with the tail region filled
  (the 19 common words, rows/cols); the preparation of that region is NOT done here.
-/

namespace EthInapproximability.CurrentPaper.EntryTailEmbed

set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Ready OuterLevel0Prep
open EntryPrepBudget
open Construction MatrixStage4Codes MatrixStage4Digits MatrixMaterialization

variable (Mm : BitMachine.Machine)
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Scalar cells outside the writer image. -/
abbrev NonWriter := {x : WeightedScalarComplete.Stack // ∀ k, WeightedColumnActualStage.writerSlots k ≠ x}

abbrev NWIdx :=
  NonWriter ⊕ (SStack ⊕ (Unit ⊕ (DStack ⊕ (Fin 7 ⊕ (Unit ⊕ (Fin 2 ⊕ (Fin 3 ⊕ ExtraFree)))))))

theorem nonWriter_not_keep (x : NonWriter) : x.1 ∉ keepS := by
  intro h
  simp only [keepS, Finset.mem_map] at h
  obtain ⟨k, -, hk⟩ := h
  exact x.2 k hk

def toBlank : NWIdx → BlankIdx
  | .inl x => .inl ⟨x.1, nonWriter_not_keep x⟩
  | .inr r => .inr r

theorem toBlank_inj : Function.Injective toBlank := by
  intro a b h
  rcases a with x | r <;> rcases b with y | r'
  · simp only [toBlank, Sum.inl.injEq, Subtype.mk.injEq] at h
    exact congrArg Sum.inl (Subtype.ext h)
  · simp [toBlank] at h
  · simp [toBlank] at h
  · simp only [toBlank, Sum.inr.injEq] at h
    exact congrArg Sum.inr h

def nwMap (z : NWIdx) : HStack := blankCell (toBlank z)

theorem nwMap_inj : Function.Injective nwMap := fun a b h => toBlank_inj (blankCell.injective h)

theorem nwMap_ne_wcell (z : NWIdx) (k : Fin 64) : nwMap z ≠ wcell k := by
  rcases z with x | r
  · intro h
    exact x.2 k (Sum.inl.inj (Sum.inl.inj (Sum.inl.inj h))).symm
  · rcases r with y | u | d | j | u | i | i | e <;> intro h <;> cases h

theorem exit_blank_nw (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool)
    (z : NWIdx) :
    exitBank G n c (G4 (level0RowsBank Mm G n c F Q P)) (nwMap z) = [] :=
  exit_blank_all Mm G n c F Q P (toBlank z)

open scoped Classical in
theorem card_nonWriter : Fintype.card NonWriter = 189 := by
  have h1 : Fintype.card NonWriter =
      Fintype.card WeightedScalarComplete.Stack - Fintype.card (Set.range WeightedColumnActualStage.writerSlots) := by
    rw [← Fintype.card_subtype_compl]
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight (fun x => by simp)
  rw [h1, Set.card_range_of_injective WeightedColumnActualStage.writerSlots.injective,
    EntryExitBlank.card_scalar, Fintype.card_fin]

open scoped Classical in
theorem card_NWIdx : Fintype.card NWIdx = 424 := by
  rw [Fintype.card_sum, card_nonWriter, Fintype.card_sum, EntryExitBlank.card_fresh, Fintype.card_sum,
    Fintype.card_unit, Fintype.card_sum, card_dstack, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_sum, Fintype.card_unit, Fintype.card_sum, Fintype.card_fin, Fintype.card_sum,
    Fintype.card_fin, card_extraFree]

abbrev K := EntryRunsRaw.K
abbrev Region := MatrixTableWriter.Stack K ⊕ Fin 2

theorem card_region : Fintype.card Region = 248 := by
  have hK : EntryRunsRaw.K = 236 := by
    simp only [EntryRunsRaw.K, Fintype.card_sum, Fintype.card_fin]
  simp only [Region, K, Fintype.card_sum, Fintype.card_fin, card_extra, hK]

open scoped Classical in
/-- A fixed classical embedding of the tail's own cells into non-writer blank cells. -/
noncomputable def regionEmb0 : Region ↪ NWIdx :=
  Classical.choice (Function.Embedding.nonempty_of_card_le (by
    rw [card_region, card_NWIdx]; decide))

/-- The tail cell of common word 12 (`Rtable`, the matrix word). -/
noncomputable def r12 : Region := .inl (.inl (.inl (EntryRunsRaw.eo (.inl 12))))

/-- The non-writer index of the named matrix-word cell `oCell`. -/
noncomputable def nwO : NWIdx := .inr (.inr (.inr (.inl EntrySeedSpec.d0)))

theorem nwMap_nwO : nwMap nwO = EntrySeedSpec.oCell := rfl

/-- ONE fixed embedding of the tail's own cells, with the matrix-word cell `r12` sent to
`oCell` (so the word produced by `EntrySeedSpec.seedProgram` is already in place). -/
noncomputable def regionEmb : Region ↪ NWIdx :=
  regionEmb0.trans (Equiv.swap (regionEmb0 r12) nwO).toEmbedding

theorem regionEmb_r12 : regionEmb r12 = nwO := by
  simp [regionEmb, Equiv.swap_apply_left]

noncomputable def tailMap : RawTableTail.Stack K → HStack
  | .inl a => nwMap (regionEmb (.inl a))
  | .inr (.inl k) => wcell k
  | .inr (.inr i) => nwMap (regionEmb (.inr i))

theorem tailMap_inj : Function.Injective tailMap := by
  intro a b h
  rcases a with a | k | i <;> rcases b with b | k' | i'
  · exact congrArg Sum.inl (Sum.inl.inj (regionEmb.injective (nwMap_inj h)))
  · exact absurd h (nwMap_ne_wcell _ _)
  · cases regionEmb.injective (nwMap_inj h)
  · exact absurd h.symm (nwMap_ne_wcell _ _)
  · exact congrArg (fun k => Sum.inr (Sum.inl k)) (wc_inj (Sum.inl.inj (Sum.inl.inj h)))
  · exact absurd h.symm (nwMap_ne_wcell _ _)
  · cases regionEmb.injective (nwMap_inj h)
  · exact absurd h (nwMap_ne_wcell _ _)
  · exact congrArg (fun i => Sum.inr (Sum.inr i)) (Sum.inr.inj (regionEmb.injective (nwMap_inj h)))

noncomputable def tailEmb : RawTableTail.Stack K ↪ HStack := ⟨tailMap, tailMap_inj⟩

/-- The embedded tail program. -/
noncomputable def tailProgram := fun l => stackStmt tailEmb
  (RawTableTail.program EntryRunsRaw.csProgram EntryRunsRaw.startLabel EntryRunsRaw.startControl l)

/-- The level writer bank of the prep exit. -/
noncomputable def Wlvl (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool) :
    Fin 64 → List Bool :=
  fun k => EntryWriter22Split.S0 Mm G n c F Q P (wcell k)

theorem embedded_tail (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool)
    (hf : level0Facts Mm G n c F Q P) :
    let b := EffectiveIteration.sourceDepth n
    let y := (Iteration.seedState b).budget
    let M := (Iteration.seedState b).matrix
    let a := Iteration.a G c b y 0 M
    let s := Iteration.s G c b y 0 M
    let q := Iteration.q₂ G c b y 0 M
    let L := Iteration.labels G c b y 0 M
    let nv := GraphVectors.vertexCount V s
    let nb := GraphVectors.auxiliaryCount s
    let hs : 0 < s := lt_of_lt_of_le (by decide : 0 < 4) (Iteration.bins_ge_four G c b y 0 M)
    let order := GraphVectors.itemOrder G s
    let cap := GraphVectors.supportCap G
      (le_trans (by decide : 3 ≤ 4) (Iteration.bins_ge_four G c b y 0 M))
    let bnk := EntryRunsRaw.cellBank (EntryLevelWords.levelWords G c b y 0 M)
    let T := EntryRunsRaw.tableT M.entry hs (Iteration.secondFamily G c b y 0 M) order
      (GraphVectors.vectors G s) cap
    let W := Wlvl Mm G n c F Q P
    let S := EntryWriter22Split.S0 Mm G n c F Q P
    ∃ t ≤ MatrixTableWriter.writerBound (rows s L nv nb M.rows) (cols a s q M.columns) T +
        (2 * (rows s L nv nb M.rows * cols a s q M.columns) + 2) + 1,
      ((advance tailProgram)^[t])
        (⟨some RawTableTail.startLabel, RawTableTail.startControl EntryRunsRaw.startControl,
          bank tailEmb S (RawTableTail.startBank bnk (rows s L nv nb M.rows)
            (cols a s q M.columns) W)⟩ :
          TM2.Cfg (fun _ : HStack => Bool) _ _) =
        ⟨none, ((EntryRunsRaw.startControl, none), none),
          bank tailEmb S (RawTableTail.exitBank bnk (rows s L nv nb M.rows)
            (cols a s q M.columns) W (EntryWriter22Split.word22 G n c))⟩ := by
  intro b y M a s q L nv nb hs order cap bnk T W S
  have hW22 : W 22 = [] := (EntryLevelWords.exit_writer_words Mm G n c F Q P hf).2.2.2.2.2.2.2
  obtain ⟨t, ht, hr, -⟩ := EntryLevelWords.level_raw_table_writer22 G c b y 0 M W hW22
  refine ⟨t, ht, ?_⟩
  have := BitMachineStackRun.run tailEmb S
    (RawTableTail.program EntryRunsRaw.csProgram EntryRunsRaw.startLabel EntryRunsRaw.startControl)
    ⟨some RawTableTail.startLabel, RawTableTail.startControl EntryRunsRaw.startControl,
      RawTableTail.startBank bnk (rows s L nv nb M.rows) (cols a s q M.columns) W⟩ t
  rw [hr] at this
  exact this

#print axioms nwMap_inj
#print axioms nwMap_ne_wcell
#print axioms exit_blank_nw
#print axioms card_NWIdx
#print axioms card_region
#print axioms tailMap_inj
#print axioms embedded_tail

/-- The tail's matrix-word cell is the named cell `oCell`. -/
theorem tailEmb_r12 : tailEmb (.inl (.inl (.inl (EntryRunsRaw.eo (.inl 12))))) = EntrySeedSpec.oCell := by
  show nwMap (regionEmb r12) = _
  rw [regionEmb_r12, nwMap_nwO]

/-- In the tail's start bank the named cell `oCell` holds the common word 12, i.e. the
level-0 matrix word `seedWord n`, exactly what `seedProgram` put there. -/
theorem start_at_oCell (G : EndpointGraph V E) (n c : ℕ) (S : HStack → List Bool) (r cl : ℕ)
    (W : Fin 64 → List Bool) :
    bank tailEmb S (RawTableTail.startBank (EntryRunsRaw.cellBank (EntryLevelWords.levelWords G c
      (EffectiveIteration.sourceDepth n) (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix)) r cl W) EntrySeedSpec.oCell =
      EntryWriter22Split.seedWord n := by
  rw [← tailEmb_r12, bank_at]
  show (MatrixTableWriter.ready _ r cl 0 0 0 0 [] []).bank (EntryRunsRaw.eo (.inl 12)) = _
  show EntryRunsRaw.cellBank _ (EntryRunsRaw.eo (.inl 12)) = _
  unfold EntryRunsRaw.cellBank
  rw [Equiv.symm_apply_apply, Sum.elim_inl]
  simp only [EntryLayout.common, EntryLevelWords.levelWords, TemplateEntry.actualWords,
    EntryWriter22Split.seedWord]
  simp

#print axioms regionEmb_r12
#print axioms tailEmb_r12
#print axioms start_at_oCell

end EthInapproximability.CurrentPaper.EntryTailEmbed
