import EthInapproximability.CurrentPaper.EntryPrepCopy

/-!
# Segment 5 (part A, continued): the region bank after part A is the tail start bank
with the eight recomputed words blank (`Y2_eq`), the run of `progA` (`prep_part_A`), and
`PrepSpec` from the remaining interface `RestSpec` (`prep_of_rest`).

Lane owner:b-stage4-entry-program-7 (Paper B, unit 2, map item 3).
-/

namespace EthInapproximability.CurrentPaper.EntryPrepCopy

set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000
set_option maxRecDepth 16384

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Ready OuterLevel0Prep
open EntryPrepBudget EntryTailEmbed EntryTailClear
open Construction MatrixStage4Codes MatrixStage4Digits MatrixMaterialization

variable (Mm : BitMachine.Machine)
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem common_wMid (G : EndpointGraph V E) (n c : ℕ) :
    EntryLayout.common (wMid G n c) =
      ![EntryLayout.rep (EntryLevelWords.w0 G n c).binB, EntryLayout.rep (EntryLevelWords.w0 G n c).wordB,
        EntryLayout.rep (EntryLevelWords.w0 G n c).binPowS, [], [], [], [true],
        EntryLayout.rep (EntryLevelWords.w0 G n c).cy, [], [],
        EntryLayout.rep (EntryLevelWords.w0 G n c).rx, [], EntryWriter22Split.seedWord n,
        EntryLayout.rep (EntryLevelWords.w0 G n c).s, EntryLayout.rep (EntryLevelWords.w0 G n c).sM1,
        EntryLayout.rep (EntryLevelWords.w0 G n c).cyPow1, [],
        EntryLayout.rep (EntryLevelWords.w0 G n c).sL, []] := by
  simp only [EntryLayout.common, wMid, EntryLevelWords.levelWords, TemplateEntry.actualWords,
    EntryWriter22Split.seedWord, EntryLayout.rep, List.replicate_zero]

theorem rows_val (G : EndpointGraph V E) (n c : ℕ) :
    let d := EntryLevelDerived.d0 G n c
    DerivedScalars.rep (d.stagePrefixRows + (d.nv + d.nb) * d.rx) = List.replicate (r0 G n c) true :=
  rfl

theorem Y2_eq (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool)
    (hf : level0Facts Mm G n c F Q P) :
    Y2 Mm G n c F Q P =
      RawTableTail.startBank (EntryRunsRaw.cellBank (wMid G n c)) (r0 G n c) (c0 G n c)
        (Wlvl Mm G n c F Q P) := by
  obtain ⟨e29, e26, e27, e17, e28, e16, e21⟩ := writer_values Mm G n c F Q P hf
  obtain ⟨v1, v2, v3, -⟩ := EntryLevelDerived.level_derived_values G n c
  have v4 := rows_val G n c
  have cw := common_wMid G n c
  funext j
  rcases j with ((k | t) | e) | (k | i)
  · obtain ⟨o, rfl⟩ := EntryRunsRaw.eo.surjective k
    rcases o with i | r
    · fin_cases i <;>
        simp only [Y2, Y1, Y0, tj, jRows, jCols, wj, Function.update_apply, RawTableTail.startBank,
          RawTableTail.glob, MatrixTableWriter.Data.contents, MatrixTableWriter.Data.cell,
          MatrixTableWriter.ready, EntryRunsRaw.cellBank, Sum.elim_inl, Sum.elim_inr,
          Equiv.symm_apply_apply, Sum.inl.injEq, reduceCtorEq,
          EmbeddingLike.apply_eq_iff_eq, Fin.isValue, if_false, if_true, cw,
          e29, e26, e27, e17, e28, e16, v1, v2, v3] <;> simp
    · simp only [Y2, Y1, Y0, tj, jRows, jCols, wj, Function.update_apply, RawTableTail.startBank,
        RawTableTail.glob, MatrixTableWriter.Data.contents, MatrixTableWriter.Data.cell,
        MatrixTableWriter.ready, EntryRunsRaw.cellBank, Sum.elim_inl, Sum.elim_inr,
        Equiv.symm_apply_apply, Sum.inl.injEq, reduceCtorEq,
        EmbeddingLike.apply_eq_iff_eq, if_false]
  · fin_cases t <;>
      simp only [Y2, Y1, Y0, tj, jRows, jCols, wj, Function.update_apply, RawTableTail.startBank,
        RawTableTail.glob, MatrixTableWriter.Data.contents, MatrixTableWriter.Data.cell,
        MatrixTableWriter.ready, Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq, Sum.inr.injEq,
        reduceCtorEq, if_false] <;> simp
  · cases e <;>
      simp only [Y2, Y1, Y0, tj, jRows, jCols, wj, Function.update_apply, RawTableTail.startBank,
        RawTableTail.glob, MatrixTableWriter.Data.contents, MatrixTableWriter.Data.foreign,
        MatrixTableWriter.ready, Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq, Sum.inr.injEq,
        reduceCtorEq, if_false, if_true, e21, v4] <;> simp
  · simp only [Y2, Y1, Y0, tj, jRows, jCols, wj, Function.update_apply, RawTableTail.startBank,
      RawTableTail.glob, Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq, Sum.inr.injEq,
      reduceCtorEq, if_false]
  · simp only [Y2, Y1, Y0, tj, jRows, jCols, wj, Function.update_apply, RawTableTail.startBank,
      RawTableTail.glob, Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq, Sum.inr.injEq,
      reduceCtorEq, if_false]

end EthInapproximability.CurrentPaper.EntryPrepCopy
