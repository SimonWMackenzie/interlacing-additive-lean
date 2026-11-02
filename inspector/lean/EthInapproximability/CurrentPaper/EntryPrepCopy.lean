import EthInapproximability.CurrentPaper.EntryTailClear
import EthInapproximability.CurrentPaper.EntryLevelDerived

/-!
# Segment 5 (part A): copies and derived scalars written straight into the tail region

Lane owner:b-stage4-entry-program-7 (Paper B, unit 2, map item 3).

ONE fixed program `progA` (owner-4 `CopyFill`/`MultiMove` copy list, one charged
handoff, owner-5 `DerivedScalars`) runs on the level stack `HStack` from the prep exit
bank with the matrix word in `oCell` (the start bank of `EntryTailClear.PrepSpec`) and
halts on `midBank`: the tail start bank `tailStart` EXCEPT that the eight common words
`q, qOne a, first table, firstLength a s - 1, cy^firstLength, row table, rowMajor vectors, L`
(cw 3, 4, 5, 8, 9, 11, 16, 18) are still blank. Every cell it touches is a cell of the
embedded tail (`tailEmb`): copy sources and scratch are level-writer cells (the tail's own
writer), outputs are tail cells. Scratch: level writers 30..37 (outside `keepW`, blank at the
prep exit, blank again at the exit).

* copies: writer 29 -> cw 0, 26 -> cw 1, 27 -> cw 7, 17 -> cw 10, 28 -> cw 13, 16 -> cw 17,
  21 -> tail `cols` (all source-preserving);
* `DerivedScalars` with inputs writers 28, 27, 29, 16, 18, 15, 17 and outputs
  cw 14 (`s - 1`), cw 15 (`cy^(s+1)`), cw 2 (`binBase^s`), cw 6 (`[true]`),
  tail `rows` (`rows s L nv nb rx`).

`prep_of_rest`: `PrepSpec` for `progA ; W` from the single remaining interface `RestSpec W`
(from `midBank` to `tailStart`), hence `OuterLevel0Full.Writer22Spec` from `RestSpec` alone.
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

abbrev TSt := RawTableTail.Stack EntryRunsRaw.K

/-- Tail index of common word `i`. -/
noncomputable def tj (i : Fin 19) : TSt := .inl (.inl (.inl (EntryRunsRaw.eo (.inl i))))
def jRows : TSt := .inl (.inr .rows)
def jCols : TSt := .inl (.inr .cols)
/-- Tail index of writer cell `k` (the tail's writer is the level writer). -/
def wj (k : Fin 64) : TSt := .inr (.inl k)

theorem tailEmb_wj (k : Fin 64) : tailEmb (wj k) = wcell k := rfl
theorem tailEmb_tj12 : tailEmb (tj 12) = EntrySeedSpec.oCell := tailEmb_r12

/-! ## The copy list -/

noncomputable def copyJobs : List (HStack × List HStack) :=
  [(tailEmb (wj 29), [tailEmb (tj 0)]), (tailEmb (wj 26), [tailEmb (tj 1)]),
   (tailEmb (wj 27), [tailEmb (tj 7)]), (tailEmb (wj 17), [tailEmb (tj 10)]),
   (tailEmb (wj 28), [tailEmb (tj 13)]), (tailEmb (wj 16), [tailEmb (tj 17)]),
   (tailEmb (wj 21), [tailEmb jCols])]

noncomputable def tempW : HStack := tailEmb (wj 37)

theorem copy_good : CopyFill.Good tempW copyJobs where
  src_not_dst := by
    simp [copyJobs, wj, tj, jCols]
  dst_nodup := by
    simp [copyJobs, wj, tj, jCols]
  src_temp := by
    simp [copyJobs, tempW, wj]
  temp_dst := by
    simp [copyJobs, tempW, wj, tj, jCols]

theorem fill_cons (s d : HStack) (js : List (HStack × List HStack)) (S : HStack → List Bool) :
    CopyFill.fill ((s, [d]) :: js) S = Function.update (CopyFill.fill js S) d (S s) := by
  funext k
  simp only [CopyFill.fill, List.mem_singleton, Function.update_apply]

theorem fill_nil (S : HStack → List Bool) : CopyFill.fill [] S = S := funext fun _ => rfl

/-! ## The derived-scalar cells -/

noncomputable def idxJ : Fin 19 → TSt :=
  ![wj 28, wj 27, wj 29, wj 16, wj 18, wj 15, wj 17, tj 14, tj 15, tj 2, tj 6, jRows,
    wj 30, wj 31, wj 32, wj 33, wj 34, wj 35, wj 36]

theorem idxJ_inj : Function.Injective idxJ := by
  intro a b h
  fin_cases a <;> fin_cases b <;> first | rfl | (simp [idxJ, wj, tj, jRows] at h)

noncomputable def ιD : Fin 19 ↪ HStack := ⟨fun k => tailEmb (idxJ k), tailEmb.injective.comp idxJ_inj⟩

theorem ιD_apply (k : Fin 19) : ιD k = tailEmb (idxJ k) := rfl

/-! ## The program -/

noncomputable def progA :=
  BitMachineRawSequence.program (MultiMove.program (copyJobs.map CopyFill.toJob) tempW)
    (DerivedScalars.program ιD)
    (BitMachineRawSequence.leftLabel
      (MultiMove.startLabel ((DerivedScalars.jobs1 ιD).map CopyFill.toJob)))
    MultiMove.initial DerivedScalars.initial

variable (Mm : BitMachine.Machine)
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-! ## Banks -/

/-- The level-0 words with the eight recomputed words blank. -/
noncomputable def wMid (G : EndpointGraph V E) (n c : ℕ) : EntryLayout.Words :=
  let w := EntryLevelWords.w0 G n c
  ⟨w.binB, w.wordB, w.binPowS, 0, 0, [], w.cy, 0, 0, w.rx, [], w.Rtable, w.s, w.sM1, w.cyPow1,
    [], w.sL, 0⟩

/-- The tail start bank with the eight recomputed words blank. -/
noncomputable def midBank (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool) :
    HStack → List Bool :=
  bank tailEmb (EntryWriter22Split.S0 Mm G n c F Q P)
    (RawTableTail.startBank (EntryRunsRaw.cellBank (wMid G n c)) (r0 G n c) (c0 G n c)
      (Wlvl Mm G n c F Q P))

/-- The PrepSpec start bank. -/
noncomputable def S0' (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool) :
    HStack → List Bool :=
  Function.update (EntryWriter22Split.S0 Mm G n c F Q P) EntrySeedSpec.oCell
    (EntryWriter22Split.seedWord n)

/-- The region view of `S0'`: blank region, level writer, matrix word at `tj 12`. -/
noncomputable def Y0 (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool) :
    TSt → List Bool :=
  Function.update (Sum.elim (fun _ => []) (Sum.elim (Wlvl Mm G n c F Q P) (fun _ => [])))
    (tj 12) (EntryWriter22Split.seedWord n)

theorem S0'_eq (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool) :
    S0' Mm G n c F Q P = bank tailEmb (EntryWriter22Split.S0 Mm G n c F Q P) (Y0 Mm G n c F Q P) := by
  funext x
  by_cases hx : ∃ j, tailEmb j = x
  · obtain ⟨j, rfl⟩ := hx
    rw [bank_at]
    unfold S0' Y0
    rw [← tailEmb_tj12]
    by_cases hj : j = tj 12
    · subst hj
      simp
    · rw [Function.update_of_ne (fun h => hj (tailEmb.injective h)), Function.update_of_ne hj]
      rcases j with a | k | i
      · exact exit_blank_nw Mm G n c F Q P _
      · rfl
      · exact exit_blank_nw Mm G n c F Q P _
  · rw [bank_outside _ _ _ _ hx]
    unfold S0'
    rw [← tailEmb_tj12]
    exact Function.update_of_ne (fun h => hx ⟨_, h.symm⟩) _ _

/-! ## Values read at the prep exit -/

theorem writer_blank (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool)
    (k : Fin 64) (hk : k ∉ keepW) : Wlvl Mm G n c F Q P k = [] := by
  show exitBank G n c (G4 (level0RowsBank Mm G n c F Q P))
    (EntryExitBlank.scalarCell (WeightedColumnActualStage.writerSlots k)) = []
  apply EntryExitBlank.exit_blank_scalar
  intro h
  exact hk ((Finset.mem_map' WeightedColumnActualStage.writerSlots).1 h)

/-- The explicit copy cost (the sum of `2 |source| + 2`). -/
noncomputable def copyCost (G : EndpointGraph V E) (n c : ℕ) : ℕ :=
  (2 * (EntryLevelWords.w0 G n c).binB + 2) + ((2 * (EntryLevelWords.w0 G n c).wordB + 2) +
  ((2 * (EntryLevelWords.w0 G n c).cy + 2) + ((2 * (EntryLevelWords.w0 G n c).rx + 2) +
  ((2 * (EntryLevelWords.w0 G n c).s + 2) + ((2 * (EntryLevelWords.w0 G n c).sL + 2) +
  ((2 * c0 G n c + 2) + 0))))))

/-- The clock of `progA`. -/
noncomputable def boundA (G : EndpointGraph V E) (n c : ℕ) : ℕ :=
  (copyCost G n c + 1) +
    DerivedScalars.bound (EntryLevelDerived.d0 G n c).s (EntryLevelDerived.d0 G n c).cy
      (EntryLevelDerived.d0 G n c).binBase (EntryLevelDerived.d0 G n c).stagePrefixRows
      (EntryLevelDerived.d0 G n c).nv (EntryLevelDerived.d0 G n c).nb
      (EntryLevelDerived.d0 G n c).rx + 1

/-- The region view after the copies. -/
noncomputable def Y1 (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool) :
    TSt → List Bool :=
  let Y := Y0 Mm G n c F Q P
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update Y jCols (Y (wj 21))) (tj 17) (Y (wj 16)))
    (tj 13) (Y (wj 28))) (tj 10) (Y (wj 17))) (tj 7) (Y (wj 27))) (tj 1) (Y (wj 26)))
    (tj 0) (Y (wj 29))

theorem fill_eq (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool) :
    CopyFill.fill copyJobs (S0' Mm G n c F Q P) =
      bank tailEmb (EntryWriter22Split.S0 Mm G n c F Q P) (Y1 Mm G n c F Q P) := by
  unfold copyJobs
  simp only [fill_cons, fill_nil]
  rw [S0'_eq]
  simp only [bank_at, ← bank_update]
  rfl

/-- The region view after the derived scalars. -/
noncomputable def Y2 (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool) :
    TSt → List Bool :=
  let d := EntryLevelDerived.d0 G n c
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Y1 Mm G n c F Q P) (tj 14) (DerivedScalars.rep (d.s - 1)))
    (tj 15) (DerivedScalars.rep (d.cy ^ (d.s + 1))))
    (tj 2) (DerivedScalars.rep (d.binBase ^ d.s))) (tj 6) [true])
    jRows (DerivedScalars.rep (d.stagePrefixRows + (d.nv + d.nb) * d.rx))

theorem outBank_eq (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool) :
    let d := EntryLevelDerived.d0 G n c
    DerivedScalars.outBank ιD (CopyFill.fill copyJobs (S0' Mm G n c F Q P))
        d.s d.cy d.binBase d.stagePrefixRows d.nv d.nb d.rx =
      bank tailEmb (EntryWriter22Split.S0 Mm G n c F Q P) (Y2 Mm G n c F Q P) := by
  intro d
  rw [fill_eq]
  unfold DerivedScalars.outBank
  have e7 : ιD 7 = tailEmb (tj 14) := rfl
  have e8 : ιD 8 = tailEmb (tj 15) := rfl
  have e9 : ιD 9 = tailEmb (tj 2) := rfl
  have e10 : ιD 10 = tailEmb (tj 6) := rfl
  have e11 : ιD 11 = tailEmb jRows := rfl
  rw [e7, e8, e9, e10, e11]
  simp only [← bank_update]
  rfl

theorem writer_values (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool)
    (hf : level0Facts Mm G n c F Q P) :
    Wlvl Mm G n c F Q P 29 = EntryLayout.rep (EntryLevelWords.w0 G n c).binB ∧
    Wlvl Mm G n c F Q P 26 = EntryLayout.rep (EntryLevelWords.w0 G n c).wordB ∧
    Wlvl Mm G n c F Q P 27 = EntryLayout.rep (EntryLevelWords.w0 G n c).cy ∧
    Wlvl Mm G n c F Q P 17 = EntryLayout.rep (EntryLevelWords.w0 G n c).rx ∧
    Wlvl Mm G n c F Q P 28 = EntryLayout.rep (EntryLevelWords.w0 G n c).s ∧
    Wlvl Mm G n c F Q P 16 = EntryLayout.rep (EntryLevelWords.w0 G n c).sL ∧
    Wlvl Mm G n c F Q P 21 = List.replicate (c0 G n c) true :=
  (EntryLevelWords.exit_writer_words Mm G n c F Q P hf).elim fun h29 h =>
    h.elim fun h26 h => h.elim fun h27 h => h.elim fun h17 h => h.elim fun h28 h =>
      h.elim fun h16 h => ⟨h29, h26, h27, h17, h28, h16, h.1⟩

end EthInapproximability.CurrentPaper.EntryPrepCopy
