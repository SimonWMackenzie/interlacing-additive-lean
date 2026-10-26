import EthInapproximability.CurrentPaper.EntryPrepVecCompose

/-!
# Segment 5c (part 1): `cy^(firstLength a s)` is the present word `wordBase`

Lane owner:b-stage4-entry-program-7 (Paper B, unit 2, map item 3).

The common word cw 9 (`cyPowF = cy ^ firstLength a s`) is literally the persistent writer
word 26 (`wordBase a s cy := cy ^ firstLength a s`, `MatrixStage4Digits.wordBase`), so it needs
no re-run (`wordB_eq`, by `rfl`; `wMid3` records the copied value in the `cyPowF` field as
`w.wordB`, definitionally `w.cyPowF`): ONE fixed charged copy `progC` (owner-4 `CopyFill`, writer 26 -> tail cw 9, temp
writer 37) goes from `midBank2` to `midBank3` (= tail start bank at `wMid3`, cw 9 filled).
`FamilySpec` then reduces to `Family5Spec` (cw 4 `qOne a`, cw 5 first table,
cw 8 `firstLength a s - 1`, cw 11 row table, cw 18 `L`).
-/

namespace EthInapproximability.CurrentPaper.EntryPrepVec

set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000
set_option maxRecDepth 16384

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Ready OuterLevel0Prep
open EntryPrepBudget EntryTailEmbed EntryTailClear EntryPrepCopy

noncomputable def jobs9 : List (HStack × List HStack) := [(tailEmb (wj 26), [tailEmb (tj 9)])]

theorem good9 : CopyFill.Good tempW jobs9 where
  src_not_dst := by simp [jobs9, wj, tj]
  dst_nodup := by simp [jobs9]
  src_temp := by simp [jobs9, tempW, wj]
  temp_dst := by simp [jobs9, tempW, wj, tj]

noncomputable def progC := MultiMove.program (jobs9.map CopyFill.toJob) tempW

variable (Mm : BitMachine.Machine)
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem wordB_eq (G : EndpointGraph V E) (n c : ℕ) :
    (EntryLevelWords.w0 G n c).wordB = (EntryLevelWords.w0 G n c).cyPowF := rfl

noncomputable def wMid3 (G : EndpointGraph V E) (n c : ℕ) : EntryLayout.Words :=
  let w := EntryLevelWords.w0 G n c
  ⟨w.binB, w.wordB, w.binPowS, w.q, 0, [], w.cy, 0, w.wordB, w.rx, [], w.Rtable, w.s, w.sM1,
    w.cyPow1, w.vtable, w.sL, 0⟩

noncomputable def midBank3 (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool) :
    HStack → List Bool :=
  bank tailEmb (EntryWriter22Split.S0 Mm G n c F Q P)
    (RawTableTail.startBank (EntryRunsRaw.cellBank (wMid3 G n c)) (r0 G n c) (c0 G n c)
      (Wlvl Mm G n c F Q P))

theorem common_wMid3 (G : EndpointGraph V E) (n c : ℕ) :
    EntryLayout.common (wMid3 G n c) =
      ![EntryLayout.rep (EntryLevelWords.w0 G n c).binB, EntryLayout.rep (EntryLevelWords.w0 G n c).wordB,
        EntryLayout.rep (EntryLevelWords.w0 G n c).binPowS,
        List.replicate (ParameterizedNP.GuardedSourceSlab.q2 G (sv G n c)) true, [], [], [true],
        EntryLayout.rep (EntryLevelWords.w0 G n c).cy, [], EntryLayout.rep (EntryLevelWords.w0 G n c).wordB,
        EntryLayout.rep (EntryLevelWords.w0 G n c).rx, [], EntryWriter22Split.seedWord n,
        EntryLayout.rep (EntryLevelWords.w0 G n c).s, EntryLayout.rep (EntryLevelWords.w0 G n c).sM1,
        EntryLayout.rep (EntryLevelWords.w0 G n c).cyPow1,
        MatrixMaterialization.rowMajor (GraphVectors.vectors G (sv G n c)) ++ [],
        EntryLayout.rep (EntryLevelWords.w0 G n c).sL, []] := by
  simp only [EntryLayout.common, wMid3, EntryLevelWords.levelWords, TemplateEntry.actualWords,
    EntryWriter22Split.seedWord, EntryLayout.rep, List.replicate_zero, List.append_nil]

theorem cellBank_mid3 (G : EndpointGraph V E) (n c : ℕ) :
    EntryRunsRaw.cellBank (wMid3 G n c) =
      Function.update (EntryRunsRaw.cellBank (wMid2 G n c)) (EntryRunsRaw.eo (.inl 9))
        (EntryLayout.rep (EntryLevelWords.w0 G n c).wordB) := by
  have cw2 := common_wMid2 G n c
  have cw3 := common_wMid3 G n c
  funext k
  obtain ⟨o, rfl⟩ := EntryRunsRaw.eo.surjective k
  rcases o with i | r
  · by_cases h : i = 9
    · subst h
      rw [Function.update_self]
      simp only [EntryRunsRaw.cellBank, Equiv.symm_apply_apply, Sum.elim_inl]
      rw [cw3]
      simp
    · rw [Function.update_of_ne (fun e => h (Sum.inl.inj (EntryRunsRaw.eo.injective e)))]
      simp only [EntryRunsRaw.cellBank, Equiv.symm_apply_apply, Sum.elim_inl]
      rw [cw2, cw3]
      clear cw2 cw3
      fin_cases i <;> simp_all
  · rw [Function.update_of_ne (fun e => by cases EntryRunsRaw.eo.injective e)]
    simp only [EntryRunsRaw.cellBank, Equiv.symm_apply_apply, Sum.elim_inr]

theorem pow_run (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool)
    (hf : level0Facts Mm G n c F Q P) :
    ((advance progC)^[((2 * (EntryLevelWords.w0 G n c).wordB + 2) + 0) + 1])
      (⟨some (MultiMove.startLabel (jobs9.map CopyFill.toJob)), MultiMove.initial,
        midBank2 Mm G n c F Q P⟩ : TM2.Cfg (fun _ : HStack => Bool) _ _) =
      ⟨none, MultiMove.initial, midBank3 Mm G n c F Q P⟩ := by
  have m2 : ∀ j, midBank2 Mm G n c F Q P (tailEmb j) =
      RawTableTail.startBank (EntryRunsRaw.cellBank (wMid2 G n c)) (r0 G n c) (c0 G n c)
        (Wlvl Mm G n c F Q P) j := fun j => by unfold midBank2; rw [bank_at]
  have e26 : midBank2 Mm G n c F Q P (tailEmb (wj 26)) =
      EntryLayout.rep (EntryLevelWords.w0 G n c).wordB := by
    rw [m2]
    exact (writer_values Mm G n c F Q P hf).2.1
  have e37 : midBank2 Mm G n c F Q P (tailEmb (wj 37)) = [] := by
    rw [m2]
    exact writer_blank Mm G n c F Q P 37 (by decide)
  have cw2 := common_wMid2 G n c
  have d9 : midBank2 Mm G n c F Q P (tailEmb (tj 9)) = [] := by
    rw [m2]
    simp only [tj, RawTableTail.startBank, RawTableTail.glob, MatrixTableWriter.Data.contents,
      MatrixTableWriter.Data.cell, MatrixTableWriter.ready, EntryRunsRaw.cellBank, Sum.elim_inl,
      Equiv.symm_apply_apply, cw2]
    simp
  have h := CopyFill.run tempW jobs9 good9 (midBank2 Mm G n c F Q P) e37 (by
    simp only [jobs9, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    exact d9)
  have hc : CopyFill.fillCost jobs9 (midBank2 Mm G n c F Q P) =
      (2 * (EntryLevelWords.w0 G n c).wordB + 2) + 0 := by
    simp only [CopyFill.fillCost, jobs9, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, e26, EntryLayout.rep, List.length_replicate]
  have hx : CopyFill.fill jobs9 (midBank2 Mm G n c F Q P) = midBank3 Mm G n c F Q P := by
    simp only [jobs9, fill_cons, fill_nil, e26]
    unfold midBank2 midBank3
    rw [← bank_update, cellBank_mid3, start_update]
    rfl
  rw [hc, hx] at h
  exact h

/-- What remains of segment 5: cw 4, 5, 8, 11, 18. -/
def Family5Spec {LW VW : Type} (W : LW → TM2.Stmt (fun _ : HStack => Bool) LW VW) (w₀ : LW)
    (v₀ : VW) (T : ℕ) (G : EndpointGraph V E) (n c : ℕ) : Prop :=
  ∀ F Q P, level0Facts Mm G n c F Q P →
    ∃ t ≤ T, ∃ v₁ : VW,
      ((advance W)^[t]) ⟨some w₀, v₀, midBank3 Mm G n c F Q P⟩ =
        ⟨none, v₁, tailStart Mm G n c F Q P⟩

theorem family_of_family5 (G : EndpointGraph V E) (n c : ℕ) {LW VW : Type}
    (W : LW → TM2.Stmt (fun _ : HStack => Bool) LW VW) (w₀ : LW) (v₀ : VW) (T : ℕ)
    (hF : Family5Spec Mm W w₀ v₀ T G n c) :
    FamilySpec Mm (BitMachineRawSequence.program progC W w₀ MultiMove.initial v₀)
      (BitMachineRawSequence.leftLabel (MultiMove.startLabel (jobs9.map CopyFill.toJob)))
      (MultiMove.initial, v₀)
      ((((2 * (EntryLevelWords.w0 G n c).wordB + 2) + 0) + 1) + T + 1) G n c := by
  intro F Q P hf
  have ha := pow_run Mm G n c F Q P hf
  obtain ⟨tb, htb, v₁, hb⟩ := hF F Q P hf
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs progC W _ w₀ _ _ v₀ v₁ _ _ _ _ tb ha hb
  exact ⟨t, by omega, _, hr⟩

#print axioms wordB_eq
#print axioms cellBank_mid3
#print axioms pow_run
#print axioms family_of_family5

end EthInapproximability.CurrentPaper.EntryPrepVec
