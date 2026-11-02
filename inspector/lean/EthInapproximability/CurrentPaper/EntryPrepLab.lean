import EthInapproximability.CurrentPaper.EntryPrepFinal

/-!
# Segment 5c (part 2): `L` by unary division of the present words `s*L` and `s`

Lane owner:b-stage4-entry-program-7 (Paper B, unit 2, map item 3).

cw 18 (`L`) needs no level re-run: writer 16 holds `s*L` and writer 28 holds `s > 0`
(`s >= 4`, admitted `Iteration.bins_ge_four`). ONE fixed program `progL`: a charged copy of
writer 16 into the scratch writer 30 (`CopyFill`, temp writer 37), then the admitted
`MatrixUnaryDivision.program` lifted on the six cells (input = writer 30, divisor = writer 28,
count = writer 31, remainder = writer 32, quotient = tail cw 18, saved = writer 33). The input
is consumed, the divisor restored, the remainder is `s*L mod s = 0` (blank), the quotient is
`L`. Scratch writers 30..33 are outside `keepW`, blank before and after.
`family5_of_family4`: `Family5Spec (progL ; W)` from `Family4Spec W` (cw 4, 5, 8, 11 only).
-/

namespace EthInapproximability.CurrentPaper.EntryPrepVec

set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000
set_option maxRecDepth 16384

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Ready OuterLevel0Prep
open EntryPrepBudget EntryTailEmbed EntryTailClear EntryPrepCopy

noncomputable def jobsL : List (HStack × List HStack) := [(tailEmb (wj 16), [tailEmb (wj 30)])]

theorem goodL : CopyFill.Good tempW jobsL where
  src_not_dst := by simp [jobsL, wj]
  dst_nodup := by simp [jobsL]
  src_temp := by simp [jobsL, tempW, wj]
  temp_dst := by simp [jobsL, tempW, wj]

noncomputable def divJ : Fin 6 → TSt := ![wj 30, wj 28, wj 31, wj 32, tj 18, wj 33]

theorem divJ_inj : Function.Injective divJ := by
  intro a b h
  fin_cases a <;> fin_cases b <;> first | rfl | (simp [divJ, wj, tj] at h)

noncomputable def ι6 : Fin 6 ↪ HStack := ⟨fun k => tailEmb (divJ k), tailEmb.injective.comp divJ_inj⟩

noncomputable def divP := fun l => stackStmt ι6 (MatrixUnaryDivision.program l)

noncomputable def progL :=
  BitMachineRawSequence.program (MultiMove.program (jobsL.map CopyFill.toJob) tempW) divP
    MatrixUnaryDivision.Label.start MultiMove.initial false

variable (Mm : BitMachine.Machine)
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

noncomputable def wMid4 (G : EndpointGraph V E) (n c : ℕ) : EntryLayout.Words :=
  let w := EntryLevelWords.w0 G n c
  ⟨w.binB, w.wordB, w.binPowS, w.q, 0, [], w.cy, 0, w.wordB, w.rx, [], w.Rtable, w.s, w.sM1,
    w.cyPow1, w.vtable, w.sL, w.L⟩

noncomputable def midBank4 (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool) :
    HStack → List Bool :=
  bank tailEmb (EntryWriter22Split.S0 Mm G n c F Q P)
    (RawTableTail.startBank (EntryRunsRaw.cellBank (wMid4 G n c)) (r0 G n c) (c0 G n c)
      (Wlvl Mm G n c F Q P))

theorem common_wMid4 (G : EndpointGraph V E) (n c : ℕ) :
    EntryLayout.common (wMid4 G n c) =
      ![EntryLayout.rep (EntryLevelWords.w0 G n c).binB, EntryLayout.rep (EntryLevelWords.w0 G n c).wordB,
        EntryLayout.rep (EntryLevelWords.w0 G n c).binPowS,
        List.replicate (ParameterizedNP.GuardedSourceSlab.q2 G (sv G n c)) true, [], [], [true],
        EntryLayout.rep (EntryLevelWords.w0 G n c).cy, [], EntryLayout.rep (EntryLevelWords.w0 G n c).wordB,
        EntryLayout.rep (EntryLevelWords.w0 G n c).rx, [], EntryWriter22Split.seedWord n,
        EntryLayout.rep (EntryLevelWords.w0 G n c).s, EntryLayout.rep (EntryLevelWords.w0 G n c).sM1,
        EntryLayout.rep (EntryLevelWords.w0 G n c).cyPow1,
        MatrixMaterialization.rowMajor (GraphVectors.vectors G (sv G n c)) ++ [],
        EntryLayout.rep (EntryLevelWords.w0 G n c).sL, EntryLayout.rep (EntryLevelWords.w0 G n c).L] := by
  simp only [EntryLayout.common, wMid4, EntryLevelWords.levelWords, TemplateEntry.actualWords,
    EntryWriter22Split.seedWord, EntryLayout.rep, List.replicate_zero, List.append_nil]

theorem cellBank_mid4 (G : EndpointGraph V E) (n c : ℕ) :
    EntryRunsRaw.cellBank (wMid4 G n c) =
      Function.update (EntryRunsRaw.cellBank (wMid3 G n c)) (EntryRunsRaw.eo (.inl 18))
        (EntryLayout.rep (EntryLevelWords.w0 G n c).L) := by
  have cw3 := common_wMid3 G n c
  have cw4 := common_wMid4 G n c
  funext k
  obtain ⟨o, rfl⟩ := EntryRunsRaw.eo.surjective k
  rcases o with i | r
  · by_cases h : i = 18
    · subst h
      rw [Function.update_self]
      simp only [EntryRunsRaw.cellBank, Equiv.symm_apply_apply, Sum.elim_inl]
      rw [cw4]
      simp
    · rw [Function.update_of_ne (fun e => h (Sum.inl.inj (EntryRunsRaw.eo.injective e)))]
      simp only [EntryRunsRaw.cellBank, Equiv.symm_apply_apply, Sum.elim_inl]
      rw [cw3, cw4]
      clear cw3 cw4
      fin_cases i <;> simp_all
  · rw [Function.update_of_ne (fun e => by cases EntryRunsRaw.eo.injective e)]
    simp only [EntryRunsRaw.cellBank, Equiv.symm_apply_apply, Sum.elim_inr]

theorem lab_run (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool)
    (hf : level0Facts Mm G n c F Q P) :
    ∃ t ≤ ((2 * (EntryLevelWords.w0 G n c).sL + 2) + 0 + 1) +
        MatrixUnaryDivision.exactTime (EntryLevelWords.w0 G n c).sL (EntryLevelWords.w0 G n c).s + 1,
      ((advance progL)^[t])
        (⟨some (BitMachineRawSequence.leftLabel (MultiMove.startLabel (jobsL.map CopyFill.toJob))),
          (MultiMove.initial, false), midBank3 Mm G n c F Q P⟩ :
          TM2.Cfg (fun _ : HStack => Bool) _ _) =
        ⟨none, (MultiMove.initial, false), midBank4 Mm G n c F Q P⟩ := by
  set M3 := midBank3 Mm G n c F Q P with hM3
  have m3 : ∀ j, M3 (tailEmb j) =
      RawTableTail.startBank (EntryRunsRaw.cellBank (wMid3 G n c)) (r0 G n c) (c0 G n c)
        (Wlvl Mm G n c F Q P) j := fun j => by rw [hM3]; unfold midBank3; rw [bank_at]
  have wv := writer_values Mm G n c F Q P hf
  have e16 : M3 (tailEmb (wj 16)) = List.replicate (EntryLevelWords.w0 G n c).sL true := by
    rw [m3]; exact wv.2.2.2.2.2.1
  have e28 : M3 (tailEmb (wj 28)) = List.replicate (EntryLevelWords.w0 G n c).s true := by
    rw [m3]; exact wv.2.2.2.2.1
  have eb : ∀ k : Fin 64, k ∉ keepW → M3 (tailEmb (wj k)) = [] := fun k hk => by
    rw [m3]; exact writer_blank Mm G n c F Q P k hk
  have cw3 := common_wMid3 G n c
  have d18 : M3 (tailEmb (tj 18)) = [] := by
    rw [m3]
    simp only [tj, RawTableTail.startBank, RawTableTail.glob, MatrixTableWriter.Data.contents,
      MatrixTableWriter.Data.cell, MatrixTableWriter.ready, EntryRunsRaw.cellBank, Sum.elim_inl,
      Equiv.symm_apply_apply, cw3]
    simp
  have hpos : 0 < (EntryLevelWords.w0 G n c).s :=
    lt_of_lt_of_le (by decide : 0 < 4) (Iteration.bins_ge_four G c (b0 n) (y0 n) 0 (M0 n))
  have hsl : (EntryLevelWords.w0 G n c).sL =
      (EntryLevelWords.w0 G n c).s * (EntryLevelWords.w0 G n c).L := rfl
  -- phase 1: copy s*L into writer 30
  have h1 := CopyFill.run tempW jobsL goodL M3 (eb 37 (by decide)) (by
    simp only [jobsL, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    exact eb 30 (by decide))
  have hc1 : CopyFill.fillCost jobsL M3 = (2 * (EntryLevelWords.w0 G n c).sL + 2) + 0 := by
    simp only [CopyFill.fillCost, jobsL, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, e16, List.length_replicate]
  set B1 := Function.update M3 (tailEmb (wj 30)) (List.replicate (EntryLevelWords.w0 G n c).sL true)
    with hB1
  have hf1 : CopyFill.fill jobsL M3 = B1 := by
    simp only [jobsL, fill_cons, fill_nil, e16, hB1]
  rw [hc1, hf1] at h1
  -- phase 2: the lifted division
  have hstart : bank ι6 B1 ![List.replicate (EntryLevelWords.w0 G n c).sL true,
      List.replicate (EntryLevelWords.w0 G n c).s true, [], [], [], []] = B1 := by
    apply bank_eq_self
    intro k
    fin_cases k
    · show _ = B1 (tailEmb (wj 30))
      rw [hB1, Function.update_self]; rfl
    · show _ = B1 (tailEmb (wj 28))
      rw [hB1, Function.update_of_ne (by simp [wj]), e28]; rfl
    · show _ = B1 (tailEmb (wj 31))
      rw [hB1, Function.update_of_ne (by simp [wj]), eb 31 (by decide)]; rfl
    · show _ = B1 (tailEmb (wj 32))
      rw [hB1, Function.update_of_ne (by simp [wj]), eb 32 (by decide)]; rfl
    · show _ = B1 (tailEmb (tj 18))
      rw [hB1, Function.update_of_ne (by simp [wj, tj]), d18]; rfl
    · show _ = B1 (tailEmb (wj 33))
      rw [hB1, Function.update_of_ne (by simp [wj]), eb 33 (by decide)]; rfl
  have hd := MatrixUnaryDivision.division_run (EntryLevelWords.w0 G n c).sL
    (EntryLevelWords.w0 G n c).s hpos
  have h2 := BitMachineStackRun.run ι6 B1 MatrixUnaryDivision.program
    (MatrixUnaryDivision.cfg (some .start) false
      (List.replicate (EntryLevelWords.w0 G n c).sL true)
      (List.replicate (EntryLevelWords.w0 G n c).s true) [] [] [] [])
    (MatrixUnaryDivision.exactTime (EntryLevelWords.w0 G n c).sL (EntryLevelWords.w0 G n c).s)
  have hd' : ((advance MatrixUnaryDivision.program)^[MatrixUnaryDivision.exactTime
      (EntryLevelWords.w0 G n c).sL (EntryLevelWords.w0 G n c).s])
      (MatrixUnaryDivision.cfg (some .start) false
        (List.replicate (EntryLevelWords.w0 G n c).sL true)
        (List.replicate (EntryLevelWords.w0 G n c).s true) [] [] [] []) = _ := hd
  rw [hd'] at h2
  simp only [stackCfg, MatrixUnaryDivision.cfg, hstart] at h2
  -- the exit bank
  have hq : (EntryLevelWords.w0 G n c).sL / (EntryLevelWords.w0 G n c).s =
      (EntryLevelWords.w0 G n c).L := by
    rw [hsl]; exact Nat.mul_div_cancel_left _ hpos
  have hr : (EntryLevelWords.w0 G n c).sL % (EntryLevelWords.w0 G n c).s = 0 := by
    rw [hsl]; exact Nat.mul_mod_right _ _
  rw [hq, hr] at h2
  have hexit : bank ι6 B1 ![[], List.replicate (EntryLevelWords.w0 G n c).s true, [],
      List.replicate 0 true, List.replicate (EntryLevelWords.w0 G n c).L true, []] =
      midBank4 Mm G n c F Q P := by
    have hv : (![[], List.replicate (EntryLevelWords.w0 G n c).s true, [],
        List.replicate 0 true, List.replicate (EntryLevelWords.w0 G n c).L true, []] :
          Fin 6 → List Bool) =
        Function.update (Function.update (fun k => B1 (ι6 k)) 0 []) 4
          (List.replicate (EntryLevelWords.w0 G n c).L true) := by
      funext k
      fin_cases k
      · rfl
      · show _ = B1 (tailEmb (wj 28))
        rw [hB1, Function.update_of_ne (by simp [wj]), e28]; rfl
      · show _ = B1 (tailEmb (wj 31))
        rw [hB1, Function.update_of_ne (by simp [wj]), eb 31 (by decide)]; rfl
      · show _ = B1 (tailEmb (wj 32))
        rw [hB1, Function.update_of_ne (by simp [wj]), eb 32 (by decide)]; rfl
      · rfl
      · show _ = B1 (tailEmb (wj 33))
        rw [hB1, Function.update_of_ne (by simp [wj]), eb 33 (by decide)]; rfl
    rw [hv, bank_update, bank_update, bank_restrict]
    show Function.update (Function.update B1 (tailEmb (wj 30)) []) (tailEmb (tj 18))
      (List.replicate (EntryLevelWords.w0 G n c).L true) = _
    have hz : Function.update M3 (tailEmb (wj 30)) [] = M3 := by
      funext y
      by_cases hy : y = tailEmb (wj 30)
      · subst hy
        rw [Function.update_self, eb 30 (by decide)]
      · rw [Function.update_of_ne hy]
    rw [hB1, Function.update_idem, hz, hM3]
    unfold midBank3 midBank4
    rw [← bank_update, cellBank_mid4, start_update]
    rfl
  rw [hexit] at h2
  obtain ⟨t, ht, hr2⟩ := BitMachineRawSequence.runs
    (MultiMove.program (jobsL.map CopyFill.toJob) tempW) divP
    (MultiMove.startLabel (jobsL.map CopyFill.toJob)) MatrixUnaryDivision.Label.start
    MultiMove.initial MultiMove.initial false false _ _ _ _ _ h1 h2
  exact ⟨t, by omega, hr2⟩

/-- What remains of segment 5: cw 4 (`qOne a`), cw 5 (first table), cw 8
(`firstLength a s - 1`), cw 11 (row table). -/
def Family4Spec {LW VW : Type} (W : LW → TM2.Stmt (fun _ : HStack => Bool) LW VW) (w₀ : LW)
    (v₀ : VW) (T : ℕ) (G : EndpointGraph V E) (n c : ℕ) : Prop :=
  ∀ F Q P, level0Facts Mm G n c F Q P →
    ∃ t ≤ T, ∃ v₁ : VW,
      ((advance W)^[t]) ⟨some w₀, v₀, midBank4 Mm G n c F Q P⟩ =
        ⟨none, v₁, tailStart Mm G n c F Q P⟩

theorem family5_of_family4 (G : EndpointGraph V E) (n c : ℕ) {LW VW : Type}
    (W : LW → TM2.Stmt (fun _ : HStack => Bool) LW VW) (w₀ : LW) (v₀ : VW) (T : ℕ)
    (hF : Family4Spec Mm W w₀ v₀ T G n c) :
    Family5Spec Mm (BitMachineRawSequence.program progL W w₀ (MultiMove.initial, false) v₀)
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel (MultiMove.startLabel (jobsL.map CopyFill.toJob))))
      ((MultiMove.initial, false), v₀)
      ((((2 * (EntryLevelWords.w0 G n c).sL + 2) + 0 + 1) +
        MatrixUnaryDivision.exactTime (EntryLevelWords.w0 G n c).sL (EntryLevelWords.w0 G n c).s + 1)
        + T + 1) G n c := by
  intro F Q P hf
  obtain ⟨ta, hta, ha⟩ := lab_run Mm G n c F Q P hf
  obtain ⟨tb, htb, v₁, hb⟩ := hF F Q P hf
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs progL W _ w₀ _ _ v₀ v₁ _ _ _ ta tb ha hb
  exact ⟨t, by omega, _, hr⟩

#print axioms divJ_inj
#print axioms cellBank_mid4
#print axioms lab_run
#print axioms family5_of_family4

end EthInapproximability.CurrentPaper.EntryPrepVec
