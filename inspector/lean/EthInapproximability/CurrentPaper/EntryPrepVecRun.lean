import EthInapproximability.CurrentPaper.EntryPrepVec

/-!
# Segment 5b (run): `progV` from `midBank` to `midBank2`

Lane owner:b-stage4-entry-program-7 (Paper B, unit 2, map item 3).
-/

namespace EthInapproximability.CurrentPaper.EntryPrepVec

set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000
set_option maxRecDepth 16384

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open EthInapproximability.ParameterizedNP.GuardedSourceSlab
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Ready OuterLevel0Prep
open EntryPrepBudget EntryTailEmbed EntryTailClear EntryPrepCopy
open VectorsProducer (Z b inp ex)

variable (Mm : BitMachine.Machine)
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem mid_w (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool)
    (k : Fin 64) : midBank Mm G n c F Q P (tailEmb (wj k)) = Wlvl Mm G n c F Q P k := by
  rw [mid_tail]
  rfl

theorem common_wMid2 (G : EndpointGraph V E) (n c : ℕ) :
    EntryLayout.common (wMid2 G n c) =
      ![EntryLayout.rep (EntryLevelWords.w0 G n c).binB, EntryLayout.rep (EntryLevelWords.w0 G n c).wordB,
        EntryLayout.rep (EntryLevelWords.w0 G n c).binPowS,
        List.replicate (q2 G (sv G n c)) true, [], [], [true],
        EntryLayout.rep (EntryLevelWords.w0 G n c).cy, [], [],
        EntryLayout.rep (EntryLevelWords.w0 G n c).rx, [], EntryWriter22Split.seedWord n,
        EntryLayout.rep (EntryLevelWords.w0 G n c).s, EntryLayout.rep (EntryLevelWords.w0 G n c).sM1,
        EntryLayout.rep (EntryLevelWords.w0 G n c).cyPow1,
        MatrixMaterialization.rowMajor (GraphVectors.vectors G (sv G n c)) ++ [],
        EntryLayout.rep (EntryLevelWords.w0 G n c).sL, []] := by
  simp only [EntryLayout.common, wMid2, EntryLevelWords.levelWords, TemplateEntry.actualWords,
    EntryWriter22Split.seedWord, EntryLayout.rep, List.replicate_zero, List.append_nil]

theorem start_update (B : Fin EntryRunsRaw.K → List Bool) (k : Fin EntryRunsRaw.K)
    (w : List Bool) (r cl : ℕ) (W : Fin 64 → List Bool) :
    RawTableTail.startBank (Function.update B k w) r cl W =
      Function.update (RawTableTail.startBank B r cl W) (.inl (.inl (.inl k))) w := by
  funext j
  rcases j with ((k' | t) | e) | x
  · simp only [RawTableTail.startBank, RawTableTail.glob, MatrixTableWriter.Data.contents,
      MatrixTableWriter.Data.cell, MatrixTableWriter.ready, Sum.elim_inl, Function.update_apply,
      Sum.inl.injEq]
  · simp only [Function.update_apply, Sum.inl.injEq, reduceCtorEq, if_false]
    rfl
  · cases e <;> (simp only [Function.update_apply, Sum.inl.injEq, reduceCtorEq, if_false]; rfl)
  · simp only [Function.update_apply, reduceCtorEq, if_false]
    rfl

theorem cellBank_mid2 (G : EndpointGraph V E) (n c : ℕ) :
    EntryRunsRaw.cellBank (wMid2 G n c) =
      Function.update (Function.update (EntryRunsRaw.cellBank (wMid G n c))
        (EntryRunsRaw.eo (.inl 16))
        (MatrixMaterialization.rowMajor (GraphVectors.vectors G (sv G n c)) ++ []))
        (EntryRunsRaw.eo (.inl 3)) (List.replicate (q2 G (sv G n c)) true) := by
  have cw := common_wMid G n c
  have cw2 := common_wMid2 G n c
  funext k
  obtain ⟨o, rfl⟩ := EntryRunsRaw.eo.surjective k
  simp only [EntryRunsRaw.cellBank, Equiv.symm_apply_apply, Function.update_apply,
    EmbeddingLike.apply_eq_iff_eq]
  rcases o with i | r
  · simp only [Sum.elim_inl, Sum.inl.injEq, cw, cw2]
    fin_cases i <;> rfl
  · simp only [Sum.elim_inr, reduceCtorEq, if_false]

/-- The tail-region view: filling cw 3 and cw 16 turns `wMid` into `wMid2`. -/
theorem start2_eq (G : EndpointGraph V E) (n c : ℕ) (W : Fin 64 → List Bool) :
    Function.update (Function.update
      (RawTableTail.startBank (EntryRunsRaw.cellBank (wMid G n c)) (r0 G n c) (c0 G n c) W)
      (tj 16) (MatrixMaterialization.rowMajor (GraphVectors.vectors G (sv G n c)) ++ []))
      (tj 3) (List.replicate (q2 G (sv G n c)) true) =
    RawTableTail.startBank (EntryRunsRaw.cellBank (wMid2 G n c)) (r0 G n c) (c0 G n c) W := by
  rw [cellBank_mid2, start_update, start_update]
  rfl

/-- The bank after phases 1-2 is the lifted start bank of the admitted controller. -/
theorem B2_eq (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool) :
    let B1 := Function.update (Function.update (midBank Mm G n c F Q P) (zIn 1)
      (List.replicate (sv G n c) true)) (zIn 0)
      (EncodedGraph.encode (EncodedETHSource.serializeGraph G))
    Function.update B1 (zIn 0) (true :: B1 (zIn 0)) =
      bank ζ (midBank Mm G n c F Q P)
        (Sum.elim (VectorsFromGraphQ.Z0 G (sv G n c) []) VectorsFromGraphQ.Q0) := by
  intro B1
  have hB1 : B1 (zIn 0) = EncodedGraph.encode (EncodedETHSource.serializeGraph G) :=
    Function.update_self _ _ _
  rw [hB1]
  simp only [B1, Function.update_idem]
  have hY : Sum.elim (VectorsFromGraphQ.Z0 G (sv G n c) []) VectorsFromGraphQ.Q0 =
      Function.update (Function.update (fun x => midBank Mm G n c F Q P (ζ x))
        (Sum.inl (inp 1)) (List.replicate (sv G n c) true))
        (Sum.inl (inp 0)) (VectorsProducer.code G) := by
    funext x
    rcases x with (j | t) | q
    · fin_cases j <;>
        simp [Function.update_apply, mid_zeta, VectorsFromGraphQ.Z0, VectorsFromGraphQ.inputs0, inp]
    · simp only [Function.update_apply, inp, Sum.inl.injEq, reduceCtorEq, if_false, mid_zeta]
      exact ready_blank t
    · simp only [Function.update_apply, reduceCtorEq, if_false, mid_zeta]
      rfl
  rw [hY, bank_update, bank_update, bank_restrict]
  rfl

theorem vec_run (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool)
    (hf : level0Facts Mm G n c F Q P) :
    ∃ t ≤ boundV G n c, ∃ v,
      ((advance progV)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (MultiMove.startLabel (jobs1.map CopyFill.toJob))),
          (MultiMove.initial, ((), (VectorsFromGraphQ.initial,
            (MultiMove.initial, ((), (none : Option Bool)))))),
          midBank Mm G n c F Q P⟩ : TM2.Cfg (fun _ : HStack => Bool) _ _) =
        ⟨none, v, midBank2 Mm G n c F Q P⟩ := by
  set M0b := midBank Mm G n c F Q P with hM0b
  have e28 : M0b (tailEmb (wj 28)) = List.replicate (sv G n c) true := by
    rw [hM0b, mid_w]
    exact (writer_values Mm G n c F Q P hf).2.2.2.2.1
  have e37 : M0b (tailEmb (wj 37)) = [] := by
    rw [hM0b, mid_w]
    exact writer_blank Mm G n c F Q P 37 (by decide)
  have eGw : M0b (mcell .Gw) = EncodedGraph.encode (EncodedETHSource.serializeGraph G) :=
    mid_mGw Mm G n c F Q P
  -- phase 1
  have h1 := CopyFill.run tempW jobs1 good1 M0b e37 (by
    simp only [jobs1, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, zIn]
    exact ⟨mid_zeta Mm G n c F Q P _, mid_zeta Mm G n c F Q P _⟩)
  have hc1 : CopyFill.fillCost jobs1 M0b =
      (2 * (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length + 2) +
        ((2 * sv G n c + 2) + 0) := by
    simp only [CopyFill.fillCost, jobs1, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, eGw, e28, List.length_replicate]
  have hf1 : CopyFill.fill jobs1 M0b =
      Function.update (Function.update M0b (zIn 1) (List.replicate (sv G n c) true)) (zIn 0)
        (EncodedGraph.encode (EncodedETHSource.serializeGraph G)) := by
    simp only [jobs1, fill_cons, fill_nil, eGw, e28]
  rw [hc1, hf1] at h1
  -- phase 2
  have h2 := push_run (zIn 0) (Function.update (Function.update M0b (zIn 1)
    (List.replicate (sv G n c) true)) (zIn 0)
    (EncodedGraph.encode (EncodedETHSource.serializeGraph G)))
  rw [B2_eq Mm G n c F Q P] at h2
  -- phase 3
  obtain ⟨t3, ht3, v3, F3, r3, hq3, hfr3, hg3⟩ := vectors_growth G (sv G n c) []
  have h3 := BitMachineStackRun.run ζ M0b VectorsFromGraphQ.program
    (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
      VectorsFromGraphQ.initial,
      Sum.elim (VectorsFromGraphQ.Z0 G (sv G n c) []) VectorsFromGraphQ.Q0⟩ :
        TM2.Cfg (fun _ : Z2 => Bool) _ _) t3
  rw [r3] at h3
  simp only [stackCfg] at h3
  set B3 := bank ζ M0b (Sum.elim (VectorsProducer.exitBank G (sv G n c) []) F3) with hB3
  have b3t : ∀ j, B3 (tailEmb j) = M0b (tailEmb j) := fun j =>
    bank_outside _ _ _ _ (fun ⟨z, hz⟩ => tail_ne_ζ j z hz.symm)
  have b3q : B3 (zIn 2) = List.replicate (q2 G (sv G n c)) true := by
    rw [hB3, zIn, bank_at]; rfl
  have b3o : B3 zOut = MatrixMaterialization.rowMajor (GraphVectors.vectors G (sv G n c)) ++ [] := by
    rw [hB3, zOut, bank_at]; rfl
  have cw := common_wMid G n c
  have d3 : B3 (tailEmb (tj 3)) = [] := by
    rw [b3t, hM0b, mid_tail]
    simp only [tj, RawTableTail.startBank, RawTableTail.glob, MatrixTableWriter.Data.contents,
      MatrixTableWriter.Data.cell, MatrixTableWriter.ready, EntryRunsRaw.cellBank, Sum.elim_inl,
      Equiv.symm_apply_apply, cw]
    simp
  have d16 : B3 (tailEmb (tj 16)) = [] := by
    rw [b3t, hM0b, mid_tail]
    simp only [tj, RawTableTail.startBank, RawTableTail.glob, MatrixTableWriter.Data.contents,
      MatrixTableWriter.Data.cell, MatrixTableWriter.ready, EntryRunsRaw.cellBank, Sum.elim_inl,
      Equiv.symm_apply_apply, cw]
    simp
  -- phase 4
  have h4 := CopyFill.run tempW jobs4 good4 B3 (by rw [tempW, b3t]; exact e37) (by
    simp only [jobs4, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    exact ⟨d3, d16⟩)
  have hc4 : CopyFill.fillCost jobs4 B3 =
      (2 * q2 G (sv G n c) + 2) +
        ((2 * (MatrixMaterialization.rowMajor (GraphVectors.vectors G (sv G n c))).length + 2) + 0) := by
    simp only [CopyFill.fillCost, jobs4, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, b3q, b3o, List.length_replicate, List.append_nil]
  rw [hc4] at h4
  -- phase 5
  have h5 := WeightedRawWords.clear_run cellsZ cellsZ_inj (CopyFill.fill jobs4 B3)
  have hz4 : ∀ i, CopyFill.fill jobs4 B3 (cellsZ i) = B3 (cellsZ i) := by
    intro i
    apply CopyFill.fill_off
    simp only [jobs4, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, cellsZ]
    exact ⟨fun h => tail_ne_ζ _ _ h.symm, fun h => tail_ne_ζ _ _ h.symm⟩
  have hsum : (∑ i, (CopyFill.fill jobs4 B3 (cellsZ i)).length) ≤
      ∑ i : Fin nZ, lenB G n c ((Fintype.equivFin Z2).symm i) := by
    apply Finset.sum_le_sum
    intro i _
    rw [hz4, hB3, cellsZ, bank_at]
    rcases ((Fintype.equivFin Z2).symm i) with z | j
    · exact le_refl _
    · exact hg3 j
  -- the exit bank
  have hexit : BitMachineClearBank.cleared cellsZ (CopyFill.fill jobs4 B3) =
      midBank2 Mm G n c F Q P := by
    funext x
    by_cases hx : ∃ i, cellsZ i = x
    · obtain ⟨i, rfl⟩ := hx
      rw [BitMachineClearBank.cleared_bank]
      unfold midBank2
      rw [cellsZ, bank_outside _ _ _ _ (fun ⟨j, hj⟩ => tail_ne_ζ j _ hj)]
      exact (exit_blank_nw Mm G n c F Q P _).symm
    · rw [BitMachineClearBank.cleared_foreign _ _ _ (fun i h => hx ⟨i, h⟩)]
      have hnz : ¬ ∃ z, ζ z = x := by
        rintro ⟨z, rfl⟩
        exact hx ⟨(Fintype.equivFin Z2) z, by simp [cellsZ]⟩
      simp only [jobs4, fill_cons, fill_nil, b3q, b3o]
      by_cases ht : ∃ j, tailEmb j = x
      · obtain ⟨j, rfl⟩ := ht
        unfold midBank2
        rw [bank_at, ← start2_eq]
        simp only [Function.update_apply, EmbeddingLike.apply_eq_iff_eq]
        split_ifs <;> first | rfl | (rw [b3t, hM0b, mid_tail])
      · have hne3 : x ≠ tailEmb (tj 3) := fun h => ht ⟨_, h.symm⟩
        have hne16 : x ≠ tailEmb (tj 16) := fun h => ht ⟨_, h.symm⟩
        rw [Function.update_of_ne hne3, Function.update_of_ne hne16, hB3,
          bank_outside _ _ _ _ hnz, hM0b]
        unfold midBank midBank2
        rw [bank_outside _ _ _ _ ht, bank_outside _ _ _ _ ht]
  rw [hexit] at h5
  -- composition
  obtain ⟨u45, hu45, r45⟩ := BitMachineRawSequence.runs
    (MultiMove.program (jobs4.map CopyFill.toJob) tempW) (WeightedRawWords.clearProgram cellsZ)
    (MultiMove.startLabel (jobs4.map CopyFill.toJob)) (0 : Fin (nZ + 2))
    MultiMove.initial MultiMove.initial ((), (none : Option Bool)) ((), (none : Option Bool))
    _ _ _ _ _ h4 h5
  obtain ⟨u345, hu345, r345⟩ := BitMachineRawSequence.runs vecZ Q45
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (BitMachineRawSequence.leftLabel (MultiMove.startLabel (jobs4.map CopyFill.toJob)))
    VectorsFromGraphQ.initial v3 (MultiMove.initial, ((), (none : Option Bool))) _
    _ _ _ t3 u45 h3 r45
  obtain ⟨u2345, hu2345, r2345⟩ := BitMachineRawSequence.runs (pushP (zIn 0)) Q345
    () (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
    () () (VectorsFromGraphQ.initial, (MultiMove.initial, ((), (none : Option Bool)))) _
    _ _ _ 1 u345 h2 r345
  obtain ⟨u, hu, r⟩ := BitMachineRawSequence.runs
    (MultiMove.program (jobs1.map CopyFill.toJob) tempW) Q2345
    (MultiMove.startLabel (jobs1.map CopyFill.toJob)) (BitMachineRawSequence.leftLabel ())
    MultiMove.initial MultiMove.initial
    ((), (VectorsFromGraphQ.initial, (MultiMove.initial, ((), (none : Option Bool))))) _
    _ _ _ _ u2345 h1 r2345
  refine ⟨u, ?_, _, r⟩
  unfold boundV
  omega

#print axioms start2_eq
#print axioms B2_eq
#print axioms vec_run

end EthInapproximability.CurrentPaper.EntryPrepVec
