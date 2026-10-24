import EthInapproximability.CurrentPaper.EntryPrepFamilyLvl

/-!
# Lane owner:b-stage4-entry-program-8: `Family4Spec progF` (from `midBank4` to `tailStart`)

`family4` discharges owner-7's interface `EntryPrepVec.Family4Spec` for the fixed program
`progF` with the public clock `TF G n c`; `level0_writer22` then gives the production consumer
`OuterLevel0Full.Writer22Spec` with NO remaining premise (through owner-7's frozen
`level0_writer22_of_family4`).
-/

namespace EthInapproximability.CurrentPaper.EntryPrepFamily

set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000
set_option maxRecDepth 16384

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Ready OuterLevel0Prep
open EntryPrepBudget EntryTailEmbed EntryTailClear EntryPrepCopy EntryPrepVec

variable (Mm : BitMachine.Machine)
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-! ## The per-cell clear allowance -/

theorem bnd_inl (G : EndpointGraph V E) (n c : ℕ) (j : WeightedLevelColumnSave.Stack) :
    bnd G n c (Sum.inl j) =
      (WeightedLevelColumnSave.initialBank (iP G n c) (gP G) WeightedRawWords.noW j).length +
        growB G n c := by
  unfold bnd; rw [Sum.elim_inl]

theorem bnd_inr (G : EndpointGraph V E) (n c : ℕ) (x : EntryFamilyAssembly.ACell) :
    bnd G n c (Sum.inr x) = (exA G n c x).length := by
  unfold bnd; rw [Sum.elim_inr]

theorem len_bound (G : EndpointGraph V E) (n c : ℕ) (Z : WeightedLevelColumnSave.Stack → List Bool)
    (hg : ∀ j, (Z j).length ≤
      (WeightedLevelColumnSave.initialBank (iP G n c) (gP G) WeightedRawWords.noW j).length +
        growB G n c)
    (y : EntryFamilyLevel.Stack) : (Sum.elim Z (exA G n c) y).length ≤ bnd G n c y := by
  rcases y with j | x
  · rw [bnd_inl, Sum.elim_inl]; exact hg j
  · rw [bnd_inr, Sum.elim_inr]

/-! ## The run -/

set_option maxHeartbeats 4000000 in
theorem family4 (G : EndpointGraph V E) (n c : ℕ) :
    Family4Spec Mm progF
      (BitMachineRawSequence.leftLabel (MultiMove.startLabel (jobsA.map CopyFill.toJob)))
      (MultiMove.initial, ((), (MultiMove.initial, (EntryFamilyLevel.initialControl,
        (MultiMove.initial, ((none : Option Bool), ((), (none : Option Bool))))))))
      (TF G n c) G n c := by
  intro F Q P hf
  set M4 := midBank4 Mm G n c F Q P with hM4
  have wv := writer_values Mm G n c F Q P hf
  have m4w : ∀ k, M4 (tailEmb (wj k)) = Wlvl Mm G n c F Q P k := fun k => by
    rw [hM4, mid4_tail]; rfl
  have e37 : M4 tempW = [] := by
    rw [tempW, m4w]; exact writer_blank Mm G n c F Q P 37 (by decide)
  have mv := WeightedLevel0Masters.masterC_values Mm G n c
  have eGw : M4 (mcell .Gw) = EncodedGraph.encode (gP G) :=
    (mid4_master Mm G n c F Q P .Gw (by simp)).trans mv.2.2.2.2.1
  have eC : M4 (mcell .C) = List.replicate c true :=
    (mid4_master Mm G n c F Q P .C (by simp)).trans mv.1
  have eB : M4 (mcell .B) = List.replicate (b0 n) true :=
    (mid4_master Mm G n c F Q P .B (by simp)).trans mv.2.1
  have eY : M4 (mcell .Y) = List.replicate (y0 n) true :=
    (mid4_master Mm G n c F Q P .Y (by simp)).trans mv.2.2.1
  have eE : M4 (mcell .E) = List.replicate (Fintype.card E) true :=
    (mid4_master Mm G n c F Q P .E (by simp)).trans mv.2.2.2.1
  have e17 : M4 (tailEmb (wj 17)) = EntryLayout.rep (EntryLevelWords.w0 G n c).rx := by
    rw [m4w]; exact wv.2.2.2.1
  have e27 : M4 (tailEmb (wj 27)) = EntryLayout.rep (EntryLevelWords.w0 G n c).cy := by
    rw [m4w]; exact wv.2.2.1
  have e28 : M4 (tailEmb (wj 28)) = EntryLayout.rep (EntryLevelWords.w0 G n c).s := by
    rw [m4w]; exact wv.2.2.2.2.1
  have mι : ∀ x, M4 (ι x) = [] := fun x => mid4_free Mm G n c F Q P _
  -- phase A: Gw -> pIn
  have hA := CopyFill.run tempW jobsA goodA M4 e37 (by
    simp only [jobsA, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
      forall_eq]
    exact mι _)
  have hcA : CopyFill.fillCost jobsA M4 = costA G := by
    simp only [CopyFill.fillCost, jobsA, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, eGw, costA]
  have hfA : CopyFill.fill jobsA M4 =
      Function.update M4 (ι pInF) (EncodedGraph.encode (gP G)) := by
    simp only [jobsA, fill_cons, fill_nil, eGw]
  rw [hcA, hfA] at hA
  -- phase B: push `true`
  have hB := push_run (ι pInF) (Function.update M4 (ι pInF) (EncodedGraph.encode (gP G)))
  rw [Function.update_self, Function.update_idem] at hB
  -- phase C: the six raw words
  have npC : mcell .C ≠ ι pInF := fun h => ι_ne_mC _ h.symm
  have npB : mcell .B ≠ ι pInF := fun h => ι_ne_mB _ h.symm
  have npY : mcell .Y ≠ ι pInF := fun h => ι_ne_mY _ h.symm
  have npE : mcell .E ≠ ι pInF := fun h => ι_ne_mE _ h.symm
  have np17 : tailEmb (wj 17) ≠ ι pInF := fun h => ι_ne_wj _ 17 h.symm
  have np27 : tailEmb (wj 27) ≠ ι pInF := fun h => ι_ne_wj _ 27 h.symm
  have npT : tempW ≠ ι pInF := fun h => ι_ne_wj _ 37 h.symm
  have hraw : ∀ k, Function.update M4 (ι pInF) (true :: EncodedGraph.encode (gP G))
      (ι (rawF k)) = [] := fun k => by
    rw [Function.update_of_ne (fun h => rawF_ne_pIn k (ι.injective h))]; exact mι _
  have hC := CopyFill.run tempW jobsC goodC
    (Function.update M4 (ι pInF) (true :: EncodedGraph.encode (gP G)))
    (by rw [Function.update_of_ne npT]; exact e37) (by
      simp only [jobsC, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq]
      exact ⟨hraw 0, hraw 5, hraw 3, hraw 4, hraw 2, hraw 1⟩)
  have hcC : CopyFill.fillCost jobsC
      (Function.update M4 (ι pInF) (true :: EncodedGraph.encode (gP G))) = costC G n c := by
    simp only [CopyFill.fillCost, jobsC, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Function.update_of_ne npC, Function.update_of_ne npB,
      Function.update_of_ne npY, Function.update_of_ne npE, Function.update_of_ne np17,
      Function.update_of_ne np27, eC, eB, eY, eE, e17, e27, List.length_replicate,
      EntryLayout.rep, costC]
  have hfC : CopyFill.fill jobsC
      (Function.update M4 (ι pInF) (true :: EncodedGraph.encode (gP G))) =
      bank ι M4 (SF G n c) := by
    rw [SF_eq]
    simp only [bank_update]
    rw [bank_eq_self ι M4 (fun _ => []) (fun k => (mι k).symm)]
    simp only [jobsC, fill_cons, fill_nil, Function.update_of_ne npC, Function.update_of_ne npB,
      Function.update_of_ne npY, Function.update_of_ne npE, Function.update_of_ne np17,
      Function.update_of_ne np27, eC, eB, eY, eE, e17, e27]
  rw [hcC, hfC] at hC
  -- phase D: the admitted level-wired family controller, lifted along `ι`
  obtain ⟨Z, nn, hnn, hrun, hgrow, hfirst, hrow⟩ := level0_family G n c
  have hD := BitMachineStackRun.run ι M4 EntryFamilyLevel.program
    (⟨some (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))))),
      EntryFamilyLevel.initialControl, SF G n c⟩ :
      TM2.Cfg (fun _ : EntryFamilyLevel.Stack => Bool) _ _) nn
  rw [hrun] at hD
  simp only [stackCfg] at hD
  set B3 := bank ι M4 (Sum.elim Z (exA G n c)) with hB3
  have b3o : ∀ x, (¬ ∃ y, ι y = x) → B3 x = M4 x := fun x hx => by
    rw [hB3, bank_outside _ _ _ _ hx]
  have b3tj : ∀ i, B3 (tailEmb (tj i)) = M4 (tailEmb (tj i)) := fun i =>
    b3o _ (fun ⟨y, hy⟩ => ι_ne_tj y i hy)
  have b3wj : ∀ k, B3 (tailEmb (wj k)) = M4 (tailEmb (wj k)) := fun k =>
    b3o _ (fun ⟨y, hy⟩ => ι_ne_wj y k hy)
  have vfirst : B3 (ι (aF .first)) = (EntryLevelWords.w0 G n c).firstTable := by
    rw [hB3, bank_at]; simp only [aF, Sum.elim_inr]; rw [w0_first]; exact hfirst
  have vrow : B3 (ι (aF .row)) = (EntryLevelWords.w0 G n c).rowTable := by
    rw [hB3, bank_at]; simp only [aF, Sum.elim_inr]; rw [w0_row]; exact hrow
  have vw : B3 (ι (aF .w)) = EntryLayout.rep (EntryLevelWords.w0 G n c).qOne := by
    rw [hB3, bank_at]; simp only [aF, Sum.elim_inr]; rfl
  -- phase E: the four copies
  have hE := CopyFill.run tempW jobsE goodE B3 (by rw [tempW, b3wj]; exact e37) (by
    simp only [jobsE, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [b3tj] <;> exact mid4_out Mm G n c F Q P _ (by decide))
  have hcE : CopyFill.fillCost jobsE B3 = costE G n c := by
    simp only [CopyFill.fillCost, jobsE, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, vfirst, vrow, vw, EntryLayout.rep, List.length_replicate, costE]
  rw [hcE] at hE
  set SE := CopyFill.fill jobsE B3 with hSE
  have hSE' : SE = Function.update (Function.update (Function.update (Function.update B3
      (tailEmb (tj 8)) (EntryLayout.rep (EntryLevelWords.w0 G n c).qOne))
      (tailEmb (tj 4)) (EntryLayout.rep (EntryLevelWords.w0 G n c).qOne))
      (tailEmb (tj 11)) (EntryLevelWords.w0 G n c).rowTable)
      (tailEmb (tj 5)) (EntryLevelWords.w0 G n c).firstTable := by
    rw [hSE]
    simp only [jobsE, fill_cons, fill_nil, vfirst, vrow, vw]
  have d45 : tailEmb (tj 4) ≠ tailEmb (tj 5) := tailEmb.injective.ne (by simp [tj])
  have d48 : tailEmb (tj 4) ≠ tailEmb (tj 8) := tailEmb.injective.ne (by simp [tj])
  have d411 : tailEmb (tj 4) ≠ tailEmb (tj 11) := tailEmb.injective.ne (by simp [tj])
  have d58 : tailEmb (tj 5) ≠ tailEmb (tj 8) := tailEmb.injective.ne (by simp [tj])
  have d511 : tailEmb (tj 5) ≠ tailEmb (tj 11) := tailEmb.injective.ne (by simp [tj])
  have d811 : tailEmb (tj 8) ≠ tailEmb (tj 11) := tailEmb.injective.ne (by simp [tj])
  have tw : ∀ (k : Fin 64) (i : Fin 19), tailEmb (wj k) ≠ tailEmb (tj i) := fun k i =>
    tailEmb.injective.ne (by simp [wj, tj])
  -- phase F: writer 28 appended onto cw 8
  have se28 : SE (ι3 0) = EntryLayout.rep (EntryLevelWords.w0 G n c).s := by
    show SE (tailEmb (wj 28)) = _
    rw [hSE', Function.update_of_ne (tw 28 5), Function.update_of_ne (tw 28 11),
      Function.update_of_ne (tw 28 4), Function.update_of_ne (tw 28 8), b3wj, e28]
  have se8 : SE (ι3 1) = EntryLayout.rep (EntryLevelWords.w0 G n c).qOne := by
    show SE (tailEmb (tj 8)) = _
    rw [hSE', Function.update_of_ne d58.symm, Function.update_of_ne d811,
      Function.update_of_ne d48.symm, Function.update_self]
  have seT : SE (ι3 2) = [] := by
    show SE (tailEmb (wj 37)) = _
    rw [hSE', Function.update_of_ne (tw 37 5), Function.update_of_ne (tw 37 11),
      Function.update_of_ne (tw 37 4), Function.update_of_ne (tw 37 8), b3wj]
    exact e37
  have hF := MatrixStage4ScalarPreparationOps.copy_run ι3 SE seT
  rw [se28, se8, firstExp_eq] at hF
  have k31 : ι3 1 = tailEmb (tj 8) := rfl
  rw [k31] at hF
  simp only [EntryLayout.rep, List.length_replicate] at hF
  -- phase G: the charged clear of the whole workspace
  set SF' := Function.update SE (tailEmb (tj 8))
    (EntryLayout.rep (EntryLevelWords.w0 G n c).firstExp) with hSF'
  have hG := WeightedRawWords.clear_run cellsF cellsF_inj SF'
  have hsum : (∑ i, (SF' (cellsF i)).length) ≤ clearB G n c := by
    apply Finset.sum_le_sum
    intro i _
    have hc : SF' (cellsF i) = B3 (cellsF i) := by
      rw [hSF', Function.update_of_ne (cellsF_ne_tj i 8), hSE', Function.update_of_ne (cellsF_ne_tj i 5),
        Function.update_of_ne (cellsF_ne_tj i 11), Function.update_of_ne (cellsF_ne_tj i 4),
        Function.update_of_ne (cellsF_ne_tj i 8)]
    rw [hc]
    show (B3 (fmap (emb0 ((Fintype.equivFin FamIdx).symm i)))).length ≤ _
    generalize (Fintype.equivFin FamIdx).symm i = x
    unfold lenF
    by_cases h : ∃ y, enc y = x
    · rw [dif_pos h]
      have hcs := Classical.choose_spec h
      generalize Classical.choose h = y at hcs ⊢
      subst hcs
      show (B3 (ι y)).length ≤ _
      rw [hB3, bank_at]
      exact len_bound G n c Z hgrow y
    · rw [dif_neg h, b3o _ (fun ⟨y, hy⟩ => h ⟨y, emb0.injective (fmap_inj hy)⟩)]
      rw [show M4 (fmap (emb0 x)) = [] from mid4_free Mm G n c F Q P _]
      exact le_refl _
  -- the exit bank is `tailStart`
  have hexit : BitMachineClearBank.cleared cellsF SF' = tailStart Mm G n c F Q P := by
    rw [tail_gap]
    funext x
    by_cases hx : ∃ i, cellsF i = x
    · obtain ⟨i, rfl⟩ := hx
      rw [BitMachineClearBank.cleared_bank]
      rw [Function.update_of_ne (cellsF_ne_tj i 11), Function.update_of_ne (cellsF_ne_tj i 8),
        Function.update_of_ne (cellsF_ne_tj i 5), Function.update_of_ne (cellsF_ne_tj i 4)]
      exact (mid4_free Mm G n c F Q P _).symm
    · rw [BitMachineClearBank.cleared_foreign _ _ _ (fun i h => hx ⟨i, h⟩)]
      have hnι : ¬ ∃ y, ι y = x := fun ⟨y, hy⟩ => by
        obtain ⟨i, hi⟩ := ι_mem y
        exact hx ⟨i, hi.trans hy⟩
      have hb : B3 x = M4 x := b3o x hnι
      rw [hSF', hSE']
      by_cases h8 : x = tailEmb (tj 8)
      · subst h8
        rw [Function.update_self, Function.update_of_ne d811, Function.update_self]
      by_cases h5 : x = tailEmb (tj 5)
      · subst h5
        rw [Function.update_of_ne d58, Function.update_self, Function.update_of_ne d511,
          Function.update_of_ne d58, Function.update_self]
      by_cases h11 : x = tailEmb (tj 11)
      · subst h11
        rw [Function.update_of_ne d811.symm, Function.update_of_ne d511.symm,
          Function.update_self, Function.update_self]
      by_cases h4 : x = tailEmb (tj 4)
      · subst h4
        rw [Function.update_of_ne d48, Function.update_of_ne d45, Function.update_of_ne d411,
          Function.update_self, Function.update_of_ne d411, Function.update_of_ne d48,
          Function.update_of_ne d45, Function.update_self]
      rw [Function.update_of_ne h8, Function.update_of_ne h5, Function.update_of_ne h11,
        Function.update_of_ne h4, Function.update_of_ne h8, hb, Function.update_of_ne h11,
        Function.update_of_ne h8, Function.update_of_ne h5, Function.update_of_ne h4]
  rw [hexit] at hG
  -- composition, innermost first
  obtain ⟨uFG, huFG, rFG⟩ := BitMachineRawSequence.runs
    (MatrixStage4ScalarPreparationOps.copyProgram ι3) (WeightedRawWords.clearProgram cellsF)
    _ _ _ _ _ _ _ _ _ _ _ hF hG
  obtain ⟨uEFG, huEFG, rEFG⟩ := BitMachineRawSequence.runs
    (MultiMove.program (jobsE.map CopyFill.toJob) tempW) QFG
    _ _ _ _ _ _ _ _ _ _ _ hE rFG
  obtain ⟨uD, huD, rD⟩ := BitMachineRawSequence.runs famP QEFG
    _ _ _ _ _ _ _ _ _ _ _ hD rEFG
  obtain ⟨uC, huC, rC⟩ := BitMachineRawSequence.runs
    (MultiMove.program (jobsC.map CopyFill.toJob) tempW) QDEFG
    _ _ _ _ _ _ _ _ _ _ _ hC rD
  obtain ⟨uB, huB, rB⟩ := BitMachineRawSequence.runs (pushP (ι pInF)) QCDEFG
    _ _ _ _ _ _ _ _ _ _ _ hB rC
  obtain ⟨u, hu, r⟩ := BitMachineRawSequence.runs
    (MultiMove.program (jobsA.map CopyFill.toJob) tempW) QBCDEFG
    _ _ _ _ _ _ _ _ _ _ _ hA rB
  refine ⟨u, ?_, _, r⟩
  have hnn' : nn ≤ famBound G n c := hnn
  unfold TF
  omega

#print axioms SF_eq
#print axioms tail_gap
#print axioms firstExp_eq
#print axioms family4

end EthInapproximability.CurrentPaper.EntryPrepFamily
