import EthInapproximability.CurrentPaper.OuterLevel0Prep

/-! Lane owner:b-weighted-level-5, unit 2, segment 1 (1c-c-outer), piece C.

`level0_prep_run`: ONE fixed program `prepProgram M c` runs from the branch
packet to the EXACT exit bank `exitBank G n c (G4 (level0RowsBank M G n c F Q P))`
(owner-4's `readyProgram` exit on the level-0 region, the closed-form outer
start region with unary `scale P0` and unary `b`, `c`, `bins P0` in the
outer-width/restoration inputs, blank scale region and temporary), within the
explicit clock `prepBound`.

`level0_physical_handoff`: from ANY bank that agrees with that exit bank on every
cell of the admitted protected bridge stack except writer 22 and holds
`d.rawBits` in writer 22 (THE named premise, lane owner:b-stage4-entry-program-3),
the admitted `MatrixTableInterlaceProtectedBridge.program`, embedded into the
same global stack, runs from its fixed start label/control within the admitted
`actualPhysicalBudget` to a halted configuration whose second-output cell is the
admitted `actualPhysicalOutput` (the next-level row-major word). -/

namespace EthInapproximability.CurrentPaper.OuterLevel0Run

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Ready
open OuterLevel0Prep

noncomputable section

set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

variable (M : BitMachine.Machine)
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem rIn_ne {i j : Fin 4} (h : i ≠ j) : rIn i ≠ rIn j := by
  intro e
  apply h
  have e1 : MatrixRestorationWidthMachine.inputStack i =
      MatrixRestorationWidthMachine.inputStack j := Sum.inl.inj (Sum.inr.inj e)
  have e2 := (Fintype.equivFin MatrixRestorationWidthMachineProduct.Stack).injective
    (Sum.inl.inj e1)
  exact Fin.ext (by simpa using congrArg Fin.val e2)

theorem oc_ne {o o' : OStk} (h : o ≠ o') : oc o ≠ oc o' :=
  fun e => h (Sum.inl.inj (Sum.inr.inj e))

theorem oIn_ne_rIn (i : Fin 4) : oIn ≠ rIn i := by intro e; cases e

/-- Length of every fresh scale cell after the admitted scale run. -/
theorem scale_growth (i : Parameters.Input) (t : ℕ) (Fs : SStack → List Bool)
    (h : ((advance ETHScaleActualComplete.program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel ETHScaleActualComplete.oldStart),
          (ETHScaleActualComplete.oldControl, ETHScaleActualComplete.finalControl),
          ETHScaleActualComplete.initialBank i⟩ :
          TM2.Cfg (fun _ : SStack => Bool) ETHScaleActualComplete.Label
            ETHScaleActualComplete.Control) =
        ⟨none, (ETHScaleActualComplete.oldControl, ScaleFinalScratch.base, none), Fs⟩)
    (x : SStack) :
    (Fs x).length ≤ ETHParameterScaleMachineInput.wordSize i +
      BitMachineStackGrowth.perStep ETHScaleActualComplete.program * t := by
  have g := BitMachineStackGrowth.run_growth ETHScaleActualComplete.program
    (⟨some (BitMachineRawSequence.leftLabel ETHScaleActualComplete.oldStart),
          (ETHScaleActualComplete.oldControl, ETHScaleActualComplete.finalControl),
          ETHScaleActualComplete.initialBank i⟩ :
          TM2.Cfg (fun _ : SStack => Bool) ETHScaleActualComplete.Label
            ETHScaleActualComplete.Control) t x
  rw [h] at g
  have hi : (ETHScaleActualComplete.initialBank i x).length ≤
      ETHParameterScaleMachineInput.wordSize i := by
    rcases x with (j | y) | y
    · rw [show ETHScaleActualComplete.initialBank i (.inl (.inl j)) =
          ETHParameterScaleMachineInput.words i j from
        bank_at ETHScaleActualComplete.oldEmbed (fun _ => [])
          (ETHScaleGlobalLog.initial i) (.inl j)]
      unfold ETHParameterScaleMachineInput.wordSize
      fin_cases j <;> simp [ETHParameterScaleMachineInput.words] <;> omega
    · rw [show ETHScaleActualComplete.initialBank i (.inl (.inr y)) = [] from
        bank_at ETHScaleActualComplete.oldEmbed (fun _ => [])
          (ETHScaleGlobalLog.initial i) (.inr y)]
      simp
    · rw [ETHScaleActualComplete.initialBank,
        bank_outside _ _ _ _ (by rintro ⟨k, hk⟩; cases hk)]
      simp
  exact le_trans g (by simpa using hi)

theorem level0_prep_run (G : EndpointGraph V E) (n c : ℕ) :
    ∃ F : ETHBinsJoinedScratch.Stack → List Bool,
    ∃ Q : WeightedGraphQJoined.Stack → List Bool,
    ∃ P : ChosenPrimeRaw.Stack → List Bool,
    ∃ t ≤ prepBound M G n c,
      ((advance (prepProgram M c))^[t])
        ⟨some (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (.inl (.scan 0)))))))),
          ((((((none, ((), ((WeightedRawWords.level0Ctrl, (WeightedRawWords.edgesCtrl, WeightedRawWords.tailCtrl)), WeightedRawWords.kCtrl M))), WeightedVertexWord.vertexCtrl), (WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit))), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27),
          H0 (SourceOriginalBranchPackets.packet n (EncodedGraph.encode (EncodedETHSource.serializeGraph G)))⟩ =
        ⟨none, ((((((none, ((), ((WeightedRawWords.level0Ctrl, (WeightedRawWords.edgesCtrl, WeightedRawWords.tailCtrl)), WeightedRawWords.kCtrl M))), WeightedVertexWord.vertexCtrl), (WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit))), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27),
          exitBank G n c (G4 (level0RowsBank M G n c F Q P))⟩ ∧
      level0Facts M G n c F Q P := by
  obtain ⟨F, Q, P, t1, ht1, h1, hf⟩ := level0_ready M G n c
  -- phase 1: owner-4 readyProgram, lifted
  have r1 := WeightedRawWords.region_run hG (readyProgram M c) _ _ t1 h1
    (H0 (SourceOriginalBranchPackets.packet n
      (EncodedGraph.encode (EncodedETHSource.serializeGraph G)))) (fun k => rfl)
  rw [bank_hG] at r1
  -- phase 2: the admitted scale controller, aliased onto the six raw words
  obtain ⟨t2, ht2, Fs, h2, hans, _, hraw⟩ := ETHScaleActualComplete.actual_scale_run (P0 G n c)
  have r2 := WeightedRawWords.region_run sEmb ETHScaleActualComplete.program _ _ t2 h2
    (K1 (G4 (level0RowsBank M G n c F Q P))) (scale_initial M G n c F Q P hf)
  -- facts about the bank after the scale stage
  have hK2G : ∀ g : GStack,
      bank sEmb (K1 (G4 (level0RowsBank M G n c F Q P))) Fs (.inl g) =
        G4 (level0RowsBank M G n c F Q P) g := by
    intro g
    by_cases hx : ∃ x, sEmb x = (.inl g : HStack)
    · obtain ⟨x, hx⟩ := hx
      rw [← hx, bank_at]
      rcases x with (j | y) | y
      · have e1 : Fs (.inl (.inl j)) = ETHParameterScaleMachineInput.words (P0 G n c) j := hraw j
        rw [e1, ← raw_words M G n c F Q P hf j]
        have e2 : rawSrc j = (.inl g : HStack) := hx
        rw [e2]
        rfl
      · cases hx
      · cases hx
    · rw [bank_outside _ _ _ _ hx]
      rfl
  have hK2O : ∀ o : OStk,
      bank sEmb (K1 (G4 (level0RowsBank M G n c F Q P))) Fs (oc o) = [] := by
    intro o
    rw [bank_outside _ _ _ _ (by
      rintro ⟨x, hx⟩
      rcases x with ((j | y) | y)
      · fin_cases j <;> cases hx
      · cases hx
      · cases hx)]
    rfl
  have hK2T : bank sEmb (K1 (G4 (level0RowsBank M G n c F Q P))) Fs tmpH = [] := by
    rw [bank_outside _ _ _ _ (by
      rintro ⟨x, hx⟩
      rcases x with ((j | y) | y)
      · fin_cases j <;> cases hx
      · cases hx
      · cases hx)]
    rfl
  have hK2A : bank sEmb (K1 (G4 (level0RowsBank M G n c F Q P))) Fs
      (fresh (.inr ScaleFinalScratch.answerKey)) =
      List.replicate (Parameters.scale (P0 G n c)) true := by
    rw [← sEmb_answer, bank_at]
    exact hans
  have hK2F : ∀ x : SStack,
      (bank sEmb (K1 (G4 (level0RowsBank M G n c F Q P))) Fs (fresh x)).length ≤
        ETHParameterScaleMachineInput.wordSize (P0 G n c) +
          BitMachineStackGrowth.perStep ETHScaleActualComplete.program *
            ETHScaleActualComplete.totalBound (P0 G n c) := by
    intro x
    have hg := scale_growth (P0 G n c) t2 Fs h2 x
    have hm : BitMachineStackGrowth.perStep ETHScaleActualComplete.program * t2 ≤
        BitMachineStackGrowth.perStep ETHScaleActualComplete.program *
          ETHScaleActualComplete.totalBound (P0 G n c) := Nat.mul_le_mul_left _ ht2
    rw [fresh_bank]
    rcases x with (j | y) | y
    · show ([] : List Bool).length ≤ _
      exact Nat.zero_le _
    · exact le_trans hg (by omega)
    · exact le_trans hg (by omega)
  -- phase 3: four charged copies
  let K2 := bank sEmb (K1 (G4 (level0RowsBank M G n c F Q P))) Fs
  let K3 := Function.update K2 (iL 1) (K2 (iL 0) ++ K2 (iL 1))
  let K4 := Function.update K3 (iB 1) (K3 (iB 0) ++ K3 (iB 1))
  let K5 := Function.update K4 (OuterLevel0Prep.iC 1) (K4 (OuterLevel0Prep.iC 0) ++ K4 (OuterLevel0Prep.iC 1))
  let K6 := Function.update K5 (iS 1) (K5 (iS 0) ++ K5 (iS 1))
  have hK2G' : ∀ g : GStack, K2 (.inl g) = G4 (level0RowsBank M G n c F Q P) g := hK2G
  have hK2O' : ∀ o : OStk, K2 (oc o) = [] := hK2O
  have hK2T' : K2 tmpH = [] := hK2T
  have hK2A' : K2 (fresh (.inr ScaleFinalScratch.answerKey)) =
      List.replicate (Parameters.scale (P0 G n c)) true := hK2A
  have hK2F' : ∀ x : SStack, (K2 (fresh x)).length ≤
      ETHParameterScaleMachineInput.wordSize (P0 G n c) +
        BitMachineStackGrowth.perStep ETHScaleActualComplete.program *
          ETHScaleActualComplete.totalBound (P0 G n c) := hK2F
  have hK6G : ∀ g : GStack, K6 (.inl g) = G4 (level0RowsBank M G n c F Q P) g := by
    intro g
    show Function.update K5 (oc (rIn 2)) _ (.inl g) = _
    rw [Function.update_of_ne (by intro h; cases h)]
    show Function.update K4 (oc (rIn 1)) _ (.inl g) = _
    rw [Function.update_of_ne (by intro h; cases h)]
    show Function.update K3 (oc (rIn 0)) _ (.inl g) = _
    rw [Function.update_of_ne (by intro h; cases h)]
    show Function.update K2 (oc oIn) _ (.inl g) = _
    rw [Function.update_of_ne (by intro h; cases h)]
    exact hK2G' g
  have hK6F : ∀ x : SStack, K6 (fresh x) = K2 (fresh x) := by
    intro x
    show Function.update K5 (oc (rIn 2)) _ (fresh x) = _
    rw [Function.update_of_ne (by intro h; cases h)]
    show Function.update K4 (oc (rIn 1)) _ (fresh x) = _
    rw [Function.update_of_ne (by intro h; cases h)]
    show Function.update K3 (oc (rIn 0)) _ (fresh x) = _
    rw [Function.update_of_ne (by intro h; cases h)]
    show Function.update K2 (oc oIn) _ (fresh x) = _
    rw [Function.update_of_ne (by intro h; cases h)]
  have hK6T : K6 tmpH = [] := by
    show Function.update K5 (oc (rIn 2)) _ tmpH = _
    rw [Function.update_of_ne (by intro h; cases h)]
    show Function.update K4 (oc (rIn 1)) _ tmpH = _
    rw [Function.update_of_ne (by intro h; cases h)]
    show Function.update K3 (oc (rIn 0)) _ tmpH = _
    rw [Function.update_of_ne (by intro h; cases h)]
    show Function.update K2 (oc oIn) _ tmpH = _
    rw [Function.update_of_ne (by intro h; cases h)]
    exact hK2T'
  have hv := WeightedLevel0Masters.masterC_values M G n c
  have hB : K3 (mcell .B) = List.replicate (EffectiveIteration.sourceDepth n) true := by
    show Function.update K2 (oc oIn) _ (mcell .B) = _
    rw [Function.update_of_ne (by intro h; cases h)]
    show K2 (.inl (Sum.inl (mc .B))) = _
    rw [hK2G', WeightedLevel0Masters.ready_master M G n c F Q P .B
      (by intro h; cases h) (by intro h; cases h) (by intro m h; cases h)]
    exact hv.2.1
  have hC : K4 (mcell .C) = List.replicate c true := by
    show Function.update K3 (oc (rIn 0)) _ (mcell .C) = _
    rw [Function.update_of_ne (by intro h; cases h)]
    show Function.update K2 (oc oIn) _ (mcell .C) = _
    rw [Function.update_of_ne (by intro h; cases h)]
    show K2 (.inl (Sum.inl (mc .C))) = _
    rw [hK2G', WeightedLevel0Masters.ready_master M G n c F Q P .C
      (by intro h; cases h) (by intro h; cases h) (by intro m h; cases h)]
    exact hv.1
  have hS : K5 (wcell 28) = List.replicate (Parameters.bins (P0 G n c)) true := by
    show Function.update K4 (oc (rIn 1)) _ (wcell 28) = _
    rw [Function.update_of_ne (by intro h; cases h)]
    show Function.update K3 (oc (rIn 0)) _ (wcell 28) = _
    rw [Function.update_of_ne (by intro h; cases h)]
    show Function.update K2 (oc oIn) _ (wcell 28) = _
    rw [Function.update_of_ne (by intro h; cases h)]
    show K2 (.inl (Sum.inl (wc 28))) = _
    rw [hK2G']
    exact writer28 M G n c F Q P hf
  have s3 := MatrixStage4ScalarPreparationOps.copy_run iL K2 hK2T'
  have l3 : (K2 (iL 0)).length = Parameters.scale (P0 G n c) := by
    show (K2 (fresh (.inr ScaleFinalScratch.answerKey))).length = _
    rw [hK2A', List.length_replicate]
  rw [l3] at s3
  have t4 : K3 (iB 2) = [] := by
    show Function.update K2 (oc oIn) _ tmpH = _
    rw [Function.update_of_ne (by intro h; cases h)]
    exact hK2T'
  have s4 := MatrixStage4ScalarPreparationOps.copy_run iB K3 t4
  have l4 : (K3 (iB 0)).length = EffectiveIteration.sourceDepth n := by
    show (K3 (mcell .B)).length = _
    rw [hB, List.length_replicate]
  rw [l4] at s4
  have t5 : K4 (OuterLevel0Prep.iC 2) = [] := by
    show Function.update K3 (oc (rIn 0)) _ tmpH = _
    rw [Function.update_of_ne (by intro h; cases h)]
    exact t4
  have s5 := MatrixStage4ScalarPreparationOps.copy_run OuterLevel0Prep.iC K4 t5
  have l5 : (K4 (OuterLevel0Prep.iC 0)).length = c := by
    show (K4 (mcell .C)).length = _
    rw [hC, List.length_replicate]
  rw [l5] at s5
  have t6 : K5 (iS 2) = [] := by
    show Function.update K4 (oc (rIn 1)) _ tmpH = _
    rw [Function.update_of_ne (by intro h; cases h)]
    exact t5
  have s6 := MatrixStage4ScalarPreparationOps.copy_run iS K5 t6
  have l6 : (K5 (iS 0)).length = Parameters.bins (P0 G n c) := by
    show (K5 (wcell 28)).length = _
    rw [hS, List.length_replicate]
  rw [l6] at s6
  -- phase 4: clear the fresh scale region
  have s7 := WeightedRawWords.clear_run cellsS cellsS_inj K6
  have l7 : (∑ i, (K6 (cellsS i)).length) ≤
      nS * (ETHParameterScaleMachineInput.wordSize (P0 G n c) +
        BitMachineStackGrowth.perStep ETHScaleActualComplete.program *
          ETHScaleActualComplete.totalBound (P0 G n c)) := by
    have hb : ∀ i ∈ (Finset.univ : Finset (Fin nS)), (K6 (cellsS i)).length ≤
        ETHParameterScaleMachineInput.wordSize (P0 G n c) +
          BitMachineStackGrowth.perStep ETHScaleActualComplete.program *
            ETHScaleActualComplete.totalBound (P0 G n c) := by
      intro i _
      show (K6 (fresh _)).length ≤ _
      rw [hK6F]
      exact hK2F' _
    have := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin nS)) _ _ hb
    simpa [Finset.card_univ, Fintype.card_fin, smul_eq_mul] using this
  -- compose (six charged handoffs)
  obtain ⟨u6, hu6, q6⟩ := BitMachineRawSequence.runs cpS clearS _ _ _ _ _ _ K5 K6
    (BitMachineClearBank.cleared cellsS K6) _ _ s6 s7
  obtain ⟨u5, hu5, q5⟩ := BitMachineRawSequence.runs cpC p67 _ _ _ _ _ _ K4 K5
    (BitMachineClearBank.cleared cellsS K6) _ _ s5 q6
  obtain ⟨u4, hu4, q4⟩ := BitMachineRawSequence.runs cpB p57 _ _ _ _ _ _ K3 K4
    (BitMachineClearBank.cleared cellsS K6) _ _ s4 q5
  obtain ⟨u3, hu3, q3⟩ := BitMachineRawSequence.runs cpL p47 _ _ _ _ _ _ K2 K3
    (BitMachineClearBank.cleared cellsS K6) _ _ s3 q4
  obtain ⟨u2, hu2, q2⟩ := BitMachineRawSequence.runs liftScale p37 _ _ _ _ _ _
    (K1 (G4 (level0RowsBank M G n c F Q P))) K2
    (BitMachineClearBank.cleared cellsS K6) _ _ r2 q3
  obtain ⟨u1, hu1, q1⟩ := BitMachineRawSequence.runs (liftReady M c) p27 _ _ _ _ _ _
    (H0 (SourceOriginalBranchPackets.packet n
      (EncodedGraph.encode (EncodedETHSource.serializeGraph G))))
    (K1 (G4 (level0RowsBank M G n c F Q P)))
    (BitMachineClearBank.cleared cellsS K6) _ _ r1 q2
  -- the exit bank is exactly `exitBank`
  have hexit : BitMachineClearBank.cleared cellsS K6 =
      exitBank G n c (G4 (level0RowsBank M G n c F Q P)) := by
    funext z
    rcases z with g | (o | (x | u))
    · rw [BitMachineClearBank.cleared_foreign _ _ _ (by intro i h; cases h)]
      exact hK6G g
    · rw [BitMachineClearBank.cleared_foreign _ _ _ (by intro i h; cases h)]
      show K6 (oc o) = OuterStartBank.outerTarget _ _ _ _ o
      rw [outerTarget_cells]
      by_cases e0 : o = oIn
      · subst e0
        rw [if_pos rfl]
        show Function.update K5 (oc (rIn 2)) _ (oc oIn) = _
        rw [Function.update_of_ne (oc_ne (oIn_ne_rIn 2))]
        show Function.update K4 (oc (rIn 1)) _ (oc oIn) = _
        rw [Function.update_of_ne (oc_ne (oIn_ne_rIn 1))]
        show Function.update K3 (oc (rIn 0)) _ (oc oIn) = _
        rw [Function.update_of_ne (oc_ne (oIn_ne_rIn 0))]
        show Function.update K2 (oc oIn) _ (oc oIn) = _
        rw [Function.update_self]
        show K2 (fresh (.inr ScaleFinalScratch.answerKey)) ++ K2 (oc oIn) = _
        rw [hK2A', hK2O', List.append_nil]
      rw [if_neg e0]
      by_cases e1 : o = rIn 0
      · subst e1
        rw [if_pos rfl]
        show Function.update K5 (oc (rIn 2)) _ (oc (rIn 0)) = _
        rw [Function.update_of_ne (oc_ne (rIn_ne (by decide)))]
        show Function.update K4 (oc (rIn 1)) _ (oc (rIn 0)) = _
        rw [Function.update_of_ne (oc_ne (rIn_ne (by decide)))]
        show Function.update K3 (oc (rIn 0)) _ (oc (rIn 0)) = _
        rw [Function.update_self]
        show K3 (mcell .B) ++ K3 (oc (rIn 0)) = _
        rw [hB]
        show _ ++ Function.update K2 (oc oIn) _ (oc (rIn 0)) = _
        rw [Function.update_of_ne (oc_ne (oIn_ne_rIn 0)).symm, hK2O', List.append_nil]
      rw [if_neg e1]
      by_cases e2 : o = rIn 1
      · subst e2
        rw [if_pos rfl]
        show Function.update K5 (oc (rIn 2)) _ (oc (rIn 1)) = _
        rw [Function.update_of_ne (oc_ne (rIn_ne (by decide)))]
        show Function.update K4 (oc (rIn 1)) _ (oc (rIn 1)) = _
        rw [Function.update_self]
        show K4 (mcell .C) ++ K4 (oc (rIn 1)) = _
        rw [hC]
        show _ ++ Function.update K3 (oc (rIn 0)) _ (oc (rIn 1)) = _
        rw [Function.update_of_ne (oc_ne (rIn_ne (by decide)))]
        show _ ++ Function.update K2 (oc oIn) _ (oc (rIn 1)) = _
        rw [Function.update_of_ne (oc_ne (oIn_ne_rIn 1)).symm, hK2O', List.append_nil]
      rw [if_neg e2]
      by_cases e3 : o = rIn 2
      · subst e3
        rw [if_pos rfl]
        show Function.update K5 (oc (rIn 2)) _ (oc (rIn 2)) = _
        rw [Function.update_self]
        show K5 (wcell 28) ++ K5 (oc (rIn 2)) = _
        rw [hS]
        show _ ++ Function.update K4 (oc (rIn 1)) _ (oc (rIn 2)) = _
        rw [Function.update_of_ne (oc_ne (rIn_ne (by decide)))]
        show _ ++ Function.update K3 (oc (rIn 0)) _ (oc (rIn 2)) = _
        rw [Function.update_of_ne (oc_ne (rIn_ne (by decide)))]
        show _ ++ Function.update K2 (oc oIn) _ (oc (rIn 2)) = _
        rw [Function.update_of_ne (oc_ne (oIn_ne_rIn 2)).symm, hK2O', List.append_nil]
      rw [if_neg e3]
      show Function.update K5 (oc (rIn 2)) _ (oc o) = _
      rw [Function.update_of_ne (oc_ne e3)]
      show Function.update K4 (oc (rIn 1)) _ (oc o) = _
      rw [Function.update_of_ne (oc_ne e2)]
      show Function.update K3 (oc (rIn 0)) _ (oc o) = _
      rw [Function.update_of_ne (oc_ne e1)]
      show Function.update K2 (oc oIn) _ (oc o) = _
      rw [Function.update_of_ne (oc_ne e0)]
      exact hK2O' o
    · have e : cellsS (Fintype.equivFin SStack x) = fresh x := by
        show fresh ((Fintype.equivFin SStack).symm (Fintype.equivFin SStack x)) = _
        rw [Equiv.symm_apply_apply]
      show BitMachineClearBank.cleared cellsS K6 (fresh x) = []
      rw [← e]
      exact BitMachineClearBank.cleared_bank cellsS K6 _
    · rw [BitMachineClearBank.cleared_foreign _ _ _ (by intro i h; cases h)]
      exact hK6T
  rw [hexit] at q1
  refine ⟨F, Q, P, u1, ?_, q1, hf⟩
  have ht1' : t1 ≤ readyBound M G n c := ht1
  unfold prepBound outerBound
  omega

#print axioms rIn_ne
#print axioms scale_growth
#print axioms level0_prep_run

end
end EthInapproximability.CurrentPaper.OuterLevel0Run
