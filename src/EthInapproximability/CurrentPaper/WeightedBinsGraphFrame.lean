import EthInapproximability.CurrentPaper.WeightedBinsGraphQ

/-! Re-expose the same-run writer frame discarded by the frozen aggregate
bins/graph theorem. This file reuses its physical controller unchanged. -/

namespace EthInapproximability.CurrentPaper.WeightedBinsGraphFrame

open Turing BitMachineEncoding BitMachineStackEmbedding
open WeightedBinsGraphQ
noncomputable section

private theorem base_writer (g : EncodedGraph.Graph)
    (W : Fin 64 → List Bool) (k : Fin 64) :
    base g W (writer k) = W k := by
  change WeightedGraphQJoined.initialBank g W
    (WeightedGraphQJoined.writer k) = _
  rw [WeightedGraphQJoined.initialBank,WeightedGraphQJoined.lift]
  change bank WeightedGraphQJoined.parserWriterSlots (fun _ => [])
    (GraphVertexPreludeJoin.parserStart g W).stk
    (WeightedGraphQJoined.parserWriterSlots (.inr k)) = _
  rw [bank_at]
  have hout : ¬ ∃ j : SourceNormalizationMachineDecode.Stack,
      GraphVertexPreludeJoin.parserSlots j =
        (.inr k : GraphVertexPreludeJoin.Stack) := by
    rintro ⟨j,h⟩; cases h
  change bank GraphVertexPreludeJoin.parserSlots
    (Sum.elim (fun _ => []) W)
    (SourceNormalizationMachineDecode.guardedStart
      (true :: EncodedGraph.encode g)).stk (.inr k) = _
  rw [bank_outside _ _ _ _ hout]
  rfl

private theorem graph_initial_parser (g : EncodedGraph.Graph)
    (W : Fin 64 → List Bool)
    (p : SourceNormalizationMachineDecode.Stack) :
    WeightedGraphQJoined.initialBank g W (.inl (.inl p)) =
      (SourceNormalizationMachineDecode.guardedStart
        (true :: EncodedGraph.encode g)).stk p := by
  change bank WeightedGraphQJoined.parserWriterSlots (fun _ => [])
    (GraphVertexPreludeJoin.parserStart g W).stk
    (WeightedGraphQJoined.parserWriterSlots (.inl p)) = _
  rw [bank_at]
  change bank GraphVertexPreludeJoin.parserSlots
    (Sum.elim (fun _ => []) W)
    (SourceNormalizationMachineDecode.guardedStart
      (true :: EncodedGraph.encode g)).stk
    (GraphVertexPreludeJoin.parserSlots p) = _
  rw [bank_at]

private theorem graph_initial_private (g : EncodedGraph.Graph)
    (W : Fin 64 → List Bool) (j : Fin 10 ⊕ QProduct.LogStack) :
    WeightedGraphQJoined.initialBank g W (.inr j) = [] := by
  have hout : ¬ ∃ k : GraphVertexPreludeJoin.Stack,
      WeightedGraphQJoined.parserWriterSlots k =
        (.inr j : QProduct.Stack) := by
    rintro ⟨k,h⟩; cases h
  change bank WeightedGraphQJoined.parserWriterSlots (fun _ => [])
    (GraphVertexPreludeJoin.parserStart g W).stk (.inr j) = []
  rw [bank_outside _ _ _ _ hout]

private theorem initial_graph_projection (i : Parameters.Input)
    (g : EncodedGraph.Graph) (W : Fin 64 → List Bool)
    (F : ETHBinsJoinedScratch.Stack → List Bool) :
    (fun j : WeightedGraphQJoined.Stack =>
      (afterBins i g W F) (graphSlots j)) =
      WeightedGraphQJoined.initialBank g
        (Function.update W 28
          (List.replicate (Parameters.bins i) true)) := by
  funext j
  cases j with
  | inl x =>
      cases x with
      | inl p =>
          have hout : ¬ ∃ k : WeightedBinsGeneric.Stack,
              binSlots k = graphSlots (.inl (.inl p)) := by
            rintro ⟨k,h⟩
            cases k with
            | inl k => cases h
            | inr k => cases h
          change bank binSlots (base g W)
            (WeightedBinsGeneric.finalBank W F i)
            (graphSlots (.inl (.inl p))) = _
          rw [bank_outside _ _ _ _ hout]
          change WeightedGraphQJoined.initialBank g W (.inl (.inl p)) =
            WeightedGraphQJoined.initialBank g
              (Function.update W 28
                (List.replicate (Parameters.bins i) true)) (.inl (.inl p))
          rw [graph_initial_parser,graph_initial_parser]
      | inr k =>
          change bank binSlots (base g W)
            (WeightedBinsGeneric.finalBank W F i)
            (binSlots (.inr k)) = _
          rw [bank_at]
          change (WeightedBinsGeneric.finalBank W F i)
            (WeightedBinsGeneric.writer k) =
            WeightedGraphQJoined.initialBank g
              (Function.update W 28
                (List.replicate (Parameters.bins i) true))
              (WeightedGraphQJoined.writer k)
          have hright := base_writer g
            (Function.update W 28
              (List.replicate (Parameters.bins i) true)) k
          change (WeightedBinsGeneric.finalBank W F i)
              (WeightedBinsGeneric.writer k) = base g
            (Function.update W 28
              (List.replicate (Parameters.bins i) true))
              (writer k)
          rw [hright]
          by_cases hk : k = 28
          · subst k
            simp [WeightedBinsGeneric.finalBank,
              WeightedBinsGeneric.writer,base_writer,
              WeightedBinsGeneric.writer]
          · have hout : ¬ ∃ p : ETHBinsJoinedScratch.Stack,
                WeightedBinsGeneric.paramSlots p =
                  (WeightedBinsGeneric.writer k : WeightedBinsGeneric.Stack) := by
              rintro ⟨p,h⟩; cases h
            have hn : WeightedBinsGeneric.writer k ≠
                WeightedBinsGeneric.writer 28 := by
              simpa [WeightedBinsGeneric.writer] using hk
            rw [WeightedBinsGeneric.finalBank,
              Function.update_of_ne hn,
              WeightedBinsGeneric.afterBins,
              bank_outside _ _ _ _ hout]
            simp [WeightedBinsGeneric.foreignBank,
              WeightedBinsGeneric.writer,base_writer,base,
              Function.update_of_ne hk]
  | inr j =>
      have hout : ¬ ∃ k : WeightedBinsGeneric.Stack,
          binSlots k = graphSlots (.inr j) := by
        rintro ⟨k,h⟩
        cases k with
        | inl k => cases h
        | inr k => cases h
      change bank binSlots (base g W)
        (WeightedBinsGeneric.finalBank W F i)
        (graphSlots (.inr j)) = _
      rw [bank_outside _ _ _ _ hout]
      change WeightedGraphQJoined.initialBank g W (.inr j) =
        WeightedGraphQJoined.initialBank g
          (Function.update W 28
            (List.replicate (Parameters.bins i) true)) (.inr j)
      rw [graph_initial_private,graph_initial_private]

private theorem prelude_writer_other (g : EncodedGraph.Graph)
    (W : Fin 64 → List Bool) (s : ℕ) (k : Fin 64)
    (h7 : k ≠ 7) (h8 : k ≠ 8) (h9 : k ≠ 9)
    (h10 : k ≠ 10) (h11 : k ≠ 11) (h12 : k ≠ 12)
    (h13 : k ≠ 13) (h14 : k ≠ 14)
    (h15 : k ≠ 15) (h18 : k ≠ 18)
    (h54 : k ≠ 54) (h55 : k ≠ 55) (h60 : k ≠ 60) :
    (WeightedGraphQJoined.afterPrelude g W s)
      (WeightedGraphQJoined.writer k) = W k := by
  change bank WeightedGraphQJoined.parserWriterSlots (fun _ => [])
    (GraphVertexPreludeJoin.finalBank g W s)
    (WeightedGraphQJoined.parserWriterSlots (.inr k)) = _
  rw [bank_at]
  change bank GraphVertexPreludeJoin.writerSlots
    (GraphVertexPreludeJoin.copied g W).stk _
    (GraphVertexPreludeJoin.writerSlots k) = _
  rw [bank_at]
  have hc : ∀ j : Fin 8,
      MatrixWeightedOrderPreparation.scratchSlots j ≠ k := by
    intro j
    fin_cases j <;>
      simp_all [MatrixWeightedOrderPreparation.scratchSlots,eq_comm]
  rw [MatrixWeightedOrderPreparation.readyBank,
    BitMachineClearBank.cleared_foreign _ _ _ hc]
  have ho : ¬ ∃ j : Fin 9,
      MatrixWeightedOrderPreparation.slots j = k := by
    rintro ⟨j,h⟩
    fin_cases j <;>
      simp_all [MatrixWeightedOrderPreparation.slots,eq_comm]
  rw [MatrixWeightedOrderPreparation.producedBank,
    bank_outside _ _ _ _ ho]
  rw [MatrixWeightedGraphItemCountsPrelude.final_foreign
    _ _ _ _ h7 h8 h9 h15 h18 h54]
  exact GraphVertexPreludeJoin.writerAfter_other g W k h54 h55

/-- The same bins/graph/q run, now retaining the already proved writer frame
at the bin and incoming-column cells. No source or controller is rerun. -/
theorem source_run_framed {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (i : Parameters.Input)
    (G : ParameterizedNP.GuardedSourceGraph.EndpointGraph V E)
    (W : Fin 64 → List Bool)
    (h28 : W 28 = []) (h61 : W 61 = [])
    (h7 : W 7 = []) (h8 : W 8 = []) (h9 : W 9 = [])
    (h10 : W 10 = []) (h11 : W 11 = []) (h12 : W 12 = [])
    (h13 : W 13 = []) (h14 : W 14 = [])
    (h15 : W 15 = []) (h18 : W 18 = [])
    (h54 : W 54 = []) (h55 : W 55 = []) (h56 : W 56 = [])
    (h57 : W 57 = []) (h58 : W 58 = []) (h60 : W 60 = []) :
    let g := EncodedETHSource.serializeGraph G
    ∃ u ≤ WeightedBinsGraphQ.bound i g (Fintype.card E),
      ∃ v : Fin ETHBinsStandaloneScratch.machine.controlCount,
      ∃ F : ETHBinsJoinedScratch.Stack → List Bool,
      ∃ Q : WeightedGraphQJoined.Stack → List Bool,
        ((advance WeightedBinsGraphQ.program)^[u])
          (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel BinsWriterAssembly.binStart)),
            WeightedBinsGraphQ.initialControl,
            WeightedBinsGraphQ.initialBank i g W⟩ :
            TM2.Cfg (fun _ : WeightedBinsGraphQ.Stack => Bool) _ _) =
          ⟨none,WeightedBinsGraphQ.initialControl,
            WeightedBinsGraphQ.afterGraph i g W F Q⟩ ∧
        (WeightedBinsGraphQ.afterGraph i g W F Q)
          (WeightedBinsGraphQ.writer 56) =
          List.replicate
            (ParameterizedNP.GuardedSourceSlab.q2 G (Parameters.bins i)) true ∧
        (WeightedBinsGraphQ.afterGraph i g W F Q)
          (WeightedBinsGraphQ.writer 54) = [] ∧
        (WeightedBinsGraphQ.afterGraph i g W F Q)
          (WeightedBinsGraphQ.writer 17) = W 17 ∧
        (WeightedBinsGraphQ.afterGraph i g W F Q)
          (WeightedBinsGraphQ.writer 57) = W 57 ∧
        (WeightedBinsGraphQ.afterGraph i g W F Q)
          (WeightedBinsGraphQ.writer 28) =
          List.replicate (Parameters.bins i) true ∧
        (WeightedBinsGraphQ.afterGraph i g W F Q)
          (WeightedBinsGraphQ.writer 27) = W 27 ∧
        F (.inl (.inr ScaleFinalScratch.answerKey)) =
          List.replicate (Parameters.scale i) true ∧
        (∀ p : ETHBinsJoinedScratch.Stack,
          (WeightedBinsGraphQ.afterGraph i g W F Q) (.inl p) = F p) := by
  let g := EncodedETHSource.serializeGraph G
  let s := Parameters.bins i
  let W' := Function.update W 28 (List.replicate s true)
  obtain ⟨ub,hub,v,F,hb,hbin,hscale,hbw⟩ :=
    WeightedBinsGeneric.run i W h28 h61
  have hBin :
      ((advance WeightedBinsGraphQ.binProgram)^[ub])
        (⟨some (BitMachineRawSequence.leftLabel
          BinsWriterAssembly.binStart),
          WeightedBinsGeneric.initialControl,
          WeightedBinsGraphQ.initialBank i g W⟩ :
          TM2.Cfg (fun _ : WeightedBinsGraphQ.Stack => Bool) _ _) =
        ⟨none,WeightedBinsGeneric.initialControl,
          WeightedBinsGraphQ.afterBins i g W F⟩ := by
    have he := BitMachineStackRun.run WeightedBinsGraphQ.binSlots
      (WeightedBinsGraphQ.base g W) WeightedBinsGeneric.program
      (⟨some (BitMachineRawSequence.leftLabel
        BinsWriterAssembly.binStart),
        WeightedBinsGeneric.initialControl,
        WeightedBinsGeneric.initialBank i W⟩ :
        TM2.Cfg (fun _ : WeightedBinsGeneric.Stack => Bool) _ _) ub
    rw [hb] at he
    simpa only [WeightedBinsGraphQ.binProgram,
      WeightedBinsGraphQ.initialBank,WeightedBinsGraphQ.afterBins,stackCfg]
      using he
  have hW' (k : Fin 64) (hk : k ≠ 28) (h : W k = []) :
      W' k = [] := by
    simpa [W',Function.update_of_ne hk] using h
  obtain ⟨ug,hug,Q,hg,hq,hq54,hq17,hq57,hframe⟩ :=
    WeightedGraphQJoined.source_run G W' s
      (by simp [W'])
      (hW' 7 (by decide) h7)
      (hW' 8 (by decide) h8)
      (hW' 9 (by decide) h9)
      (hW' 10 (by decide) h10)
      (hW' 11 (by decide) h11)
      (hW' 12 (by decide) h12)
      (hW' 13 (by decide) h13)
      (hW' 14 (by decide) h14)
      (hW' 15 (by decide) h15)
      (hW' 18 (by decide) h18)
      (hW' 54 (by decide) h54)
      (hW' 55 (by decide) h55)
      (hW' 56 (by decide) h56)
      (hW' 57 (by decide) h57)
      (hW' 58 (by decide) h58)
      (hW' 60 (by decide) h60)
  let B := WeightedBinsGraphQ.afterBins i g W F
  have hp : (fun j : WeightedGraphQJoined.Stack =>
      B (WeightedBinsGraphQ.graphSlots j)) =
      WeightedGraphQJoined.initialBank g W' := by
    simpa only [B,W',s] using initial_graph_projection i g W F
  have hi : bank WeightedBinsGraphQ.graphSlots B
      (WeightedGraphQJoined.initialBank g W') = B :=
    bank_eq_self WeightedBinsGraphQ.graphSlots B _
      (fun j => (congrFun hp j).symm)
  have hGraph :
      ((advance WeightedBinsGraphQ.graphProgram)^[ug])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel (.inr .gate)))),
          WeightedGraphQJoined.initialControl,B⟩ :
          TM2.Cfg (fun _ : WeightedBinsGraphQ.Stack => Bool) _ _) =
        ⟨none,WeightedGraphQJoined.initialControl,
          WeightedBinsGraphQ.afterGraph i g W F Q⟩ := by
    have he := BitMachineStackRun.run WeightedBinsGraphQ.graphSlots B
      WeightedGraphQJoined.program
      (⟨some (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel (.inr .gate)))),
        WeightedGraphQJoined.initialControl,
        WeightedGraphQJoined.initialBank g W'⟩ :
        TM2.Cfg (fun _ : WeightedGraphQJoined.Stack => Bool) _ _) ug
    rw [hg] at he
    simpa only [WeightedBinsGraphQ.graphProgram,
      WeightedBinsGraphQ.afterGraph,stackCfg,hi,B] using he
  obtain ⟨u,hu,hr⟩ := BitMachineRawSequence.runs
    WeightedBinsGraphQ.binProgram WeightedBinsGraphQ.graphProgram
    (BitMachineRawSequence.leftLabel BinsWriterAssembly.binStart)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel (.inr .gate))))
    WeightedBinsGeneric.initialControl WeightedBinsGeneric.initialControl
    WeightedGraphQJoined.initialControl WeightedGraphQJoined.initialControl
    (WeightedBinsGraphQ.initialBank i g W) B
    (WeightedBinsGraphQ.afterGraph i g W F Q)
    ub ug hBin hGraph
  have hug' : ug ≤ WeightedGraphQJoined.bound g s (Fintype.card E) := by
    simpa only [g] using hug
  refine ⟨u,by change u ≤ WeightedBinsGeneric.bound i +
    WeightedGraphQJoined.bound g s (Fintype.card E) + 1; omega,
    v,F,Q,?_,?_,?_,?_,?_,?_,?_,hscale,?_⟩
  · simpa only [WeightedBinsGraphQ.program,
      WeightedBinsGraphQ.initialControl,B] using hr
  · change (bank WeightedBinsGraphQ.graphSlots B Q)
      (WeightedBinsGraphQ.graphSlots (WeightedGraphQJoined.writer 56)) = _
    rw [bank_at]
    exact hq
  · change (bank WeightedBinsGraphQ.graphSlots B Q)
      (WeightedBinsGraphQ.graphSlots (WeightedGraphQJoined.writer 54)) = _
    rw [bank_at]
    exact hq54
  · change (bank WeightedBinsGraphQ.graphSlots B Q)
      (WeightedBinsGraphQ.graphSlots (WeightedGraphQJoined.writer 17)) = _
    rw [bank_at]
    simpa only [W',Function.update_of_ne (by decide : (17 : Fin 64) ≠ 28)]
      using hq17
  · change (bank WeightedBinsGraphQ.graphSlots B Q)
      (WeightedBinsGraphQ.graphSlots (WeightedGraphQJoined.writer 57)) = _
    rw [bank_at]
    simpa only [W',Function.update_of_ne (by decide : (57 : Fin 64) ≠ 28)]
      using hq57
  · change (bank WeightedBinsGraphQ.graphSlots B Q)
      (WeightedBinsGraphQ.graphSlots (WeightedGraphQJoined.writer 28)) = _
    rw [bank_at]
    exact (hframe 28 (by decide)).trans
      (prelude_writer_other g W' s 28
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) |>.trans
          (by simp [W',s]))
  · change (bank WeightedBinsGraphQ.graphSlots B Q)
      (WeightedBinsGraphQ.graphSlots (WeightedGraphQJoined.writer 27)) = _
    rw [bank_at]
    exact (hframe 27 (by decide)).trans
      (prelude_writer_other g W' s 27
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) |>.trans
          (by simp [W']))
  · intro p
    have hout : ¬ ∃ j : WeightedGraphQJoined.Stack,
        WeightedBinsGraphQ.graphSlots j = (.inl p : WeightedBinsGraphQ.Stack) := by
      rintro ⟨j,h⟩; cases h
    change (bank WeightedBinsGraphQ.graphSlots B Q) (.inl p) = F p
    rw [bank_outside _ _ _ _ hout]
    change bank WeightedBinsGraphQ.binSlots (WeightedBinsGraphQ.base g W)
      (WeightedBinsGeneric.finalBank W F i)
      (WeightedBinsGraphQ.binSlots (.inl p)) = F p
    rw [bank_at]
    simp [WeightedBinsGeneric.finalBank,
      WeightedBinsGeneric.afterBins,WeightedBinsGeneric.writer]
    change bank WeightedBinsGeneric.paramSlots
      (WeightedBinsGeneric.foreignBank W) F
      (WeightedBinsGeneric.paramSlots p) = F p
    rw [bank_at]

#print axioms initial_graph_projection
#print axioms source_run_framed

end
end EthInapproximability.CurrentPaper.WeightedBinsGraphFrame
