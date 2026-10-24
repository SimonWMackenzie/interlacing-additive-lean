import EthInapproximability.CurrentPaper.WeightedBinsGeneric
import EthInapproximability.CurrentPaper.WeightedGraphQJoined
import EthInapproximability.CurrentPaper.BitMachineStackRun

/-! Actual six raw parameter words and literal guarded source graph share one
physical bank. Bins are installed into writer28 before the graph/order/q
controller starts; no second raw-six copy or edge-count oracle is present. -/

namespace EthInapproximability.CurrentPaper.WeightedBinsGraphQ

open Turing BitMachineEncoding BitMachineStackEmbedding
noncomputable section

abbrev Stack := ETHBinsJoinedScratch.Stack ⊕ WeightedGraphQJoined.Stack
def binSlots : WeightedBinsGeneric.Stack ↪ Stack where
  toFun
    | .inl p => .inl p
    | .inr k => .inr (WeightedGraphQJoined.writer k)
  inj' := by
    intro a b h
    rcases a with a | a <;> rcases b with b | b
    · cases h; rfl
    · cases h
    · cases h
    · change Sum.inr (WeightedGraphQJoined.writer a) =
        Sum.inr (WeightedGraphQJoined.writer b) at h
      cases h; rfl
def graphSlots : WeightedGraphQJoined.Stack ↪ Stack :=
  ⟨Sum.inr,by intro a b h; exact Sum.inr_injective h⟩
def writer (k : Fin 64) : Stack :=
  .inr (WeightedGraphQJoined.writer k)
def base (g : EncodedGraph.Graph) (W : Fin 64 → List Bool) :
    Stack → List Bool :=
  Sum.elim (fun _ => []) (WeightedGraphQJoined.initialBank g W)
def initialBank (i : Parameters.Input) (g : EncodedGraph.Graph)
    (W : Fin 64 → List Bool) : Stack → List Bool :=
  bank binSlots (base g W) (WeightedBinsGeneric.initialBank i W)
def afterBins (i : Parameters.Input) (g : EncodedGraph.Graph)
    (W : Fin 64 → List Bool)
    (F : ETHBinsJoinedScratch.Stack → List Bool) : Stack → List Bool :=
  bank binSlots (base g W) (WeightedBinsGeneric.finalBank W F i)
def afterGraph (i : Parameters.Input) (g : EncodedGraph.Graph)
    (W : Fin 64 → List Bool)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) : Stack → List Bool :=
  bank graphSlots (afterBins i g W F) Q
def binProgram := fun l => stackStmt binSlots (WeightedBinsGeneric.program l)
def graphProgram := fun l => stackStmt graphSlots (WeightedGraphQJoined.program l)
def program := BitMachineRawSequence.program binProgram graphProgram
  (BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (.inr .gate))))
  WeightedBinsGeneric.initialControl WeightedGraphQJoined.initialControl
def initialControl :=
  (WeightedBinsGeneric.initialControl,WeightedGraphQJoined.initialControl)
def bound (i : Parameters.Input) (g : EncodedGraph.Graph) (e : ℕ) :=
  WeightedBinsGeneric.bound i +
  WeightedGraphQJoined.bound g (Parameters.bins i) e + 1

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
      WeightedGraphQJoined.parserWriterSlots k = (.inr j : QProduct.Stack) := by
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

/-- The raw-six bins program and the literal-graph/order/q program execute
sequentially on one bank, with the actual bin word handed to graph preparation.
The parser is not reset or rerun for q. -/
theorem source_run {V E : Type*} [Fintype V] [DecidableEq V]
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
    ∃ u ≤ bound i g (Fintype.card E),
      ∃ v : Fin ETHBinsStandaloneScratch.machine.controlCount,
      ∃ F : ETHBinsJoinedScratch.Stack → List Bool,
      ∃ Q : WeightedGraphQJoined.Stack → List Bool,
        ((advance program)^[u])
          (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel BinsWriterAssembly.binStart)),
            initialControl,initialBank i g W⟩ :
            TM2.Cfg (fun _ : Stack => Bool) _ _) =
          ⟨none,initialControl,afterGraph i g W F Q⟩ ∧
        (afterGraph i g W F Q) (writer 56) =
          List.replicate
            (ParameterizedNP.GuardedSourceSlab.q2 G (Parameters.bins i)) true ∧
        (afterGraph i g W F Q) (writer 54) = [] ∧
        (afterGraph i g W F Q) (writer 17) = W 17 ∧
        (afterGraph i g W F Q) (writer 57) = W 57 ∧
        F (.inl (.inr ScaleFinalScratch.answerKey)) =
          List.replicate (Parameters.scale i) true ∧
        (∀ p : ETHBinsJoinedScratch.Stack,
          (afterGraph i g W F Q) (.inl p) = F p) := by
  let g := EncodedETHSource.serializeGraph G
  let s := Parameters.bins i
  let W' := Function.update W 28 (List.replicate s true)
  obtain ⟨ub,hub,v,F,hb,hbin,hscale,hbw⟩ :=
    WeightedBinsGeneric.run i W h28 h61
  have hBin :
      ((advance binProgram)^[ub])
        (⟨some (BitMachineRawSequence.leftLabel
          BinsWriterAssembly.binStart),
          WeightedBinsGeneric.initialControl,initialBank i g W⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,WeightedBinsGeneric.initialControl,
          afterBins i g W F⟩ := by
    have he := BitMachineStackRun.run binSlots (base g W)
      WeightedBinsGeneric.program
      (⟨some (BitMachineRawSequence.leftLabel
        BinsWriterAssembly.binStart),
        WeightedBinsGeneric.initialControl,
        WeightedBinsGeneric.initialBank i W⟩ :
        TM2.Cfg (fun _ : WeightedBinsGeneric.Stack => Bool) _ _) ub
    rw [hb] at he
    simpa only [binProgram,initialBank,afterBins,stackCfg] using he
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
  let B := afterBins i g W F
  have hp : (fun j : WeightedGraphQJoined.Stack => B (graphSlots j)) =
      WeightedGraphQJoined.initialBank g W' := by
    simpa only [B,W',s] using initial_graph_projection i g W F
  have hi : bank graphSlots B
      (WeightedGraphQJoined.initialBank g W') = B :=
    bank_eq_self graphSlots B _ (fun j => (congrFun hp j).symm)
  have hGraph :
      ((advance graphProgram)^[ug])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel (.inr .gate)))),
          WeightedGraphQJoined.initialControl,B⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,WeightedGraphQJoined.initialControl,
          afterGraph i g W F Q⟩ := by
    have he := BitMachineStackRun.run graphSlots B
      WeightedGraphQJoined.program
      (⟨some (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel (.inr .gate)))),
        WeightedGraphQJoined.initialControl,
        WeightedGraphQJoined.initialBank g W'⟩ :
        TM2.Cfg (fun _ : WeightedGraphQJoined.Stack => Bool) _ _) ug
    rw [hg] at he
    simpa only [graphProgram,afterGraph,stackCfg,hi,B] using he
  obtain ⟨u,hu,hr⟩ := BitMachineRawSequence.runs
    binProgram graphProgram
    (BitMachineRawSequence.leftLabel BinsWriterAssembly.binStart)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel (.inr .gate))))
    WeightedBinsGeneric.initialControl WeightedBinsGeneric.initialControl
    WeightedGraphQJoined.initialControl WeightedGraphQJoined.initialControl
    (initialBank i g W) B (afterGraph i g W F Q)
    ub ug hBin hGraph
  have hug' : ug ≤ WeightedGraphQJoined.bound g s (Fintype.card E) := by
    simpa only [g] using hug
  refine ⟨u,by change u ≤ WeightedBinsGeneric.bound i +
    WeightedGraphQJoined.bound g s (Fintype.card E) + 1; omega,
    v,F,Q,?_,?_,?_,?_,?_,hscale,?_⟩
  · simpa only [program,initialControl,B] using hr
  · change (bank graphSlots B Q)
      (graphSlots (WeightedGraphQJoined.writer 56)) = _
    rw [bank_at]
    exact hq
  · change (bank graphSlots B Q)
      (graphSlots (WeightedGraphQJoined.writer 54)) = _
    rw [bank_at]
    exact hq54
  · change (bank graphSlots B Q)
      (graphSlots (WeightedGraphQJoined.writer 17)) = _
    rw [bank_at]
    simpa only [W',Function.update_of_ne (by decide : (17 : Fin 64) ≠ 28)]
      using hq17
  · change (bank graphSlots B Q)
      (graphSlots (WeightedGraphQJoined.writer 57)) = _
    rw [bank_at]
    simpa only [W',Function.update_of_ne (by decide : (57 : Fin 64) ≠ 28)]
      using hq57
  · intro p
    have hout : ¬ ∃ j : WeightedGraphQJoined.Stack,
        graphSlots j = (.inl p : Stack) := by
      rintro ⟨j,h⟩; cases h
    change (bank graphSlots B Q) (.inl p) = F p
    rw [bank_outside _ _ _ _ hout]
    change bank binSlots (base g W)
      (WeightedBinsGeneric.finalBank W F i) (binSlots (.inl p)) = F p
    rw [bank_at]
    simp [WeightedBinsGeneric.finalBank,
      WeightedBinsGeneric.afterBins,WeightedBinsGeneric.writer]
    change bank WeightedBinsGeneric.paramSlots
      (WeightedBinsGeneric.foreignBank W) F
      (WeightedBinsGeneric.paramSlots p) = F p
    rw [bank_at]

#print axioms source_run

end
end EthInapproximability.CurrentPaper.WeightedBinsGraphQ
