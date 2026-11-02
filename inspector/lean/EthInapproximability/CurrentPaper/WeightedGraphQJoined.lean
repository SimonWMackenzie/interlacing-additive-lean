import EthInapproximability.CurrentPaper.GraphVertexPreludeJoin
import EthInapproximability.CurrentPaper.QArithmeticJoined
import EthInapproximability.CurrentPaper.BitMachineStackRun

/-! One parsing pass on the literal guarded source graph: its retained parser
bank is used first for graph-item/order preparation, then directly for the
same-graph q₂ arithmetic. The q phase does not reparse or receive an edge
count as an input. -/

namespace EthInapproximability.CurrentPaper.WeightedGraphQJoined

open Turing BitMachineEncoding BitMachineStackEmbedding
noncomputable section

abbrev Stack := QProduct.Stack
def parserWriterSlots := QProduct.parserWriterSlots
def writer (k : Fin 64) : Stack := .inl (.inr k)
def lift (S : GraphVertexPreludeJoin.Stack → List Bool) :
    Stack → List Bool :=
  bank parserWriterSlots (fun _ => []) S
def initialBank (g : EncodedGraph.Graph)
    (W : Fin 64 → List Bool) : Stack → List Bool :=
  lift (GraphVertexPreludeJoin.parserStart g W).stk
def afterPrelude (g : EncodedGraph.Graph)
    (W : Fin 64 → List Bool) (s : ℕ) : Stack → List Bool :=
  lift (GraphVertexPreludeJoin.finalBank g W s)
def preludeProgram := fun l => stackStmt parserWriterSlots
  (GraphVertexPreludeJoin.fullProgram l)
def program := BitMachineRawSequence.program preludeProgram
  QArithmeticJoined.program
  (BitMachineRawSequence.leftLabel QProductJoined.start)
  ((GraphVertexPreludeJoin.parserInitial,none),
    (MatrixWeightedGraphItemCountsPrelude.initial,
      MatrixWeightedOrderPreparation.initial))
  QArithmeticJoined.initial
def initialControl :=
  (((GraphVertexPreludeJoin.parserInitial,(none : Option Bool)),
    (MatrixWeightedGraphItemCountsPrelude.initial,
      MatrixWeightedOrderPreparation.initial)),QArithmeticJoined.initial)
def bound (g : EncodedGraph.Graph) (s e : ℕ) : ℕ :=
  101 * ((EncodedGraph.encode g).length + 1)^3 +
  (2 * g.vertices + 2) +
  MatrixWeightedGraphItemCountsPrelude.cost g.vertices s +
  MatrixWeightedOrderPreparation.prepCost g.vertices (s-3) (4*s) + 3 +
  QArithmeticJoined.cost s e + 1

private theorem prelude_writer_at (g : EncodedGraph.Graph)
    (W : Fin 64 → List Bool) (s : ℕ) (j : Fin 64) :
    (afterPrelude g W s) (writer j) =
      (MatrixWeightedOrderPreparation.readyBank
        (MatrixWeightedGraphItemCountsPrelude.finalBank
          (GraphVertexPreludeJoin.writerAfter g W) g.vertices s)
        g.vertices (s-3) (4*s)) j := by
  change bank parserWriterSlots (fun _ => [])
    (GraphVertexPreludeJoin.finalBank g W s)
    (parserWriterSlots (.inr j)) = _
  rw [bank_at]
  change bank GraphVertexPreludeJoin.writerSlots
    (GraphVertexPreludeJoin.copied g W).stk _
    (GraphVertexPreludeJoin.writerSlots j) = _
  rw [bank_at]

private theorem prelude_writer_other (g : EncodedGraph.Graph)
    (W : Fin 64 → List Bool) (s : ℕ) (k : Fin 64)
    (h7 : k ≠ 7) (h8 : k ≠ 8) (h9 : k ≠ 9)
    (h10 : k ≠ 10) (h11 : k ≠ 11) (h12 : k ≠ 12)
    (h13 : k ≠ 13) (h14 : k ≠ 14)
    (h15 : k ≠ 15) (h18 : k ≠ 18)
    (h54 : k ≠ 54) (h55 : k ≠ 55) (h60 : k ≠ 60) :
    (afterPrelude g W s) (writer k) = W k := by
  rw [prelude_writer_at]
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

private theorem prelude_q_blank (g : EncodedGraph.Graph)
    (W : Fin 64 → List Bool) (s : ℕ) (h56 : W 56 = []) :
    (afterPrelude g W s) QProduct.q = [] := by
  rw [show QProduct.q = writer 56 from rfl,prelude_writer_at]
  have hclear : ∀ k : Fin 8,
      MatrixWeightedOrderPreparation.scratchSlots k ≠ (56 : Fin 64) := by
    intro k
    fin_cases k <;> decide
  rw [MatrixWeightedOrderPreparation.readyBank,
    BitMachineClearBank.cleared_foreign _ _ _ hclear]
  have hslots : ¬ ∃ k : Fin 9,
      MatrixWeightedOrderPreparation.slots k = (56 : Fin 64) := by
    rintro ⟨k,h⟩
    fin_cases k <;>
      simp [MatrixWeightedOrderPreparation.slots] at h
  rw [MatrixWeightedOrderPreparation.producedBank,
    bank_outside _ _ _ _ hslots]
  rw [MatrixWeightedGraphItemCountsPrelude.final_foreign]
  · exact (GraphVertexPreludeJoin.writerAfter_other g W 56
      (by decide) (by decide)).trans h56
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

private theorem prelude_s (g : EncodedGraph.Graph)
    (W : Fin 64 → List Bool) (s : ℕ)
    (hs : W 28 = List.replicate s true) :
    (afterPrelude g W s) QProduct.s = List.replicate s true := by
  rw [show QProduct.s = writer 28 from rfl]
  change bank parserWriterSlots (fun _ => [])
    (GraphVertexPreludeJoin.finalBank g W s)
    (parserWriterSlots (.inr 28)) = _
  rw [bank_at]
  exact (GraphVertexPreludeJoin.final_scale g W s).trans hs

private theorem prelude_54_blank (g : EncodedGraph.Graph)
    (W : Fin 64 → List Bool) (s : ℕ) :
    (afterPrelude g W s) (writer 54) = [] := by
  change bank parserWriterSlots (fun _ => [])
    (GraphVertexPreludeJoin.finalBank g W s)
    (parserWriterSlots (.inr 54)) = _
  rw [bank_at]
  exact GraphVertexPreludeJoin.final_vertex_source_empty g W s

private theorem prelude_edge (g : EncodedGraph.Graph)
    (W : Fin 64 → List Bool) (s : ℕ) :
    (afterPrelude g W s) QProduct.edge =
      List.replicate g.edges.length true := by
  change bank parserWriterSlots (fun _ => [])
    (GraphVertexPreludeJoin.finalBank g W s)
    (parserWriterSlots (.inl (.inr (1 : Fin 6)))) = _
  rw [bank_at]
  have hwriter : ¬ ∃ k : Fin 64,
      GraphVertexPreludeJoin.writerSlots k =
        (.inl (.inr (1 : Fin 6)) : GraphVertexPreludeJoin.Stack) := by
    rintro ⟨k,h⟩; cases h
  rw [GraphVertexPreludeJoin.finalBank,
    bank_outside _ _ _ _ hwriter]
  have hcopy : ¬ ∃ k : Fin 3,
      GraphVertexPreludeJoin.copySlots k =
        (.inl (.inr (1 : Fin 6)) : GraphVertexPreludeJoin.Stack) := by
    rintro ⟨k,h⟩
    fin_cases k <;> cases h
  change bank GraphVertexPreludeJoin.copySlots
    (GraphVertexPreludeJoin.parserFinish g W).stk
    (BitMachineCopy.cfg none none
      (List.replicate g.vertices true)
      (List.replicate g.vertices true) []).stk
    (.inl (.inr (1 : Fin 6))) = _
  rw [bank_outside _ _ _ _ hcopy]
  simpa [GraphVertexPreludeJoin.parserFinish,
    GraphCountBridge.finish] using GraphCountBridge.finish_edge_count g W

private theorem prelude_temp (g : EncodedGraph.Graph)
    (W : Fin 64 → List Bool) (s : ℕ) (j : Fin 10) :
    (afterPrelude g W s) (QProduct.temp j) = [] := by
  have hout : ¬ ∃ k : GraphVertexPreludeJoin.Stack,
      parserWriterSlots k = QProduct.temp j := by
    rintro ⟨k,h⟩; cases h
  change bank parserWriterSlots (fun _ => [])
    (GraphVertexPreludeJoin.finalBank g W s) (QProduct.temp j) = []
  rw [bank_outside _ _ _ _ hout]

private theorem prelude_log (g : EncodedGraph.Graph)
    (W : Fin 64 → List Bool) (s : ℕ) (j : QLog.Local) :
    (afterPrelude g W s) (QLog.logSlots j) = [] := by
  have hout : ¬ ∃ k : GraphVertexPreludeJoin.Stack,
      parserWriterSlots k = QLog.logSlots j := by
    rintro ⟨k,h⟩; cases h
  change bank parserWriterSlots (fun _ => [])
    (GraphVertexPreludeJoin.finalBank g W s) (QLog.logSlots j) = []
  rw [bank_outside _ _ _ _ hout]

/-- The already-checked parser/order controller lifted into the q arithmetic
bank; all q-private cells remain blank. -/
theorem prelude_run (g : EncodedGraph.Graph) (hg : g.Valid)
    (W : Fin 64 → List Bool) (s : ℕ)
    (hs : W 28 = List.replicate s true)
    (h7 : W 7 = []) (h8 : W 8 = []) (h9 : W 9 = [])
    (h10 : W 10 = []) (h11 : W 11 = []) (h12 : W 12 = [])
    (h13 : W 13 = []) (h14 : W 14 = [])
    (h15 : W 15 = []) (h18 : W 18 = [])
    (h54 : W 54 = []) (h55 : W 55 = []) (h56 : W 56 = [])
    (h57 : W 57 = []) (h58 : W 58 = []) (h60 : W 60 = []) :
    ∃ u ≤ 101 * ((EncodedGraph.encode g).length + 1)^3 +
        (2 * g.vertices + 2) +
        MatrixWeightedGraphItemCountsPrelude.cost g.vertices s +
        MatrixWeightedOrderPreparation.prepCost g.vertices (s-3) (4*s) + 3,
      ((advance preludeProgram)^[u])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel (.inr .gate))),
          ((GraphVertexPreludeJoin.parserInitial,none),
            (MatrixWeightedGraphItemCountsPrelude.initial,
              MatrixWeightedOrderPreparation.initial)),initialBank g W⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,((GraphVertexPreludeJoin.parserInitial,none),
            (MatrixWeightedGraphItemCountsPrelude.initial,
              MatrixWeightedOrderPreparation.initial)),
          afterPrelude g W s⟩ := by
  obtain ⟨u,hu,hr⟩ := GraphVertexPreludeJoin.full_run g hg W s hs
    h7 h8 h9 h10 h11 h12 h13 h14 h15 h18
    h54 h55 h56 h57 h58 h60
  have he := BitMachineStackRun.run parserWriterSlots
    (fun _ => []) GraphVertexPreludeJoin.fullProgram
    (⟨some (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (.inr .gate))),
      ((GraphVertexPreludeJoin.parserInitial,none),
        (MatrixWeightedGraphItemCountsPrelude.initial,
          MatrixWeightedOrderPreparation.initial)),
      (GraphVertexPreludeJoin.parserStart g W).stk⟩ :
      TM2.Cfg (fun _ : GraphVertexPreludeJoin.Stack => Bool) _ _) u
  rw [hr] at he
  refine ⟨u,hu,?_⟩
  simpa only [preludeProgram,initialBank,afterPrelude,lift,stackCfg]
    using he

/-- From the actual graph code and writer bin count, the one fixed program
prepares graph items/order and then computes q₂ using that same parser bank.
No separate edge-count input or second graph parser appears. -/
theorem run (g : EncodedGraph.Graph) (hg : g.Valid)
    (W : Fin 64 → List Bool) (s : ℕ)
    (hs : W 28 = List.replicate s true)
    (h7 : W 7 = []) (h8 : W 8 = []) (h9 : W 9 = [])
    (h10 : W 10 = []) (h11 : W 11 = []) (h12 : W 12 = [])
    (h13 : W 13 = []) (h14 : W 14 = [])
    (h15 : W 15 = []) (h18 : W 18 = [])
    (h54 : W 54 = []) (h55 : W 55 = []) (h56 : W 56 = [])
    (h57 : W 57 = []) (h58 : W 58 = []) (h60 : W 60 = []) :
    ∃ u ≤ bound g s g.edges.length,
      ∃ F : Stack → List Bool,
        ((advance program)^[u])
          (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel (.inr .gate)))),
            initialControl,initialBank g W⟩ :
            TM2.Cfg (fun _ : Stack => Bool) _ _) =
          ⟨none,initialControl,F⟩ ∧
        F QProduct.q =
          List.replicate (2^Nat.clog 2 (12*s*g.edges.length)) true ∧
        F (writer 54) = [] ∧
        F (writer 17) = W 17 ∧
        F (writer 57) = W 57 ∧
        (∀ k : Fin 64, k ≠ 56 →
          F (writer k) = (afterPrelude g W s) (writer k)) := by
  obtain ⟨up,hup,hpre⟩ := prelude_run g hg W s hs
    h7 h8 h9 h10 h11 h12 h13 h14 h15 h18
    h54 h55 h56 h57 h58 h60
  let D := afterPrelude g W s
  obtain ⟨uq,huq,F,hqrun,hq,hframe⟩ :=
    QArithmeticJoined.run D s g.edges.length
      (prelude_s g W s hs) (prelude_edge g W s)
      (prelude_temp g W s 0) (prelude_temp g W s 1)
      (prelude_temp g W s 2) (prelude_temp g W s 3)
      (prelude_temp g W s 4) (prelude_temp g W s 5)
      (prelude_temp g W s 6) (prelude_temp g W s 7)
      (prelude_temp g W s 8) (prelude_log g W s)
      (prelude_q_blank g W s h56)
  obtain ⟨u,hu,hr⟩ := BitMachineRawSequence.runs
    preludeProgram QArithmeticJoined.program
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (.inr .gate)))
    (BitMachineRawSequence.leftLabel QProductJoined.start)
    ((GraphVertexPreludeJoin.parserInitial,none),
      (MatrixWeightedGraphItemCountsPrelude.initial,
        MatrixWeightedOrderPreparation.initial))
    ((GraphVertexPreludeJoin.parserInitial,none),
      (MatrixWeightedGraphItemCountsPrelude.initial,
        MatrixWeightedOrderPreparation.initial))
    QArithmeticJoined.initial QArithmeticJoined.initial
    (initialBank g W) D F up uq hpre hqrun
  refine ⟨u,by dsimp [bound]; omega,F,?_,hq,?_,?_,?_,?_⟩
  · simpa only [program,initialControl] using hr
  · exact (hframe (.inr 54) (by decide)).trans
      (prelude_54_blank g W s)
  · exact (hframe (.inr 17) (by decide)).trans
      (prelude_writer_other g W s 17
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide))
  · exact (hframe (.inr 57) (by decide)).trans
      (prelude_writer_other g W s 57
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide))
  · intro k hk
    exact hframe (.inr k) (by
      intro h; exact hk (Sum.inr_injective h))

/-- Specialization to the exact graph used by the ETH source. -/
theorem source_run {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (G : ParameterizedNP.GuardedSourceGraph.EndpointGraph V E)
    (W : Fin 64 → List Bool) (s : ℕ)
    (hs : W 28 = List.replicate s true)
    (h7 : W 7 = []) (h8 : W 8 = []) (h9 : W 9 = [])
    (h10 : W 10 = []) (h11 : W 11 = []) (h12 : W 12 = [])
    (h13 : W 13 = []) (h14 : W 14 = [])
    (h15 : W 15 = []) (h18 : W 18 = [])
    (h54 : W 54 = []) (h55 : W 55 = []) (h56 : W 56 = [])
    (h57 : W 57 = []) (h58 : W 58 = []) (h60 : W 60 = []) :
    ∃ u ≤ bound (EncodedETHSource.serializeGraph G) s (Fintype.card E),
      ∃ F : Stack → List Bool,
        ((advance program)^[u])
          (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel (.inr .gate)))),
            initialControl,
            initialBank (EncodedETHSource.serializeGraph G) W⟩ :
            TM2.Cfg (fun _ : Stack => Bool) _ _) =
          ⟨none,initialControl,F⟩ ∧
        F QProduct.q = List.replicate
          (ParameterizedNP.GuardedSourceSlab.q2 G s) true ∧
        F (writer 54) = [] ∧
        F (writer 17) = W 17 ∧
        F (writer 57) = W 57 ∧
        (∀ k : Fin 64, k ≠ 56 →
          F (writer k) =
            (afterPrelude (EncodedETHSource.serializeGraph G) W s)
              (writer k)) := by
  obtain ⟨u,hu,F,hr,hq,h54final,h17,h57,hframe⟩ := run
    (EncodedETHSource.serializeGraph G)
    (EncodedETHSource.serializeGraph_valid G) W s hs
    h7 h8 h9 h10 h11 h12 h13 h14 h15 h18
    h54 h55 h56 h57 h58 h60
  refine ⟨u,?_,F,hr,?_,h54final,h17,h57,hframe⟩
  · simpa only [EncodedETHSource.serializeGraph_edges] using hu
  · simpa [ParameterizedNP.GuardedSourceSlab.q2,
      EncodedETHSource.serializeGraph_edges] using hq

#print axioms prelude_q_blank
#print axioms prelude_edge
#print axioms run
#print axioms source_run

end
end EthInapproximability.CurrentPaper.WeightedGraphQJoined
