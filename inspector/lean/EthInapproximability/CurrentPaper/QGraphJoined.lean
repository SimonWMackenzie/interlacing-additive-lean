import EthInapproximability.CurrentPaper.QArithmeticJoined
import EthInapproximability.CurrentPaper.BitMachineStackRun

/-! Same-graph guarded decoding followed by the fixed q₂ arithmetic
controller. No edge-count or final q word is present in the initial bank. -/

namespace EthInapproximability.CurrentPaper.QGraphJoined

open Turing BitMachineEncoding BitMachineStackEmbedding
noncomputable section

abbrev Stack := QProduct.Stack
abbrev WriterStack := Fin 64

def parserProgram := fun l => stackStmt QProduct.parserWriterSlots
  (GraphCountBridge.program l)

def emptyForeign : Stack → List Bool := fun _ => []

def startBank (g : EncodedGraph.Graph)
    (W : WriterStack → List Bool) : Stack → List Bool :=
  bank QProduct.parserWriterSlots emptyForeign
    (GraphCountBridge.start g W).stk

def decodedBank (g : EncodedGraph.Graph)
    (W : WriterStack → List Bool) : Stack → List Bool :=
  bank QProduct.parserWriterSlots emptyForeign
    (GraphCountBridge.finish g W).stk

theorem parser_run (g : EncodedGraph.Graph) (hg : g.Valid)
    (W : WriterStack → List Bool) :
    ∃ t ≤ 101*((EncodedGraph.encode g).length+1)^3,
      ((advance parserProgram)^[t])
        (⟨some (.inr .gate),
          (GraphCountBridge.start g W).var,startBank g W⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            SourceNormalizationMachineDecode.Label
            SourceNormalizationMachineDecode.Control) =
        ⟨none,(GraphCountBridge.finish g W).var,decodedBank g W⟩ := by
  obtain ⟨t,ht,hr⟩ := GraphCountBridge.parser_run g hg W
  have he := BitMachineStackRun.run QProduct.parserWriterSlots
    emptyForeign GraphCountBridge.program
    (GraphCountBridge.start g W) t
  rw [hr] at he
  refine ⟨t,ht,?_⟩
  simpa [parserProgram,startBank,decodedBank,
    GraphCountBridge.start,SourceNormalizationMachineDecode.guardedStart]
    using he

theorem decoded_at (g : EncodedGraph.Graph)
    (W : WriterStack → List Bool) (j : GraphCountBridge.Stack) :
    decodedBank g W (.inl j) = (GraphCountBridge.finish g W).stk j := by
  exact bank_at QProduct.parserWriterSlots _ _ j

theorem decoded_temp (g : EncodedGraph.Graph)
    (W : WriterStack → List Bool) (j : Fin 10) :
    decodedBank g W (QProduct.temp j) = [] := by
  have hj : ¬ ∃ k : GraphCountBridge.Stack,
      QProduct.parserWriterSlots k = QProduct.temp j := by
    rintro ⟨k,h⟩; cases h
  exact bank_outside QProduct.parserWriterSlots _ _ _ hj

theorem decoded_log (g : EncodedGraph.Graph)
    (W : WriterStack → List Bool) (k : QLog.Local) :
    decodedBank g W (QLog.logSlots k) = [] := by
  have hk : ¬ ∃ j : GraphCountBridge.Stack,
      QProduct.parserWriterSlots j = QLog.logSlots k := by
    rintro ⟨j,h⟩; cases h
  exact bank_outside QProduct.parserWriterSlots _ _ _ hk

theorem same_graph_q_run {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (G : ParameterizedNP.GuardedSourceGraph.EndpointGraph V E)
    (W : WriterStack → List Bool) (s : ℕ)
    (hs : W 28 = List.replicate s true)
    (hq : W 56 = []) :
    ∃ t ≤ 101*((EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length+1)^3 +
      QArithmeticJoined.cost s (Fintype.card E) + 1,
      ∃ F : Stack → List Bool,
        ((advance (BitMachineRawSequence.program
          parserProgram QArithmeticJoined.program
          (BitMachineRawSequence.leftLabel QProductJoined.start)
          (GraphCountBridge.start (EncodedETHSource.serializeGraph G) W).var
          QArithmeticJoined.initial))^[t])
          (⟨some (BitMachineRawSequence.leftLabel
              (Sum.inr SourceNormalizationMachineDecode.Admin.gate)),
            ((GraphCountBridge.start (EncodedETHSource.serializeGraph G) W).var,
              QArithmeticJoined.initial),
            startBank (EncodedETHSource.serializeGraph G) W⟩ :
              TM2.Cfg (fun _ : Stack => Bool) _ _) =
          ⟨none,((GraphCountBridge.start
            (EncodedETHSource.serializeGraph G) W).var,
              QArithmeticJoined.initial),F⟩ ∧
        F QProduct.q =
          List.replicate (ParameterizedNP.GuardedSourceSlab.q2 G s) true ∧
        (∀ j : WriterStack, j ≠ 56 →
          F (.inl (.inr j)) = W j) ∧
        F QProduct.edge = List.replicate (Fintype.card E) true := by
  let g := EncodedETHSource.serializeGraph G
  let D := decodedBank g W
  obtain ⟨tp,htp,hparse⟩ := parser_run g
    (EncodedETHSource.serializeGraph_valid G) W
  have hedge : D QProduct.edge = List.replicate (Fintype.card E) true := by
    dsimp only [D]
    rw [show QProduct.edge = (.inl (.inl (.inr (1 : Fin 6))) : Stack) from rfl,
      decoded_at]
    simpa [g] using GraphCountBridge.finish_edge_count g W
  have hsD : D QProduct.s = List.replicate s true := by
    dsimp only [D]
    rw [show QProduct.s = (.inl (.inr (28 : Fin 64)) : Stack) from rfl,
      decoded_at,GraphCountBridge.finish_writer]
    exact hs
  have hqD : D QProduct.q = [] := by
    dsimp only [D]
    rw [show QProduct.q = (.inl (.inr (56 : Fin 64)) : Stack) from rfl,
      decoded_at,GraphCountBridge.finish_writer]
    exact hq
  obtain ⟨ta,hta,F,harith,hout,hframe⟩ :=
    QArithmeticJoined.run D s (Fintype.card E) hsD hedge
      (decoded_temp g W 0) (decoded_temp g W 1)
      (decoded_temp g W 2) (decoded_temp g W 3)
      (decoded_temp g W 4) (decoded_temp g W 5)
      (decoded_temp g W 6) (decoded_temp g W 7)
      (decoded_temp g W 8) (decoded_log g W) hqD
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    parserProgram QArithmeticJoined.program
    (Sum.inr SourceNormalizationMachineDecode.Admin.gate)
    (BitMachineRawSequence.leftLabel QProductJoined.start)
    (GraphCountBridge.start g W).var
    (GraphCountBridge.finish g W).var
    QArithmeticJoined.initial QArithmeticJoined.initial
    (startBank g W) D F tp ta hparse harith
  refine ⟨t,by dsimp [g] at *; omega,F,?_,?_,?_,?_⟩
  · simpa only [g,D] using hr
  · simpa [ParameterizedNP.GuardedSourceSlab.q2] using hout
  · intro j hj
    have hD := GraphCountBridge.finish_writer g W j
    exact (hframe (.inr j) (by
      intro hh; exact hj (Sum.inr_injective hh))).trans
      ((decoded_at g W (.inr j)).trans hD)
  · have hj : (.inl (.inr (1 : Fin 6)) : GraphCountBridge.Stack) ≠
        (.inr (56 : Fin 64)) := by decide
    exact (hframe _ hj).trans hedge

#print axioms same_graph_q_run

end
end EthInapproximability.CurrentPaper.QGraphJoined
