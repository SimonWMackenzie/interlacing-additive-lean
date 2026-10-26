import EthInapproximability.CurrentPaper.SourceNormalizationMachineDecode
import EthInapproximability.CurrentPaper.EncodedETHSource
import EthInapproximability.CurrentPaper.BitMachineStackRun
import Mathlib.Data.Fin.VecNotation

/-! A physical edge-count producer from the exact graph passed to the
CurrentPaper ETH iteration. The parser consumes its guarded graph code; the
weighted writer is a disjoint, unchanged bank. No edge count is an input. -/

namespace EthInapproximability.CurrentPaper.GraphCountBridge

open Turing BitMachineEncoding BitMachineStackEmbedding

abbrev ParserStack := SourceNormalizationMachineDecode.Stack
abbrev WriterStack := Fin 64
abbrev Stack := ParserStack ⊕ WriterStack

def parserSlots : ParserStack ↪ Stack :=
  ⟨Sum.inl, by intro a b h; exact Sum.inl_injective h⟩

def program := fun l => stackStmt parserSlots
  (SourceNormalizationMachineDecode.program l)

noncomputable def start (g : EncodedGraph.Graph)
    (W : WriterStack → List Bool) :
    TM2.Cfg (fun _ : Stack => Bool)
      SourceNormalizationMachineDecode.Label
      SourceNormalizationMachineDecode.Control :=
  stackCfg parserSlots (Sum.elim (fun _ => []) W)
    (SourceNormalizationMachineDecode.guardedStart
      (true :: EncodedGraph.encode g))

noncomputable def finish (g : EncodedGraph.Graph)
    (W : WriterStack → List Bool) :=
  stackCfg parserSlots (Sum.elim (fun _ => []) W)
    (SourceNormalizationMachineDecode.cfg none
      (SourceNormalizationMachineDecode.doneControl true) {}
      (List.replicate g.vertices true)
      (List.replicate g.edges.length true) [] []
      (SourceNormalizationMachineDecode.endpointStream g) [])

theorem parser_run (g : EncodedGraph.Graph) (hg : g.Valid)
    (W : WriterStack → List Bool) :
    ∃ t ≤ 101 * ((EncodedGraph.encode g).length + 1)^3,
      ((advance program)^[t]) (start g W) = finish g W := by
  obtain ⟨t,ht,hr⟩ :=
    SourceNormalizationMachineDecode.guarded_valid_run g hg
  refine ⟨t,ht,?_⟩
  have he := BitMachineStackRun.run parserSlots
    (Sum.elim (fun _ => []) W)
    SourceNormalizationMachineDecode.program
    (SourceNormalizationMachineDecode.guardedStart
      (true :: EncodedGraph.encode g)) t
  unfold SourceNormalizationMachineDecode.run at hr
  rw [hr] at he
  simpa only [program, start, finish] using he

theorem finish_edge_count (g : EncodedGraph.Graph)
    (W : WriterStack → List Bool) :
    (finish g W).stk (.inl (.inr (1 : Fin 6))) =
      List.replicate g.edges.length true := by
  change (finish g W).stk (parserSlots (.inr (1 : Fin 6))) = _
  unfold finish
  dsimp only [stackCfg]
  rw [bank_at]
  rfl

theorem finish_writer (g : EncodedGraph.Graph)
    (W : WriterStack → List Bool) (j : WriterStack) :
    (finish g W).stk (.inr j) = W j := by
  have hout : ¬ ∃ k : ParserStack, parserSlots k = (.inr j : Stack) := by
    rintro ⟨k,h⟩; cases h
  exact bank_outside parserSlots _ _ _ hout

theorem same_graph_run {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (G : ParameterizedNP.GuardedSourceGraph.EndpointGraph V E)
    (W : WriterStack → List Bool) :
    ∃ t ≤ 101 * ((EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length + 1)^3,
      ((advance program)^[t])
        (start (EncodedETHSource.serializeGraph G) W) =
        finish (EncodedETHSource.serializeGraph G) W ∧
      (finish (EncodedETHSource.serializeGraph G) W).stk
        (.inl (.inr (1 : Fin 6))) = List.replicate (Fintype.card E) true ∧
      ∀ j, (finish (EncodedETHSource.serializeGraph G) W).stk (.inr j) = W j := by
  obtain ⟨t,ht,hr⟩ := parser_run _
    (EncodedETHSource.serializeGraph_valid G) W
  refine ⟨t,ht,hr,?_,?_⟩
  · simpa only [EncodedETHSource.serializeGraph_edges] using
      finish_edge_count (EncodedETHSource.serializeGraph G) W
  · exact finish_writer _ W

#print axioms parser_run
#print axioms same_graph_run

end EthInapproximability.CurrentPaper.GraphCountBridge
