import EthInapproximability.CurrentPaper.QCleanup
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-! The full same-graph q₂ producer with a charged private-bank cleanup.
The literal controller is independent of the graph and all numeric inputs;
only the initial Boolean stacks carry those data. -/

namespace EthInapproximability.CurrentPaper.QFinal

open Turing BitMachineEncoding
noncomputable section

abbrev Stack := QProduct.Stack
abbrev WriterStack := Fin 64

def qProgram (g : EncodedGraph.Graph) (W : WriterStack → List Bool) :=
  BitMachineRawSequence.program
    QGraphJoined.parserProgram QArithmeticJoined.program
    (BitMachineRawSequence.leftLabel QProductJoined.start)
    (GraphCountBridge.start g W).var QArithmeticJoined.initial

theorem qProgram_fixed (g h : EncodedGraph.Graph)
    (W X : WriterStack → List Bool) : qProgram g W = qProgram h X := rfl

def qInitial (g : EncodedGraph.Graph) (W : WriterStack → List Bool) :=
  ((GraphCountBridge.start g W).var,QArithmeticJoined.initial)

def program (g : EncodedGraph.Graph) (W : WriterStack → List Bool) :=
  BitMachineRawSequence.program (qProgram g W) QCleanup.program
    (.inl (0 : Fin (QCleanup.count+1)))
    (qInitial g W) ((),none)

theorem program_fixed (g h : EncodedGraph.Graph)
    (W X : WriterStack → List Bool) : program g W = program h X := rfl

theorem same_graph_q_clean_run {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (G : ParameterizedNP.GuardedSourceGraph.EndpointGraph V E)
    (W : WriterStack → List Bool) (s : ℕ)
    (hs : W 28 = List.replicate s true)
    (hq : W 56 = []) :
    let g := EncodedETHSource.serializeGraph G
    ∃ (t : ℕ) (F C : Stack → List Bool),
      t ≤ 101*((EncodedGraph.encode g).length+1)^3 +
        QArithmeticJoined.cost s (Fintype.card E) + 1 +
        QCleanup.cost C + 1 ∧
      F = QCleanup.cleared C ∧
        ((advance (program g W))^[t])
          (⟨some (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (Sum.inr SourceNormalizationMachineDecode.Admin.gate))),
            (qInitial g W,((),none)),QGraphJoined.startBank g W⟩ :
              TM2.Cfg (fun _ : Stack => Bool) _ _) =
          ⟨none,(qInitial g W,((),none)),F⟩ ∧
        F QProduct.q =
          List.replicate (ParameterizedNP.GuardedSourceSlab.q2 G s) true ∧
        (∀ j : WriterStack, j ≠ 56 → F (.inl (.inr j)) = W j) ∧
        F QProduct.edge = List.replicate (Fintype.card E) true ∧
        (∀ j : QCleanup.ClearIndex, F (QCleanup.embed j) = []) := by
  let g := EncodedETHSource.serializeGraph G
  obtain ⟨tq,htq,F,hqrun,hout,hwriter,hedge⟩ :=
    QGraphJoined.same_graph_q_run G W s hs hq
  have hqrun' : ((advance (qProgram g W))^[tq])
        (⟨some (BitMachineRawSequence.leftLabel
            (Sum.inr SourceNormalizationMachineDecode.Admin.gate)),
          qInitial g W,QGraphJoined.startBank g W⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,qInitial g W,F⟩ := by
    simpa only [qProgram,qInitial,g] using hqrun
  have hc := QCleanup.run F
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    (qProgram g W) QCleanup.program
    (BitMachineRawSequence.leftLabel
      (Sum.inr SourceNormalizationMachineDecode.Admin.gate))
    (.inl (0 : Fin (QCleanup.count+1)))
    (qInitial g W) (qInitial g W)
    ((),none) ((),none)
    (QGraphJoined.startBank g W) F (QCleanup.cleared F)
    tq (QCleanup.cost F) hqrun' hc
  refine ⟨t,QCleanup.cleared F,F,?_,rfl,?_,?_,?_,?_,?_⟩
  · dsimp only [g]; omega
  · simpa only [program,qInitial] using hr
  · exact (QCleanup.cleared_parser_writer F (.inr 56)).trans hout
  · intro j hj
    exact (QCleanup.cleared_parser_writer F (.inr j)).trans (hwriter j hj)
  · exact (QCleanup.cleared_parser_writer F (.inl (.inr 1))).trans hedge
  · exact QCleanup.cleared_private F

#print axioms same_graph_q_clean_run

end
end EthInapproximability.CurrentPaper.QFinal
