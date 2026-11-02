import CurrentAdditive.QuarticFormulaError
import CurrentAdditive.QuarticMachineFromNumeric
import Paper2.ASquarePost

/-!
# Physical square postprocessing of the literal v27 selected word

This is the first physical composition needed by the square classifier. The
machine before the postprocessor is the v27 machine, not the preserved v12
selector. The only remaining premise of this layer is its explicit numeric
front construction.
-/

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open EthInapproximability.CurrentPaper
open Paper2 Paper2.CurrentAdditive.QuarticConstructor
open Paper2.CurrentAdditive.QuarticMachineWrapper

theorem H_square_27_of_H_A3 (Δ : ℕ) (γ : ℚ)
    (hA : H_A3_27 Δ γ) :
    ∃ (MA : BitMachine.Machine) (CA EA : ℕ),
      ∀ (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices) (k : ℕ),
        QuarticDispatchSpec.Hyp Δ g hg k →
        ∀ t : (select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape,
          MA.OutputsWithin
            (BitMachineBankCodec.encode
              (QuarticDispatchSpec.inputBank27 Δ γ g hg hn k t))
            (EncodedCommunication.encodeInstance
              (Paper2.ASquare.squareInstance
                (selectedInstance27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k t)))
            (CA * (g.vertices + 2) ^ (EA * (k + 1)) +
              2 * (outputBits27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k t).length + 2 +
              Paper2.ASquare.Post.squareCP *
                ((outputBits27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k t).length + 1) ^
                  Paper2.ASquare.Post.squareEP) := by
  obtain ⟨M, CA, EA, hM⟩ := hA
  refine ⟨BitMachineComposition.composition M Paper2.ASquare.Post.squareMachine,
    CA, EA, ?_⟩
  intro g hg hn k hdispatch t
  let edge := CanonicalEdgeTape.graphEdge g hg
  let i := selectedInstance27 hn edge Δ γ k t
  have hp := select27_dimensions_pos hn edge Δ γ k
  have hvalid : i.Valid := Paper2.EncodedSelectedOutput.instanceOf_valid _ _ hp.1 hp.2
  have hfirst := hM g hg hn k hdispatch t
  have hsecond := Paper2.ASquare.Post.squarePost i hvalid
  exact BitMachineComposition.composition_outputsWithin M _ hfirst hsecond

#print axioms H_square_27_of_H_A3

end Paper2.CurrentAdditive.QuarticClassEndpoint
