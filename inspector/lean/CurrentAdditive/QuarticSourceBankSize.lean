import CurrentAdditive.QuarticSourceScheduled

/-! The actual v27 source bank is uniformly small across selected tapes. -/

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open Paper2 Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics
open Paper2.CurrentAdditive.QuarticConstructor
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition

theorem source_inputBank_size27
    (Dsrc : DinurReduction) (Bsrc : BOTReduction (booleanOccurrence Dsrc))
    (Φ : ValidFormula) (hN : 36 ≤ Φ.val.variables) :
    let g := t10Graph Dsrc Bsrc Φ
    let hg := t10Graph_valid Dsrc Bsrc Φ
    let hn := t10_vertices_pos Dsrc Bsrc Φ
    let edge := CanonicalEdgeTape.graphEdge g hg
    let k := kOf Φ.val.variables
    ∀ t : (select27 hn edge Bsrc.degreeBound (sourceGap Dsrc Bsrc) k).Tape,
      (BitMachineBankCodec.encode
        (QuarticDispatchSpec.inputBank27 Bsrc.degreeBound
          (sourceGap Dsrc Bsrc) g hg hn k t)).length ≤
        (4 * Bsrc.degreeBound + 9) *
          (g.vertices + 2) ^ (160 * (k + 1)) := by
  intro g hg hn edge k t
  obtain ⟨_, _, hinc, hdeg, _, _, _⟩ := t10_source Dsrc Bsrc Φ
  have hk : 1 ≤ k :=
    Paper2.Unit4Shell.AsymptoticsExplicit.kOf_pos _ hN
  exact Paper2.CurrentAdditive.QuarticDispatchSize.inputSize27
    Bsrc.degreeBound (sourceGap Dsrc Bsrc) g hg hn k
    ⟨hk, hinc, hdeg⟩ t

#print axioms source_inputBank_size27

end Paper2.CurrentAdditive.QuarticClassEndpoint
