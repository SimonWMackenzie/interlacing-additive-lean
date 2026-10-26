import CurrentAdditive.QuarticSourceDeciderError

/-! The fixed v27 square printer applied to the actual encoded source graph. -/

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2 Paper2.Unit4Shell.T10Finite
open Paper2.CurrentAdditive.QuarticConstructor
open Paper2.CurrentAdditive.QuarticMachineWrapper

theorem source_square_machine27
    (Dsrc : DinurReduction) (Bsrc : BOTReduction (booleanOccurrence Dsrc))
    (hA : H_A3_27 Bsrc.degreeBound (sourceGap Dsrc Bsrc)) :
    ∃ (M : BitMachine.Machine) (C E : ℕ),
      ∀ (Φ : ValidFormula) (hN : 36 ≤ Φ.val.variables),
        let g := t10Graph Dsrc Bsrc Φ
        let hg := t10Graph_valid Dsrc Bsrc Φ
        let hn := t10_vertices_pos Dsrc Bsrc Φ
        let edge := CanonicalEdgeTape.graphEdge g hg
        let k := Paper2.Unit4Shell.Asymptotics.kOf Φ.val.variables
        ∀ t : (select27 hn edge Bsrc.degreeBound (sourceGap Dsrc Bsrc) k).Tape,
          M.OutputsWithin
            (BitMachineBankCodec.encode
              (QuarticDispatchSpec.inputBank27 Bsrc.degreeBound (sourceGap Dsrc Bsrc)
                g hg hn k t))
            (EncodedCommunication.encodeInstance
              (Paper2.ASquare.squareInstance
                (selectedInstance27 hn edge Bsrc.degreeBound (sourceGap Dsrc Bsrc) k t)))
            (C * (g.vertices + 2) ^ (E * (k + 1)) +
              2 * (outputBits27 hn edge Bsrc.degreeBound (sourceGap Dsrc Bsrc) k t).length + 2 +
              Paper2.ASquare.Post.squareCP *
                ((outputBits27 hn edge Bsrc.degreeBound (sourceGap Dsrc Bsrc) k t).length + 1) ^
                  Paper2.ASquare.Post.squareEP) := by
  obtain ⟨M, C, E, hM⟩ := H_square_27_of_H_A3 _ _ hA
  refine ⟨M, C, E, ?_⟩
  intro Φ hN g hg hn edge k t
  obtain ⟨_, _, hinc, hdeg, _, _, _⟩ := t10_source Dsrc Bsrc Φ
  have hk : 1 ≤ k :=
    Paper2.Unit4Shell.AsymptoticsExplicit.kOf_pos _ hN
  exact hM g hg hn k ⟨hk, hinc, hdeg⟩ t

#print axioms source_square_machine27

end Paper2.CurrentAdditive.QuarticClassEndpoint
