import CurrentAdditive.QuarticSelectedBitsInjective
import CurrentAdditive.QuarticPairUniform

/-! The uniform-cap pair front returns the literal selected input bank. -/

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open Paper2 Paper2.CurrentAdditive.QuarticConstructor
open Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition

noncomputable section
set_option maxHeartbeats 8000000

theorem pair_front_selected_uniform27
    (Dsrc : DinurReduction) (Bsrc : BOTReduction (booleanOccurrence Dsrc))
    (Φ : ValidFormula) (fullTape : List Bool)
    (t : (select27 (t10_vertices_pos Dsrc Bsrc Φ)
      (CanonicalEdgeTape.graphEdge (t10Graph Dsrc Bsrc Φ)
        (t10Graph_valid Dsrc Bsrc Φ))
      Bsrc.degreeBound (sourceGap Dsrc Bsrc) (kOf Φ.val.variables)).Tape)
    (hchecks : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin (t10Graph Dsrc Bsrc Φ).vertices)
      (Edges := Fin (t10Graph Dsrc Bsrc Φ).edges.length)
      (Nat.clog 2 (t10Graph Dsrc Bsrc Φ).vertices)
      Bsrc.degreeBound (sourceGap Dsrc Bsrc))
    (hfit : (select27 (t10_vertices_pos Dsrc Bsrc Φ)
      (CanonicalEdgeTape.graphEdge (t10Graph Dsrc Bsrc Φ)
        (t10Graph_valid Dsrc Bsrc Φ))
      Bsrc.degreeBound (sourceGap Dsrc Bsrc) (kOf Φ.val.variables)).inputBits ≤
      Paper2.AEth3.cutLen Φ.val)
    (hbits : (select27 (t10_vertices_pos Dsrc Bsrc Φ)
      (CanonicalEdgeTape.graphEdge (t10Graph Dsrc Bsrc Φ)
        (t10Graph_valid Dsrc Bsrc Φ))
      Bsrc.degreeBound (sourceGap Dsrc Bsrc) (kOf Φ.val.variables)).tapeBits t =
      fullTape.take (select27 (t10_vertices_pos Dsrc Bsrc Φ)
        (CanonicalEdgeTape.graphEdge (t10Graph Dsrc Bsrc Φ)
          (t10Graph_valid Dsrc Bsrc Φ))
        Bsrc.degreeBound (sourceGap Dsrc Bsrc) (kOf Φ.val.variables)).inputBits)
    (Z : ℕ) (hZ : 1 ≤ Z)
    (hP : (BitMachineBankCodec.encode
      (FullFront.X0 (t10Graph Dsrc Bsrc Φ) (kOf Φ.val.variables)
        (fullTape.take (Paper2.AEth3.cutLen Φ.val)))).length ≤ Z)
    (hRaw : Paper2.CurrentAdditive.QuarticNumericFront.Raw27.clock
      (t10Graph Dsrc Bsrc Φ) Bsrc.degreeBound (sourceGap Dsrc Bsrc)
      (kOf Φ.val.variables)
      (fullTape.take (Paper2.AEth3.cutLen Φ.val)) ≤ Z) :
    let g := t10Graph Dsrc Bsrc Φ
    let hg := t10Graph_valid Dsrc Bsrc Φ
    let hn := t10_vertices_pos Dsrc Bsrc Φ
    let k := kOf Φ.val.variables
    let raw := fullTape.take (Paper2.AEth3.cutLen Φ.val)
    let Y := QuarticDispatchSpec.inputBank27 Bsrc.degreeBound
      (sourceGap Dsrc Bsrc) g hg hn k t
    (Paper2.CurrentAdditive.QuarticPairFront.pairFrontMachine Dsrc Bsrc).OutputsWithin
      (EncodedComplexity.pair (EncodedCNF.encode Φ.val) raw)
      (EncodedComplexity.pair (EncodedCNF.encode Φ.val)
        (BitMachineBankCodec.encode Y))
      (Paper2.CurrentAdditive.QuarticPairFront.pairFrontClock Dsrc Bsrc Φ raw
        (BitMachineBankCodec.encode Y)
        (Paper2.CurrentAdditive.QuarticOuterMachine.cutClock
          (FullFront.X0 g k raw) Y
          (Paper2.CurrentAdditive.QuarticOuterUniform.localCap g
            Bsrc.degreeBound (sourceGap Dsrc Bsrc) k raw Z))) := by
  intro g hg hn k raw Y
  have hfront := Paper2.CurrentAdditive.QuarticPairUniform.pair_front_outputs_uniform
    Dsrc Bsrc Φ raw Z hZ hP hRaw
  have hpacket := cutPacket_eq_inputBank27 g hg hn Bsrc.degreeBound
    (sourceGap Dsrc Bsrc) k hchecks Φ.val fullTape t hfit hbits
  have hpacketRaw : QuarticCutOutputCopies.outPacket g k
      (raw.take (QuarticCutCount.count27 g.vertices g.edges.length
        (Nat.clog 2 g.vertices) Bsrc.degreeBound (sourceGap Dsrc Bsrc) k)) =
      Y := by simpa only [raw, Y] using hpacket
  dsimp only at hfront
  rw [hpacketRaw] at hfront
  simpa only [g, hg, hn, k, raw, Y] using hfront

#print axioms pair_front_selected_uniform27

end
end Paper2.CurrentAdditive.QuarticClassEndpoint
