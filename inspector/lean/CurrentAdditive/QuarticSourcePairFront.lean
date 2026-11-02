import CurrentAdditive.QuarticSourceCutInst
import CurrentAdditive.QuarticPairUniformBank
import CurrentAdditive.QuarticUniformInputCap

/-! Instantiate the already checked uniform physical pair front at its literal cap. -/

namespace Paper2.CurrentAdditive.QuarticSourcePairFront

open Paper2 Paper2.CurrentAdditive.QuarticConstructor
open Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2.CurrentAdditive.QuarticClassEndpoint

noncomputable section
set_option maxHeartbeats 8000000

theorem pair_front_selected_at_inputCap
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
        Bsrc.degreeBound (sourceGap Dsrc Bsrc) (kOf Φ.val.variables)).inputBits) :
    let g := t10Graph Dsrc Bsrc Φ
    let hg := t10Graph_valid Dsrc Bsrc Φ
    let hn := t10_vertices_pos Dsrc Bsrc Φ
    let k := kOf Φ.val.variables
    let raw := fullTape.take (Paper2.AEth3.cutLen Φ.val)
    let Y := QuarticDispatchSpec.inputBank27 Bsrc.degreeBound
      (sourceGap Dsrc Bsrc) g hg hn k t
    let Z := QuarticUniformInputCap.inputCap g Bsrc.degreeBound
      (sourceGap Dsrc Bsrc) k raw.length
    (Paper2.CurrentAdditive.QuarticPairFront.pairFrontMachine Dsrc Bsrc).OutputsWithin
      (EncodedComplexity.pair (EncodedCNF.encode Φ.val) raw)
      (EncodedComplexity.pair (EncodedCNF.encode Φ.val)
        (BitMachineBankCodec.encode Y))
      (Paper2.CurrentAdditive.QuarticPairFront.pairFrontClock Dsrc Bsrc Φ raw
        (BitMachineBankCodec.encode Y)
        (QuarticOuterMachine.cutClock (FullFront.X0 g k raw) Y
          (QuarticOuterUniform.localCap g Bsrc.degreeBound
            (sourceGap Dsrc Bsrc) k raw Z))) := by
  intro g hg hn k raw Y Z
  have hP := QuarticUniformInputCap.encoded_input_le g Bsrc.degreeBound
    (sourceGap Dsrc Bsrc) k raw.length raw (le_refl _)
  have hmass : g.edges.length ≤ Bsrc.degreeBound * g.vertices := by
    obtain ⟨_, _, _, hdeg, _, _, _⟩ := t10_source Dsrc Bsrc Φ
    have htwice := Paper2.A3Assembly.Size.twice_edges_le g hg hn
      Bsrc.degreeBound hdeg
    omega
  have hRaw := QuarticUniformInputCap.raw_clock_le g hg Bsrc.degreeBound
    (sourceGap Dsrc Bsrc) (source_gap_pos Dsrc Bsrc)
    Bsrc.degreeBound_pos hn (t10_source Dsrc Bsrc Φ).1 hmass
    k raw.length raw (le_refl _)
  have h := pair_front_selected_uniform27 Dsrc Bsrc Φ fullTape t hchecks
    hfit hbits Z (QuarticUniformInputCap.inputCap_pos g
      Bsrc.degreeBound (sourceGap Dsrc Bsrc) k raw.length) hP hRaw
  simpa only [g, hg, hn, k, raw, Y, Z] using h

#print axioms pair_front_selected_at_inputCap

end
end Paper2.CurrentAdditive.QuarticSourcePairFront
