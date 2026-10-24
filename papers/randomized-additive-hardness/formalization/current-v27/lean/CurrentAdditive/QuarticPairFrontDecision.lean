import CurrentAdditive.QuarticFrontBankIdentity
import CurrentAdditive.QuarticPairFront
import CurrentAdditive.QuarticAnyPhysicalOutput

/-! The fixed pair front feeds the fixed formula decision machine at the
literal selected v27 bank.  The selected tape and square-printer run remain
visible parameters until the source and numeric bounds are supplied. -/

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open Paper2 Paper2.CurrentAdditive.QuarticConstructor
open Paper2.Unit4Shell.T10Finite
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

theorem pair_front_decision27
    (Dsrc : DinurReduction) (Bsrc : BOTReduction (booleanOccurrence Dsrc))
    (printer : BitMachine.Machine) (C : Paper2.SelectedTape.Algorithm)
    (K N₁ : ℕ) (hN₁ : 1 ≤ N₁) (x tape : List Bool)
    (t : (select27 (t10_vertices_pos Dsrc Bsrc
      (Paper2.AEth4.routedV K N₁ hN₁ x))
      (CanonicalEdgeTape.graphEdge
        (t10Graph Dsrc Bsrc (Paper2.AEth4.routedV K N₁ hN₁ x))
        (t10Graph_valid Dsrc Bsrc (Paper2.AEth4.routedV K N₁ hN₁ x)))
      Bsrc.degreeBound (sourceGap Dsrc Bsrc)
      (Paper2.Unit4Shell.Asymptotics.kOf
        (Paper2.AEth4.routedV K N₁ hN₁ x).val.variables)).Tape)
    (hchecks : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin (t10Graph Dsrc Bsrc
        (Paper2.AEth4.routedV K N₁ hN₁ x)).vertices)
      (Edges := Fin (t10Graph Dsrc Bsrc
        (Paper2.AEth4.routedV K N₁ hN₁ x)).edges.length)
      (Nat.clog 2 (t10Graph Dsrc Bsrc
        (Paper2.AEth4.routedV K N₁ hN₁ x)).vertices)
      Bsrc.degreeBound (sourceGap Dsrc Bsrc))
    (hfit : (select27 (t10_vertices_pos Dsrc Bsrc
      (Paper2.AEth4.routedV K N₁ hN₁ x))
      (CanonicalEdgeTape.graphEdge
        (t10Graph Dsrc Bsrc (Paper2.AEth4.routedV K N₁ hN₁ x))
        (t10Graph_valid Dsrc Bsrc (Paper2.AEth4.routedV K N₁ hN₁ x)))
      Bsrc.degreeBound (sourceGap Dsrc Bsrc)
      (Paper2.Unit4Shell.Asymptotics.kOf
        (Paper2.AEth4.routedV K N₁ hN₁ x).val.variables)).inputBits ≤
      Paper2.AEth3.cutLen (Paper2.AEth4.routedV K N₁ hN₁ x).val)
    (hbits : (select27 (t10_vertices_pos Dsrc Bsrc
      (Paper2.AEth4.routedV K N₁ hN₁ x))
      (CanonicalEdgeTape.graphEdge
        (t10Graph Dsrc Bsrc (Paper2.AEth4.routedV K N₁ hN₁ x))
        (t10Graph_valid Dsrc Bsrc (Paper2.AEth4.routedV K N₁ hN₁ x)))
      Bsrc.degreeBound (sourceGap Dsrc Bsrc)
      (Paper2.Unit4Shell.Asymptotics.kOf
        (Paper2.AEth4.routedV K N₁ hN₁ x).val.variables)).tapeBits t =
      tape.take (select27 (t10_vertices_pos Dsrc Bsrc
        (Paper2.AEth4.routedV K N₁ hN₁ x))
        (CanonicalEdgeTape.graphEdge
          (t10Graph Dsrc Bsrc (Paper2.AEth4.routedV K N₁ hN₁ x))
          (t10Graph_valid Dsrc Bsrc (Paper2.AEth4.routedV K N₁ hN₁ x)))
        Bsrc.degreeBound (sourceGap Dsrc Bsrc)
        (Paper2.Unit4Shell.Asymptotics.kOf
          (Paper2.AEth4.routedV K N₁ hN₁ x).val.variables)).inputBits)
    (Tprint : ℕ)
    (hprint : printer.OutputsWithin
      (BitMachineBankCodec.encode
        (QuarticDispatchSpec.inputBank27 Bsrc.degreeBound
          (sourceGap Dsrc Bsrc)
          (t10Graph Dsrc Bsrc (Paper2.AEth4.routedV K N₁ hN₁ x))
          (t10Graph_valid Dsrc Bsrc (Paper2.AEth4.routedV K N₁ hN₁ x))
          (t10_vertices_pos Dsrc Bsrc (Paper2.AEth4.routedV K N₁ hN₁ x))
          (Paper2.Unit4Shell.Asymptotics.kOf
            (Paper2.AEth4.routedV K N₁ hN₁ x).val.variables) t))
      (EncodedCommunication.encodeInstance (Paper2.ASquare.squareInstance
        (selectedInstance27
          (t10_vertices_pos Dsrc Bsrc (Paper2.AEth4.routedV K N₁ hN₁ x))
          (CanonicalEdgeTape.graphEdge
            (t10Graph Dsrc Bsrc (Paper2.AEth4.routedV K N₁ hN₁ x))
            (t10Graph_valid Dsrc Bsrc (Paper2.AEth4.routedV K N₁ hN₁ x)))
          Bsrc.degreeBound (sourceGap Dsrc Bsrc)
          (Paper2.Unit4Shell.Asymptotics.kOf
            (Paper2.AEth4.routedV K N₁ hN₁ x).val.variables) t))) Tprint)
    (hk : 1 ≤ Paper2.Unit4Shell.Asymptotics.kOf
      (Paper2.AEth4.routedV K N₁ hN₁ x).val.variables)
    (hclassifier : C.tapeLength
      (Paper2.HeaderWordRun.headeredWord
        (Paper2.Unit4Shell.Asymptotics.kOf
          (Paper2.AEth4.routedV K N₁ hN₁ x).val.variables)
        (Paper2.ASquare.squareInstance (selectedInstance27
          (t10_vertices_pos Dsrc Bsrc (Paper2.AEth4.routedV K N₁ hN₁ x))
          (CanonicalEdgeTape.graphEdge
            (t10Graph Dsrc Bsrc (Paper2.AEth4.routedV K N₁ hN₁ x))
            (t10Graph_valid Dsrc Bsrc (Paper2.AEth4.routedV K N₁ hN₁ x)))
          Bsrc.degreeBound (sourceGap Dsrc Bsrc)
          (Paper2.Unit4Shell.Asymptotics.kOf
            (Paper2.AEth4.routedV K N₁ hN₁ x).val.variables) t))) ≤
      ((tape.take (2 ^ C.cR * Paper2.AEth3.cutLen
        (Paper2.AEth4.routedV K N₁ hN₁ x).val)).drop
          (Paper2.AEth3.cutLen (Paper2.AEth4.routedV K N₁ hN₁ x).val)).length) :
    ∃ Tcut : ℕ,
      let Φ := (Paper2.AEth4.routedV K N₁ hN₁ x).val
      let raw := tape.take (Paper2.AEth3.cutLen Φ)
      let block := (tape.take (2 ^ C.cR * Paper2.AEth3.cutLen Φ)).drop
        (Paper2.AEth3.cutLen Φ)
      let bank := BitMachineBankCodec.encode
        (QuarticDispatchSpec.inputBank27 Bsrc.degreeBound
          (sourceGap Dsrc Bsrc)
          (t10Graph Dsrc Bsrc (Paper2.AEth4.routedV K N₁ hN₁ x))
          (t10Graph_valid Dsrc Bsrc (Paper2.AEth4.routedV K N₁ hN₁ x))
          (t10_vertices_pos Dsrc Bsrc (Paper2.AEth4.routedV K N₁ hN₁ x))
          (Paper2.Unit4Shell.Asymptotics.kOf Φ.variables) t)
      let i := selectedInstance27
        (t10_vertices_pos Dsrc Bsrc (Paper2.AEth4.routedV K N₁ hN₁ x))
        (CanonicalEdgeTape.graphEdge
          (t10Graph Dsrc Bsrc (Paper2.AEth4.routedV K N₁ hN₁ x))
          (t10Graph_valid Dsrc Bsrc (Paper2.AEth4.routedV K N₁ hN₁ x)))
        Bsrc.degreeBound (sourceGap Dsrc Bsrc)
        (Paper2.Unit4Shell.Asymptotics.kOf Φ.variables) t
      let w := Paper2.HeaderWordRun.headeredWord
        (Paper2.Unit4Shell.Asymptotics.kOf Φ.variables)
        (Paper2.ASquare.squareInstance i)
      (Paper2.CurrentAdditive.QuarticPairFront.pairFrontMachine Dsrc Bsrc).OutputsWithin
        (EncodedComplexity.pair (EncodedCNF.encode Φ) raw)
        (EncodedComplexity.pair (EncodedCNF.encode Φ) bank) Tcut ∧
      (sourceDecision27 (tailFromPrefix27
        (Paper2.CurrentAdditive.QuarticPairFront.pairFrontMachine Dsrc Bsrc)
        printer) C K N₁).OutputsWithin
        (EncodedComplexity.pair x tape)
        (C.output w (block.take (C.tapeLength w)))
        (sourceDecisionClock27 C x (Paper2.AEth3.fOut Φ)
          raw block w (Paper2.AEth5.twoCutTime K N₁ C.cR x)
          (sourceCoreClock27 Φ raw
            (Tcut + 2 * (EncodedComplexity.pair
              (EncodedCNF.encode Φ) bank).length + 2 +
              headerClock27 Φ bank i
                ((EncodedCNF.encode Φ).length + 2 +
                  2 * bank.length + 2 + Tprint))) block.length) := by
  let Φv := Paper2.AEth4.routedV K N₁ hN₁ x
  let Φ := Φv.val
  let g := t10Graph Dsrc Bsrc Φv
  let hg := t10Graph_valid Dsrc Bsrc Φv
  let hn := t10_vertices_pos Dsrc Bsrc Φv
  let k := Paper2.Unit4Shell.Asymptotics.kOf Φ.variables
  let raw := tape.take (Paper2.AEth3.cutLen Φ)
  let bank := BitMachineBankCodec.encode
    (QuarticDispatchSpec.inputBank27 Bsrc.degreeBound (sourceGap Dsrc Bsrc)
      g hg hn k t)
  let i := selectedInstance27 hn (CanonicalEdgeTape.graphEdge g hg)
    Bsrc.degreeBound (sourceGap Dsrc Bsrc) k t
  obtain ⟨Bwork, H, hfront⟩ :=
    Paper2.CurrentAdditive.QuarticPairFront.pair_front_outputs Dsrc Bsrc Φv raw
  have hpacket := cutPacket_eq_inputBank27 g hg hn
    Bsrc.degreeBound (sourceGap Dsrc Bsrc) k hchecks Φ tape t hfit hbits
  rw [hpacket] at hfront
  let Tcut := Paper2.CurrentAdditive.QuarticPairFront.pairFrontClock Dsrc Bsrc
    Φv raw bank (QuarticOuterMachine.cutClock (FullFront.X0 g k raw)
      (QuarticDispatchSpec.inputBank27 Bsrc.degreeBound
        (sourceGap Dsrc Bsrc) g hg hn k t)
      (QuarticOuterMachine.localBudget g Bsrc.degreeBound
        (sourceGap Dsrc Bsrc) k raw Bwork H))
  refine ⟨Tcut, ?_, ?_⟩
  · simpa only [Tcut, Φv, Φ, g, hg, hn, k, raw, bank] using hfront
  · have hdec := sourceDecision_any_from_bank27
      (Paper2.CurrentAdditive.QuarticPairFront.pairFrontMachine Dsrc Bsrc)
      printer C K N₁ hN₁ x tape bank i Tcut Tprint
      (((tape.take (2 ^ C.cR * Paper2.AEth3.cutLen Φ)).drop
        (Paper2.AEth3.cutLen Φ)).length)
    simpa only [Φv, Φ, g, hg, hn, k, raw, bank, i, Tcut] using
      (hdec hk (by simpa only [Tcut, Φv, Φ, g, hg, hn, k, raw, bank] using hfront)
        (by simpa only [Φv, Φ, g, hg, hn, k, bank, i] using hprint)
        (by rfl) hclassifier)

#print axioms pair_front_decision27

end
end Paper2.CurrentAdditive.QuarticClassEndpoint
