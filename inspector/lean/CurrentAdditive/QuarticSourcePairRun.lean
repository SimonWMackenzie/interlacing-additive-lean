import CurrentAdditive.QuarticSourcePairFront
import CurrentAdditive.QuarticSourcePairSubexp

/-! An actual bounded run of the fixed public-bank pair front on sparse source formulas. -/

namespace Paper2.CurrentAdditive.QuarticSourcePairRun

open Paper2 Paper2.CurrentAdditive.QuarticConstructor
open Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2.CurrentAdditive.QuarticSourcePairFront
open Paper2.CurrentAdditive.QuarticSourcePairSubexp

noncomputable section
set_option maxHeartbeats 8000000

theorem source_pair_front_outputs_subexp
    (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))
    (cs : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C N₀ : ℕ, ∀ Φ : ValidFormula,
      Φ.val.clauses.length ≤ cs * Φ.val.variables →
      N₀ ≤ Φ.val.variables →
      (hchecks : CurrentAdditive.QuarticSchedule.Checks27
        (V := Fin (t10Graph D B Φ).vertices)
        (Edges := Fin (t10Graph D B Φ).edges.length)
        (Nat.clog 2 (t10Graph D B Φ).vertices)
        B.degreeBound (sourceGap D B)) →
      let g := t10Graph D B Φ
      let hg := t10Graph_valid D B Φ
      let hn := t10_vertices_pos D B Φ
      let k := kOf Φ.val.variables
      ∀ fullTape : List Bool,
      ∀ t : (select27 hn (CanonicalEdgeTape.graphEdge g hg)
        B.degreeBound (sourceGap D B) k).Tape,
      (hfit : (select27 hn (CanonicalEdgeTape.graphEdge g hg)
        B.degreeBound (sourceGap D B) k).inputBits ≤
        Paper2.AEth3.cutLen Φ.val) →
      (hbits : (select27 hn (CanonicalEdgeTape.graphEdge g hg)
        B.degreeBound (sourceGap D B) k).tapeBits t =
        fullTape.take (select27 hn (CanonicalEdgeTape.graphEdge g hg)
          B.degreeBound (sourceGap D B) k).inputBits) →
      let raw := fullTape.take (Paper2.AEth3.cutLen Φ.val)
      let Y := QuarticDispatchSpec.inputBank27 B.degreeBound
        (sourceGap D B) g hg hn k t
      (QuarticPairFront.pairFrontMachine D B).OutputsWithin
        (EncodedComplexity.pair (EncodedCNF.encode Φ.val) raw)
        (EncodedComplexity.pair (EncodedCNF.encode Φ.val)
          (BitMachineBankCodec.encode Y))
        (C * ⌈(2 : ℝ) ^ (ε * Φ.val.variables)⌉₊) := by
  obtain ⟨C, N₀, hclock⟩ := source_pair_front_subexp D B cs ε hε
  refine ⟨C, N₀, ?_⟩
  intro Φ hsparse hlarge hchecks g hg hn k fullTape t hfit hbits raw Y
  have hrun := pair_front_selected_at_inputCap D B Φ fullTape t
    hchecks hfit hbits
  have hbound := hclock Φ hsparse hlarge hchecks fullTape t
  apply BitMachine.outputsWithin_mono _ hrun
  simpa only [g, hg, hn, k, raw, Y] using hbound

#print axioms source_pair_front_outputs_subexp

end
end Paper2.CurrentAdditive.QuarticSourcePairRun
