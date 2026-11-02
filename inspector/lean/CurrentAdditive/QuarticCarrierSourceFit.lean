import CurrentAdditive.QuarticPhysicalCarrier

/-! Eventual source bounds discharge the R20 carrier's prefix and block fit. -/

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open Paper2 Paper2.AEth4 Paper2.CurrentAdditive.QuarticConstructor
open Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition

noncomputable section
set_option maxHeartbeats 8000000

theorem routed_carrier_fit27
    (Dsrc : DinurReduction) (Bsrc : BOTReduction (booleanOccurrence Dsrc))
    (C : SelectedTape.Algorithm) (cs N₁ : ℕ)
    (hlarge : physicalCut27 Dsrc Bsrc C cs ≤ N₁)
    (hN₁ : 1 ≤ N₁) :
    ∀ x : List Bool,
      ∀ a : (sourceSelector27 Dsrc Bsrc (cs + 2) N₁ hN₁ x).Tape,
      (sourceSelector27 Dsrc Bsrc (cs + 2) N₁ hN₁ x).inputBits ≤
        tapeCA (phiLen N₁) (8 + C.cR) x.length ∧
      Paper2.AEth3.cutLen (routedV (cs + 2) N₁ hN₁ x).val +
        C.tapeLength (sourceHeader27 Dsrc Bsrc (cs + 2) N₁ hN₁ x a) ≤
          tapeCA (phiLen N₁) (8 + C.cR) x.length := by
  intro x a
  let Φ := routedV (cs + 2) N₁ hN₁ x
  have hvars : N₁ ≤ Φ.val.variables :=
    routed4_variables (cs + 2) N₁ x
  have hK : 2 ≤ (cs + 2) * N₁ := by
    have h2 : 2 ≤ cs + 2 := by omega
    exact le_trans h2 (Nat.le_mul_of_pos_right _ hN₁)
  have hsp : Φ.val.clauses.length ≤ (cs + 2) * Φ.val.variables :=
    routed4_sparse (cs + 2) N₁ hK x
  have hinputLarge : Classical.choose
      (source_inputBits_fit27 Dsrc Bsrc (cs + 2)) ≤ Φ.val.variables := by
    have : Classical.choose (source_inputBits_fit27 Dsrc Bsrc (cs + 2)) ≤
        physicalCut27 Dsrc Bsrc C cs :=
      (le_max_left _ _).trans (le_max_right _ _)
    omega
  have hclassLarge : Classical.choose
      (source_classifier_fit27 Dsrc Bsrc (cs + 2) C) ≤ Φ.val.variables := by
    have : Classical.choose (source_classifier_fit27 Dsrc Bsrc (cs + 2) C) ≤
        physicalCut27 Dsrc Bsrc C cs :=
      (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    omega
  let g := t10Graph Dsrc Bsrc Φ
  let hg := t10Graph_valid Dsrc Bsrc Φ
  let hn := t10_vertices_pos Dsrc Bsrc Φ
  let edge := CanonicalEdgeTape.graphEdge g hg
  let k := kOf Φ.val.variables
  have hinput := (Classical.choose_spec
    (source_inputBits_fit27 Dsrc Bsrc (cs + 2))) Φ hsp hinputLarge
  have hclass := (Classical.choose_spec
    (source_classifier_fit27 Dsrc Bsrc (cs + 2) C)) Φ hsp hclassLarge a
  have hblocks := blocks_fit (cs + 2) hN₁ C.cR x
  change Paper2.AEth3.cutLen Φ.val +
    C.cR * Paper2.AEth.expLen Φ.val.variables ≤
      tapeCA (phiLen N₁) (8 + C.cR) x.length at hblocks
  have hI : (sourceSelector27 Dsrc Bsrc (cs + 2) N₁ hN₁ x).inputBits ≤
      tapeCA (phiLen N₁) (8 + C.cR) x.length := by
    change (select27 hn edge Bsrc.degreeBound
      (sourceGap Dsrc Bsrc) k).inputBits ≤ _
    have hinput' : (select27 hn edge Bsrc.degreeBound
        (sourceGap Dsrc Bsrc) k).inputBits ≤
        Paper2.AEth.expLen Φ.val.variables := by
      simpa only [g, hg, hn, edge, k] using hinput.2
    have hge := Paper2.AEth3.cutLen_ge Φ.val
    omega
  have hC : C.tapeLength
      (sourceHeader27 Dsrc Bsrc (cs + 2) N₁ hN₁ x a) ≤
      C.cR * Paper2.AEth.expLen Φ.val.variables := by
    simpa only [sourceHeader27, Φ, g, hg, hn, edge, k] using hclass
  refine ⟨hI, ?_⟩
  change Paper2.AEth3.cutLen Φ.val +
    C.tapeLength (sourceHeader27 Dsrc Bsrc (cs + 2) N₁ hN₁ x a) ≤
      tapeCA (phiLen N₁) (8 + C.cR) x.length
  omega

#print axioms routed_carrier_fit27

end
end Paper2.CurrentAdditive.QuarticClassEndpoint
