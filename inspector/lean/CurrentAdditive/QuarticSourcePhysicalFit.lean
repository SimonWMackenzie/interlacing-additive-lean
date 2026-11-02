import CurrentAdditive.QuarticPairFrontDecision
import CurrentAdditive.QuarticHeaderFit
import CurrentAdditive.QuarticSourceScheduled

/-! Uniform source-side conditions for the physical v27 decision run. -/

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open Paper2 Paper2.CurrentAdditive.QuarticConstructor
open Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

theorem source_second_block_fit27
    (K N₁ : ℕ) (hN₁ : 1 ≤ N₁) (C : Paper2.SelectedTape.Algorithm)
    (x tape : List Bool)
    (hfull : Paper2.AEth4.tapeCA (Paper2.AEth4.phiLen N₁)
      (8 + C.cR) x.length ≤ tape.length) :
    let Φ := Paper2.AEth4.routed4 K N₁ x
    let block := (tape.take (2 ^ C.cR * Paper2.AEth3.cutLen Φ)).drop
      (Paper2.AEth3.cutLen Φ)
    Paper2.AEth3.cutLen Φ ≤ tape.length ∧
    C.cR * Paper2.AEth.expLen Φ.variables ≤ block.length ∧
    block.length ≤ 2 ^ C.cR * Paper2.AEth3.cutLen Φ := by
  intro Φ block
  have htwo : 2 ^ C.cR * Paper2.AEth3.cutLen Φ ≤ tape.length := by
    have hfit := Paper2.AEth5.twoCut_fit K N₁ C.cR hN₁ x
    have hmono : Paper2.AEth4.tapeCA (Paper2.AEth4.phiLen N₁)
        (7 + C.cR) x.length ≤
        Paper2.AEth4.tapeCA (Paper2.AEth4.phiLen N₁)
          (8 + C.cR) x.length := by
      unfold Paper2.AEth4.tapeCA
      apply Nat.pow_le_pow_right (by omega)
      omega
    exact hfit.trans (hmono.trans hfull)
  have hcut : Paper2.AEth3.cutLen Φ ≤ tape.length := by
    have hp : 1 ≤ 2 ^ C.cR := by
      have hp' : 0 < 2 ^ C.cR := by positivity
      omega
    have hm := Nat.le_mul_of_pos_left (Paper2.AEth3.cutLen Φ) hp
    omega
  have hblock : block.length =
      2 ^ C.cR * Paper2.AEth3.cutLen Φ - Paper2.AEth3.cutLen Φ := by
    simp only [block, List.length_drop, List.length_take]
    rw [Nat.min_eq_left htwo]
  have hsecond := Paper2.AEth5.second_block_fit C.cR Φ
  constructor
  · exact hcut
  constructor
  · rw [hblock]
    omega
  · rw [hblock]
    omega

def physicalCut27
    (Dsrc : DinurReduction) (Bsrc : BOTReduction (booleanOccurrence Dsrc))
    (C : Paper2.SelectedTape.Algorithm) (cs : ℕ) : ℕ :=
  max 36 (max
    (Classical.choose (source_inputBits_fit27 Dsrc Bsrc (cs + 2)))
    (max (Classical.choose
      (source_classifier_fit27 Dsrc Bsrc (cs + 2) C))
      (Bsrc.degreeBound * CurrentAdditive.QuarticSchedule.threshold27
        Bsrc.degreeBound (sourceGap Dsrc Bsrc))))

theorem routed_source_physical_fit27
    (Dsrc : DinurReduction) (Bsrc : BOTReduction (booleanOccurrence Dsrc))
    (C : Paper2.SelectedTape.Algorithm) (cs N₁ : ℕ)
    (hlarge : physicalCut27 Dsrc Bsrc C cs ≤ N₁)
    (x tape : List Bool)
    (hfull : Paper2.AEth4.tapeCA (Paper2.AEth4.phiLen N₁)
      (8 + C.cR) x.length ≤ tape.length) :
    let hN₁ : 1 ≤ N₁ := by
      have : 36 ≤ N₁ := (le_max_left _ _).trans hlarge
      omega
    let Φ := Paper2.AEth4.routedV (cs + 2) N₁ hN₁ x
    let g := t10Graph Dsrc Bsrc Φ
    let hg := t10Graph_valid Dsrc Bsrc Φ
    let hn := t10_vertices_pos Dsrc Bsrc Φ
    let edge := CanonicalEdgeTape.graphEdge g hg
    let k := kOf Φ.val.variables
    let block := (tape.take (2 ^ C.cR * Paper2.AEth3.cutLen Φ.val)).drop
      (Paper2.AEth3.cutLen Φ.val)
    ∃ t : (select27 hn edge Bsrc.degreeBound (sourceGap Dsrc Bsrc) k).Tape,
      CurrentAdditive.QuarticSchedule.Checks27
        (V := Fin g.vertices) (Edges := Fin g.edges.length)
        (Nat.clog 2 g.vertices) Bsrc.degreeBound (sourceGap Dsrc Bsrc) ∧
      (select27 hn edge Bsrc.degreeBound (sourceGap Dsrc Bsrc) k).inputBits ≤
        Paper2.AEth3.cutLen Φ.val ∧
      (select27 hn edge Bsrc.degreeBound (sourceGap Dsrc Bsrc) k).tapeBits t =
        tape.take
          (select27 hn edge Bsrc.degreeBound (sourceGap Dsrc Bsrc) k).inputBits ∧
      1 ≤ k ∧
      C.tapeLength (Paper2.HeaderWordRun.headeredWord k
        (Paper2.ASquare.squareInstance
          (selectedInstance27 hn edge Bsrc.degreeBound (sourceGap Dsrc Bsrc)
            k t))) ≤ block.length := by
  intro hN₁ Φ g hg hn edge k block
  have hvars : N₁ ≤ Φ.val.variables :=
    Paper2.AEth4.routed4_variables (cs + 2) N₁ x
  have hK : 2 ≤ (cs + 2) * N₁ := by
    have h2 : 2 ≤ cs + 2 := by omega
    exact le_trans h2 (Nat.le_mul_of_pos_right _ hN₁)
  have hsp : Φ.val.clauses.length ≤ (cs + 2) * Φ.val.variables :=
    Paper2.AEth4.routed4_sparse (cs + 2) N₁ hK x
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
  have hschedLarge : Bsrc.degreeBound *
      CurrentAdditive.QuarticSchedule.threshold27
        Bsrc.degreeBound (sourceGap Dsrc Bsrc) ≤ Φ.val.variables := by
    have : Bsrc.degreeBound * CurrentAdditive.QuarticSchedule.threshold27
        Bsrc.degreeBound (sourceGap Dsrc Bsrc) ≤
        physicalCut27 Dsrc Bsrc C cs :=
      (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    omega
  have hinput := (Classical.choose_spec
    (source_inputBits_fit27 Dsrc Bsrc (cs + 2))) Φ hsp hinputLarge
  have hcut : (select27 hn edge Bsrc.degreeBound
      (sourceGap Dsrc Bsrc) k).inputBits ≤ Paper2.AEth3.cutLen Φ.val :=
    hinput.2.trans (le_trans (by omega :
      Paper2.AEth.expLen Φ.val.variables ≤
        2 * Paper2.AEth.expLen Φ.val.variables)
      (Paper2.AEth3.cutLen_ge Φ.val))
  have hblock := source_second_block_fit27 (cs + 2) N₁ hN₁ C x tape hfull
  have hword : Paper2.AEth3.cutLen Φ.val ≤ tape.length := hblock.1
  have hlen : (select27 hn edge Bsrc.degreeBound
      (sourceGap Dsrc Bsrc) k).inputBits ≤ tape.length := hcut.trans hword
  obtain ⟨t, ht⟩ := exists_tape_of_prefix27 hn edge
    Bsrc.degreeBound (sourceGap Dsrc Bsrc) k tape hlen
  have hclass := (Classical.choose_spec
    (source_classifier_fit27 Dsrc Bsrc (cs + 2) C)) Φ hsp hclassLarge t
  have hchecks := source_checks27_above Dsrc Bsrc Φ hschedLarge
  refine ⟨t, hchecks, hcut, ht, hinput.1, ?_⟩
  exact hclass.trans hblock.2.1

#print axioms routed_source_physical_fit27

#print axioms source_second_block_fit27

end
end Paper2.CurrentAdditive.QuarticClassEndpoint
