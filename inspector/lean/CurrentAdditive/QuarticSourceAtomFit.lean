import CurrentAdditive.QuarticSourceRawFit
import CurrentAdditive.QuarticSourceBankSize
import CurrentAdditive.QuarticUniformInputCap

/-! All charged source words, including the selected public bank, fit the effective tape scale. -/

namespace Paper2.CurrentAdditive.QuarticSourceAtomFit

open Paper2 Paper2.CurrentAdditive.QuarticConstructor
open Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2.CurrentAdditive.QuarticClassEndpoint
open Paper2.CurrentAdditive.QuarticSourceRawFit
open Paper2.CurrentAdditive.QuarticTMClockRepair

noncomputable section
set_option maxHeartbeats 8000000

theorem source_atom_fit
    (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))
    (cs : ℕ) :
    ∃ N₀ : ℕ, ∀ Φ : ValidFormula,
      Φ.val.clauses.length ≤ cs * Φ.val.variables →
      N₀ ≤ Φ.val.variables →
      let g := t10Graph D B Φ
      let hg := t10Graph_valid D B Φ
      let hn := t10_vertices_pos D B Φ
      let k := kOf Φ.val.variables
      let U := Paper2.AEth.expLen Φ.val.variables
      ∀ tape : List Bool,
      ∀ t : (select27 hn (CanonicalEdgeTape.graphEdge g hg)
        B.degreeBound (sourceGap D B) k).Tape,
        (EncodedCNF.encode Φ.val).length ≤ U ∧
        (tape.take (Paper2.AEth3.cutLen Φ.val)).length ≤ 5 * U ∧
        (g.vertices + 2) ^
          (rawExponent B.degreeBound (sourceGap D B) * (k + 1)) ≤ U ∧
        (g.vertices + 2) ^ (360 * (k + 1)) ≤ U ∧
        (BitMachineBankCodec.encode
          (QuarticDispatchSpec.inputBank27 B.degreeBound (sourceGap D B)
            g hg hn k t)).length ≤ (4 * B.degreeBound + 9) * U := by
  obtain ⟨Nraw, hraw⟩ := formula_and_raw_fit cs
  obtain ⟨Np, hp⟩ := source_graph_power_fit27 D B cs
    (rawExponent B.degreeBound (sourceGap D B))
  obtain ⟨Nq, hq⟩ := source_graph_power_fit27 D B cs 360
  obtain ⟨Nb, hb⟩ := source_graph_power_fit27 D B cs 160
  refine ⟨max Nraw (max Np (max Nq (max Nb 36))), ?_⟩
  intro Φ hsparse hlarge g hg hn k U tape t
  have hR : Nraw ≤ Φ.val.variables := (le_max_left _ _).trans hlarge
  have hP : Np ≤ Φ.val.variables :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
  have hQ : Nq ≤ Φ.val.variables :=
    (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans hlarge))
  have hB : Nb ≤ Φ.val.variables :=
    (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hlarge)))
  have h36 : 36 ≤ Φ.val.variables :=
    (le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hlarge)))
  obtain ⟨hX, hRaw⟩ := hraw Φ hsparse hR
  have hPraw := hp Φ hsparse hP
  have hPcut := hq Φ hsparse hQ
  have hPbank := hb Φ hsparse hB
  have hO := source_inputBank_size27 D B Φ h36 t
  refine ⟨hX, hRaw tape, hPraw, hPcut, ?_⟩
  exact hO.trans (Nat.mul_le_mul_left _ hPbank)

#print axioms source_atom_fit

end
end Paper2.CurrentAdditive.QuarticSourceAtomFit
