import CurrentAdditive.QuarticPrefixTape
import Paper2.E3Inner

/-!
# Eventual v27 selector prefix length on sparse source formulas

The literal v27 selector uses at most the source decider's subexponential
first tape block. This is a size theorem, separate from a physical cut
program that computes the exact v27 prefix length.
-/

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open Paper2 Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2.CurrentAdditive.QuarticConstructor

theorem source_inputBits_fit27
    (Dsrc : DinurReduction) (Bsrc : BOTReduction (booleanOccurrence Dsrc))
    (cs : ℕ) :
    ∃ N₀ : ℕ, ∀ Φ : ValidFormula,
      Φ.val.clauses.length ≤ cs * Φ.val.variables →
      N₀ ≤ Φ.val.variables →
      1 ≤ kOf Φ.val.variables ∧
      (select27 (t10_vertices_pos Dsrc Bsrc Φ)
        (CanonicalEdgeTape.graphEdge (t10Graph Dsrc Bsrc Φ)
          (t10Graph_valid Dsrc Bsrc Φ))
        Bsrc.degreeBound (sourceGap Dsrc Bsrc) (kOf Φ.val.variables)).inputBits ≤
        Paper2.AEth.expLen Φ.val.variables := by
  obtain ⟨N₁, hN₁⟩ := Paper2.AEth3.bits_fit 160 (Dsrc.sizeExponent + 2)
  refine ⟨max N₁ (max 36
    (2 ^ (2 ^ (Dsrc.sizeExponent + 1) *
      Paper2.Unit4Shell.T10Size.t45C Dsrc Bsrc cs))), ?_⟩
  intro Φ hsp hN
  have h1 : N₁ ≤ Φ.val.variables := le_trans (le_max_left _ _) hN
  have h2 : 36 ≤ Φ.val.variables :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have h4 : 2 ^ (2 ^ (Dsrc.sizeExponent + 1) *
      Paper2.Unit4Shell.T10Size.t45C Dsrc Bsrc cs) ≤ Φ.val.variables :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hk : 1 ≤ kOf Φ.val.variables :=
    Paper2.Unit4Shell.AsymptoticsExplicit.kOf_pos _ h2
  have hbits :=
    (QuarticInputSize.selected_announced_counts_le27
      (t10_vertices_pos Dsrc Bsrc Φ)
      (CanonicalEdgeTape.graphEdge (t10Graph Dsrc Bsrc Φ)
        (t10Graph_valid Dsrc Bsrc Φ))
      Bsrc.degreeBound (sourceGap Dsrc Bsrc) (kOf Φ.val.variables) hk).2
  have hsize := Paper2.Unit4Shell.T10Size.t45_shell_form
    Dsrc Bsrc cs Φ hsp h4
  exact ⟨hk, le_trans hbits (hN₁ Φ.val.variables h1 _ hsize)⟩

theorem source_tape_of_cut_prefix27
    (Dsrc : DinurReduction) (Bsrc : BOTReduction (booleanOccurrence Dsrc))
    (cs : ℕ) :
    ∃ N₀ : ℕ, ∀ Φ : ValidFormula,
      Φ.val.clauses.length ≤ cs * Φ.val.variables →
      N₀ ≤ Φ.val.variables →
      ∀ word : List Bool, Paper2.AEth3.cutLen Φ.val ≤ word.length →
        ∃ t : (select27 (t10_vertices_pos Dsrc Bsrc Φ)
            (CanonicalEdgeTape.graphEdge (t10Graph Dsrc Bsrc Φ)
              (t10Graph_valid Dsrc Bsrc Φ))
            Bsrc.degreeBound (sourceGap Dsrc Bsrc) (kOf Φ.val.variables)).Tape,
          (select27 (t10_vertices_pos Dsrc Bsrc Φ)
            (CanonicalEdgeTape.graphEdge (t10Graph Dsrc Bsrc Φ)
              (t10Graph_valid Dsrc Bsrc Φ))
            Bsrc.degreeBound (sourceGap Dsrc Bsrc) (kOf Φ.val.variables)).tapeBits t =
            word.take (select27 (t10_vertices_pos Dsrc Bsrc Φ)
              (CanonicalEdgeTape.graphEdge (t10Graph Dsrc Bsrc Φ)
                (t10Graph_valid Dsrc Bsrc Φ))
              Bsrc.degreeBound (sourceGap Dsrc Bsrc) (kOf Φ.val.variables)).inputBits := by
  obtain ⟨N₀, hN₀⟩ := source_inputBits_fit27 Dsrc Bsrc cs
  refine ⟨N₀, ?_⟩
  intro Φ hsparse hlarge word hword
  have hfit := (hN₀ Φ hsparse hlarge).2
  have hcut := Paper2.AEth3.cutLen_ge Φ.val
  have hlen : (select27 (t10_vertices_pos Dsrc Bsrc Φ)
      (CanonicalEdgeTape.graphEdge (t10Graph Dsrc Bsrc Φ)
        (t10Graph_valid Dsrc Bsrc Φ))
      Bsrc.degreeBound (sourceGap Dsrc Bsrc) (kOf Φ.val.variables)).inputBits ≤
      word.length := by omega
  exact exists_tape_of_prefix27 _ _ _ _ _ word hlen

#print axioms source_inputBits_fit27
#print axioms source_tape_of_cut_prefix27

end Paper2.CurrentAdditive.QuarticClassEndpoint
