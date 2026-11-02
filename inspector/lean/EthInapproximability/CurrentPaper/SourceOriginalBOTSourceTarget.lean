import EthInapproximability.CurrentPaper.SourceOriginalBOTCanonicalListMapperCost
import EthInapproximability.CurrentPaper.EncodedETHSourceComposition

/-! Exact semantic target for a future physical post-Dinur/CSP packet producer. -/

namespace EthInapproximability.CurrentPaper.SourceOriginalBOTSourceTarget

variable {η : ℚ}
  (S : EncodedETHSource.Sparsification η)
  (D : EncodedETHSource.DinurReduction)
  (B : EncodedETHSource.BOTReduction
    (EncodedETHSourceComposition.booleanOccurrence D))

def booleanPacketList (f : EncodedETHSource.ValidFormula) : List Bool :=
  SourceOriginalBOTCanonicalListMapper.inputList f.val.variables
    (EncodedETHSourceComposition.booleanBranches S D f)

def normalizedGraphPacketList (f : EncodedETHSource.ValidFormula) : List Bool :=
  SourceOriginalBOTCanonicalListMapper.outputList B f.val.variables
    (EncodedETHSourceComposition.booleanBranches S D f)

theorem normalizedGraphPacketList_sourceGraphs
    (f : EncodedETHSource.ValidFormula) :
    normalizedGraphPacketList S D B f =
      SourceListEncoding.encode
        ((EncodedETHSourceComposition.sourceGraphs S D B f).map fun g =>
          SourceOriginalBranchPackets.packet f.val.variables
            (EncodedGraph.encode g.val)) := by
  simp only [normalizedGraphPacketList,
    SourceOriginalBOTCanonicalListMapper.outputList,
    SourceOriginalBOTCanonicalListMapper.outputItems,
    EncodedETHSourceComposition.sourceGraphs,
    EncodedETHSource.BOTReduction.graphList, List.map_map]
  rfl

theorem canonical_map (f : EncodedETHSource.ValidFormula) :
    (SourceOriginalBOTCanonicalListMapper.machine B).OutputsWithin
      (booleanPacketList S D f)
      (normalizedGraphPacketList S D B f)
      (SourceOriginalBOTCanonicalListMapper.mapTime B f.val.variables
        (EncodedETHSourceComposition.booleanBranches S D f)) := by
  exact SourceOriginalBOTCanonicalListMapper.mapped_outputs B _ _

end EthInapproximability.CurrentPaper.SourceOriginalBOTSourceTarget
