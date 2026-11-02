import EthInapproximability.CurrentPaper.SourceNormalizationMachineGraphCost
import EthInapproximability.CurrentPaper.SourceNormalizationNumericSource

/-! The ordered abstract normalizer and the physical finite-stack graph output
agree exactly on valid encoded input, including its occurrence order. -/

namespace EthInapproximability.CurrentPaper.SourceNormalizationMachineComplete

open Turing BitMachineEncoding

theorem final_abstract_output (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) :
    (SourceNormalizationMachineGraphOutput.finalHost g originalN).stk
        (SourceNormalizationMachineGraphOutput.finalizerStack 4) =
      EncodedGraph.encode
        (SourceNormalizationNumericSource.serializeNormalized
          (EncodedETHSource.rawGraph g hg) originalN) := by
  rw [SourceNormalizationMachineGraphOutput.final_output,
    SourceNormalizationNumericSource.serializeNormalized_raw]
  rfl

theorem physical_normalization_run (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) :
    ∃ t ≤ 10000 * (UnaryBinaryEncoding.coefficient + 5) *
        ((EncodedGraph.encode g).length + originalN + 4)^8,
      SourceNormalizationMachineGraphOutput.run t
        (SourceNormalizationMachineGraphOutput.start
          (EncodedGraph.encode g) originalN) =
          SourceNormalizationMachineGraphOutput.finalHost g originalN ∧
      (SourceNormalizationMachineGraphOutput.finalHost g originalN).stk
          (SourceNormalizationMachineGraphOutput.finalizerStack 4) =
            EncodedGraph.encode
              (SourceNormalizationNumericSource.serializeNormalized
                (EncodedETHSource.rawGraph g hg) originalN) ∧
      (SourceNormalizationMachineGraphOutput.finalHost g originalN).stk
          SourceNormalizationMachineGraphCost.originalNStack =
            List.replicate originalN true := by
  obtain ⟨t,ht,hr⟩ := SourceNormalizationMachineGraphCost.graph_output_polynomial_run
    g hg originalN
  exact ⟨t,ht,hr,final_abstract_output g hg originalN,
    SourceNormalizationMachineGraphCost.final_originalN g originalN⟩

end EthInapproximability.CurrentPaper.SourceNormalizationMachineComplete
