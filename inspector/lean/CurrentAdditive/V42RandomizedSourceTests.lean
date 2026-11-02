import CurrentAdditive.V42RandomizedSourceData
namespace CurrentAdditive.V42RandomizedETHEndpoint
open Paper2 EthInapproximability.CurrentPaper EncodedETHSource EncodedETHSourceComposition
open Unit4Shell.T10Finite
abbrev SourceTests (D : DinurReduction) (B : BOTReduction (booleanOccurrence D)) (Φ : ValidFormula) :=
  V42RuntimeSchedule.FullTests
    (V38Schedule.fullConstant (sourceGap D B) B.degreeBound
      (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length)
    (Nat.clog 2 (t10Graph D B Φ).vertices) (t10Graph D B Φ).edges.length
    (V38Schedule.sourceDeltaV (sourceGap D B) B.degreeBound
      (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length)
    (V38Schedule.sourceZeta (sourceGap D B))
end CurrentAdditive.V42RandomizedETHEndpoint
