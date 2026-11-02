import CurrentV43.Randomized.Source
namespace CurrentV43.RandomizedRate
noncomputable section
open CurrentAdditive Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition Unit4Shell.T10Finite
variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))
def sourceCoefficient (Φ : ValidFormula) :=
  V38Schedule.fullConstant (sourceGap D B) B.degreeBound
    (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length
def sourceDeltaV (Φ : ValidFormula) :=
  V38Schedule.sourceDeltaV (sourceGap D B) B.degreeBound
    (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length
def sourceZeta := V38Schedule.sourceZeta (sourceGap D B)

end
end CurrentV43.RandomizedRate
