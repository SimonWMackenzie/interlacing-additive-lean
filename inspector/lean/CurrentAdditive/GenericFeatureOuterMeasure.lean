import CurrentAdditive.GenericFeaturePrefixByteBounds

noncomputable section
set_option autoImplicit false
namespace CurrentAdditive.GenericFeatureOuterMeasure
open EthInapproximability.CurrentPaper FeatureOldDescriptorFrame96

def extensionBytes (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat))) : Nat :=
  (cs.map (fun c => (FeatureEligibleDescriptor96.extensions j c ys).length)).sum

/-- This is a byte/count expression derived from the literal ordered lists.
It is not a supplied output-size bound or an execution certificate. -/
def measure (D j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) : Nat :=
  (SourceListEncoding.encode (words cs)).length+
    (SourceListEncoding.fields (words (CylinderOrderedSpec.extendList D j ys cs))).length+
    extensionBytes j ys cs+
    (SourceListEncoding.encode (FeatureInnerAlphabetRun64.labelWords ys)).length+
    j.bits.length+(j+1).bits.length+qfuel.length+jUnary.length+carry.length+cs.length+ys.length+1

end CurrentAdditive.GenericFeatureOuterMeasure
