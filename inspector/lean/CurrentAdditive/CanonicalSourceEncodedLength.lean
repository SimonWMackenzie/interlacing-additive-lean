import CurrentAdditive.CanonicalEncodedLength
import CurrentAdditive.SmallBiasCanonicalSource

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalTable

open CurrentAdditive.SmallBias
open Paper2.YaoCloneSource Paper2.YaoX05Draft
open EthInapproximability.CurrentPaper.EncodedCommunication

/-- The exact source-to-instance output uses only polynomially many bits at
fixed gap parameter. This is a size bound, not a physical printing clock. -/
theorem source_canonical_encoded_length (g : ℕ)
    (G : GLSourceDraft (v27GapParameter g)) (input : List Bool) :
    let t := v27GapParameter g
    let source := cloneSource t (forbiddenColours t) (G.output input)
    let b := exactAddressBits source.2.1
    (encodeInstance (sourceCanonicalInstance g G input)).length ≤
      5 * tableConstant t * source.1 * (2 ^ b) ^ tableExponent t +
        2 * (2 * b + 4 * t + 2) + 3 := by
  dsimp only
  let t := v27GapParameter g
  let source := cloneSource t (forbiddenColours t) (G.output input)
  let b := exactAddressBits source.2.1
  have hv : 0 < source.1 := draft_clone_source_nonempty G input
  have ht : 4 ≤ t := v27GapParameter_ge_four g
  have h := encoded_instance_length_polynomial b t ht hv
    (sourceExactModulus g G input)
    (exactAddress_capacity source.2.1) source.2.2
  simpa only [sourceCanonicalInstance] using h

#print axioms source_canonical_encoded_length

end CurrentAdditive.FiniteFieldConstructor.CanonicalTable
