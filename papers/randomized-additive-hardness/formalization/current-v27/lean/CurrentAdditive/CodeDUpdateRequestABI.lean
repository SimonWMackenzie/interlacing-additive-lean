import CurrentAdditive.CodeDUpdateSourceFields
import CurrentAdditive.CodeDUpdatedArithmeticABI

/-! Ordered source-position arithmetic requests before physical callbacks. -/

namespace CurrentAdditive.CodeDUpdateRequestABI

open CodeDSourceCodecV2 CodeDCanonicalSourceV2

def requestItems {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ)
    (lambda : ℚ) : List (List Bool) :=
  (List.range source.size).filterMap (fun i =>
    (source[i]?).map (fun old =>
      CodeDUpdateProductPairFields.requestPacket (canonicalEntry old)
        lambda (coeff[i]?.getD 0)))

def requestPacketList {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ)
    (lambda : ℚ) : List Bool :=
  CodeDCodecV2.encodeItems (requestItems source coeff lambda)

theorem requestItems_length_le_source {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ)
    (lambda : ℚ) :
    (requestItems source coeff lambda).length ≤ source.size := by
  simp only [requestItems]
  calc
    ((List.range source.size).filterMap fun i =>
      (source[i]?).map fun old =>
        CodeDUpdateProductPairFields.requestPacket (canonicalEntry old)
          lambda (coeff[i]?.getD 0)).length ≤ (List.range source.size).length :=
        List.length_filterMap_le _ _
    _ = source.size := by simp

#print axioms requestItems_length_le_source

end CurrentAdditive.CodeDUpdateRequestABI
