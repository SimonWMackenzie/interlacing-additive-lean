import Paper2.YaoParameterCore
import Paper2.YaoPayloadLoop
import Paper2.YaoPreservedFlatSlice

/-! Algebraic boundary between the physically produced unary words and the
literal flat-tape coordinates used by the combined entry machine. This file
does not assert an unimplemented machine handoff. -/

namespace Paper2.YaoEntryParameters

open Paper2.YaoLowerBound
open Paper2.YaoLowerBound.Materialization

theorem selector_scalar_is_entry_offset (t b lambda : ℕ)
    (z : Fin (selectorCount t b lambda))
    (g : Fin (2 ^ (t - 1))) :
    (z.val * 2 ^ (t - 1) + g.val) * b =
      Paper2.YaoPreservedFlatSlice.selectorOffset t b lambda z g := rfl

theorem payload_scalar_is_entry_base (t b lambda : ℕ)
    (l : Fin (payloadCount t b lambda))
    (p : Fin (2 ^ t * 2 ^ t + 1)) :
    selectorCount t b lambda * 2 ^ (t - 1) * b +
      relativePayload l.val (2 ^ b) (2 ^ t * 2 ^ t + 1) p.val =
      Paper2.YaoPayloadLoop.payloadBase t b lambda l p := by
  dsimp only [relativePayload, Paper2.YaoPayloadLoop.payloadBase]
  simp only [Nat.mul_assoc, Nat.add_assoc]

#print axioms selector_scalar_is_entry_offset
#print axioms payload_scalar_is_entry_base

end Paper2.YaoEntryParameters
