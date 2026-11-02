import Paper2.YaoFullScalarJoin
import Paper2.YaoParameterLayout

/-! Source-level check for the literal scalar words required by the existing
combined Yao entry evaluator. This file does not identify the distinct stack
types or claim a machine handoff. -/

namespace Paper2.YaoEntryParameterJoin

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

open Paper2.YaoLowerBound
open Paper2.YaoLowerBound.Materialization
open Paper2.YaoLookup
open Paper2.YaoEntryParameters
open Paper2.YaoParameterBank

theorem selector_value_is_entry_offset (t lambda e : ℕ)
    (z : Fin (selectorCount t (paddedEdgeBits e) lambda))
    (g : Fin (2 ^ (t - 1))) :
    (z.val * fixedQ t + g.val) * paddedEdgeBits e =
      Paper2.YaoPreservedFlatSlice.selectorOffset t (paddedEdgeBits e)
        lambda z g := by
  simpa only [fixedQ] using
    selector_scalar_is_entry_offset t (paddedEdgeBits e) lambda z g

theorem payload_value_is_entry_base (t lambda e : ℕ)
    (l : Fin (payloadCount t (paddedEdgeBits e) lambda))
    (p : Fin (2 ^ t * 2 ^ t + 1)) :
    payloadBaseValue t lambda e l.val p.val =
      Paper2.YaoPayloadLoop.payloadBase t (paddedEdgeBits e) lambda l p := by
  simp only [payloadBaseValue, fixedQ, fixedK, paddedEdgeCount,
    Paper2.YaoPayloadLoop.payloadBase]
  simp only [Nat.mul_assoc]

theorem stride_value_is_entry_stride (t : ℕ) :
    fixedK t = Paper2.YaoPayloadLoop.payloadStride t := rfl

theorem count_value_is_entry_count (e : ℕ) :
    paddedEdgeCount e = 2 ^ paddedEdgeBits e := rfl

#print axioms selector_value_is_entry_offset
#print axioms payload_value_is_entry_base
#print axioms stride_value_is_entry_stride
#print axioms count_value_is_entry_count

end Paper2.YaoEntryParameterJoin
