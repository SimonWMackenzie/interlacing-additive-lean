import Paper2.YaoRoutedParameterJoin
import Paper2.YaoEntryCombined

/-! Compare the checked routed scalar bank with the exact existing combined
entry evaluator's input bank. This theorem does not parse the basic unary
parameters from graph/source code, and does not compose the evaluator's
controller transition after the parameter loader's halting state. -/

namespace Paper2.YaoEntryParameterJoin

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

open Paper2.YaoLowerBound
open Paper2.YaoLowerBound.Materialization
open Paper2.YaoLookup
open Paper2.YaoParameterBank

theorem routed_bank_is_entry_input {v e : ℕ} (t lambda : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (bits : SerializedTape t (paddedEdgeBits e) lambda)
    (vertex : Fin v)
    (z : Fin (selectorCount t (paddedEdgeBits e) lambda))
    (g : Fin (2 ^ (t - 1))) (a : Fin (paddedEdgeCount e))
    (l : Fin (payloadCount t (paddedEdgeBits e) lambda))
    (S : PayloadStack t lambda → List Bool)
    (h0 : S (.inl (selectorSlot t lambda 11)) =
      List.replicate ((z.val * fixedQ t + g.val) * paddedEdgeBits e) true)
    (h1 : S (bCell t lambda) = List.replicate (paddedEdgeBits e) true)
    (h2 : S (fresh t lambda 6) =
      List.replicate (payloadBaseValue t lambda e l.val
        (positionEval (paddedEdgesEval edges) a vertex).val) true)
    (h3 : S (strideCell t lambda) = List.replicate (fixedK t) true)
    (h4 : S (hCell t lambda) = List.replicate (paddedEdgeCount e) true) :
    (fun i : Fin 13 => routedFinal S bits.val (.inr (.inl i))) =
      (Paper2.YaoEntryComposition.entryInput t lambda edges bits vertex z g a l).stk := by
  have hr0 : routedFinal S bits.val (.inr (.inl (0 : Fin 13))) =
      List.replicate (Paper2.YaoPreservedFlatSlice.selectorOffset t
        (paddedEdgeBits e) lambda z g) true := by
    have h := (routed_final_targets t lambda S bits.val 0).trans h0
    simpa only [routeTarget,routeScalarSource,
      selector_value_is_entry_offset] using h
  have hr7 : routedFinal S bits.val (.inr (.inl (7 : Fin 13))) =
      List.replicate (paddedEdgeBits e) true := by
    simpa only [routeTarget,routeScalarSource] using
      (routed_final_targets t lambda S bits.val 1).trans h1
  have hr8 : routedFinal S bits.val (.inr (.inl (8 : Fin 13))) =
      List.replicate (Paper2.YaoPayloadLoop.payloadBase t
        (paddedEdgeBits e) lambda l
        (positionEval (paddedEdgesEval edges) a vertex)) true := by
    have h := (routed_final_targets t lambda S bits.val 2).trans h2
    simpa only [routeTarget,routeScalarSource,
      payload_value_is_entry_base] using h
  have hr9 : routedFinal S bits.val (.inr (.inl (9 : Fin 13))) =
      List.replicate (Paper2.YaoPayloadLoop.payloadStride t) true := by
    have h := (routed_final_targets t lambda S bits.val 3).trans h3
    simpa only [routeTarget,routeScalarSource,
      stride_value_is_entry_stride] using h
  have hr10 : routedFinal S bits.val (.inr (.inl (10 : Fin 13))) =
      List.replicate (2 ^ paddedEdgeBits e) true := by
    have h := (routed_final_targets t lambda S bits.val 4).trans h4
    simpa only [routeTarget,routeScalarSource,
      count_value_is_entry_count] using h
  funext i
  fin_cases i <;>
    norm_num [Paper2.YaoEntryComposition.entryInput,
      Paper2.YaoEntryComposition.cfg] <;>
    first | exact hr0 | exact hr7 | exact hr8 | exact hr9 |
      exact hr10 | exact routed_final_source t lambda S bits.val | rfl

#print axioms routed_bank_is_entry_input

end Paper2.YaoEntryParameterJoin
