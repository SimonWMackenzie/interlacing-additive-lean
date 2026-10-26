import Paper2.YaoEntryBankIdentity

/-! Actual parameter-loader endpoint: one physical controller from basic unary
`e,z,g,ell,position` to the exact scalar bank of the existing entry machine.
The position word, valid typed indices, and serialized flat tape are supplied
at the boundary; their graph/source parsing is not asserted here. -/

namespace Paper2.YaoEntryParameterJoin

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

open Turing
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.YaoLowerBound
open Paper2.YaoLowerBound.Materialization
open Paper2.YaoLookup
open Paper2.YaoParameterBank

theorem physical_routed_entry_bank {v e : ℕ} (t lambda : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (bits : SerializedTape t (paddedEdgeBits e) lambda)
    (vertex : Fin v)
    (z : Fin (selectorCount t (paddedEdgeBits e) lambda))
    (g : Fin (2 ^ (t - 1))) (a : Fin (paddedEdgeCount e))
    (l : Fin (payloadCount t (paddedEdgeBits e) lambda)) :
    ∃ (scalarSteps routeSteps total : ℕ)
      (S : PayloadStack t lambda → List Bool),
      scalarSteps ≤ scalarBudget t lambda e z.val g.val l.val
        (positionEval (paddedEdgesEval edges) a vertex).val ∧
      total ≤ scalarSteps + routeSteps + 1 ∧
      routeSteps ≤ 2*((z.val * fixedQ t + g.val) * paddedEdgeBits e +
        paddedEdgeBits e + payloadBaseValue t lambda e l.val
          (positionEval (paddedEdgesEval edges) a vertex).val +
        fixedK t + paddedEdgeCount e)+10 ∧
      let c0 := selectorInitial t lambda e z.val g.val l.val
        (positionEval (paddedEdgesEval edges) a vertex).val
      let stageV0 : StageOneControl t lambda :=
        ((frameStart t lambda e z.val g.val l.val
          (positionEval (paddedEdgesEval edges) a vertex).val).var,())
      let v0 := c0.var
      let S₀ : PayloadStack t lambda → List Bool :=
        Sum.elim c0.stk (fun _ => [])
      ((advance (routedParameterProgram t lambda stageV0 v0))^[total])
        (⟨some (.inl (.inl (.inl (.inl (.inl (.inl
          (widthStartLabel t lambda))))))),
          ((((v0,()),false),()),none),
          Sum.elim S₀ (routedForeign bits.val)⟩ :
          TM2.Cfg (fun _ : RouteStack t lambda => Bool) _ _) =
        ⟨none,((((v0,()),false),()),none),routedFinal S bits.val⟩ ∧
      (fun i : Fin 13 => routedFinal S bits.val (.inr (.inl i))) =
        (Paper2.YaoEntryComposition.entryInput t lambda edges bits vertex z g a l).stk := by
  let p := positionEval (paddedEdgesEval edges) a vertex
  obtain ⟨scalarSteps,routeSteps,total,S,hbudget,htotal,hroute,
    hrun,h0,h1,h2,h3,h4,_⟩ :=
    physical_routed_parameter_join t lambda e z.val g.val l.val p.val bits.val
  have hs0 : S (.inl (selectorSlot t lambda 11)) =
      List.replicate ((z.val * fixedQ t + g.val) * paddedEdgeBits e) true := by
    exact (routed_final_targets t lambda S bits.val 0).symm.trans h0
  have hs1 : S (bCell t lambda) = List.replicate (paddedEdgeBits e) true := by
    exact (routed_final_targets t lambda S bits.val 1).symm.trans h1
  have hs2 : S (fresh t lambda 6) =
      List.replicate (payloadBaseValue t lambda e l.val p.val) true := by
    exact (routed_final_targets t lambda S bits.val 2).symm.trans h2
  have hs3 : S (strideCell t lambda) = List.replicate (fixedK t) true := by
    exact (routed_final_targets t lambda S bits.val 3).symm.trans h3
  have hs4 : S (hCell t lambda) = List.replicate (paddedEdgeCount e) true := by
    exact (routed_final_targets t lambda S bits.val 4).symm.trans h4
  refine ⟨scalarSteps,routeSteps,total,S,hbudget,htotal,hroute,?_⟩
  dsimp only
  exact ⟨by simpa only [p] using hrun,
    routed_bank_is_entry_input t lambda edges bits vertex z g a l S
      hs0 hs1 hs2 hs3 hs4⟩

#print axioms physical_routed_entry_bank

end Paper2.YaoEntryParameterJoin
