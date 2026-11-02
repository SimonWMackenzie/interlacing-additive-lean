import Paper2.YaoLogPowerFullBank

/-! Four simultaneously retained unary values of the single composed
edge-count-to-selector-count program. Exact other stacks are the concrete
`rightCfg` expression, not an arbitrary desired-value certificate. -/

namespace Paper2.YaoParameterBank

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachine
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineComposition
open Paper2.YaoParameterLoader
open Paper2.YaoLowerBound
open Paper2.YaoLookup

private theorem padded_bits_eq_clog (e : ℕ) :
    paddedEdgeBits e = Nat.clog 2 e := by
  cases e with
  | zero => decide
  | succ e => simp [paddedEdgeBits]

private theorem power_input_ne_output :
    MatrixUnaryPower.machine.input ≠ MatrixUnaryPower.machine.output := by
  intro h
  have hh := (Fintype.equivFin MatrixUnaryPower.Stack).injective h
  exact Sum.inr_ne_inl hh

noncomputable def edgeCell : Fin logPowerMachine.stackCount :=
  (Fintype.equivFin (BitMachineComposition.Stack
    ETHParameterScaleMachineLogCopy.machine MatrixUnaryPower.machine))
    (.inl ETHParameterScaleMachineLogCopy.machine.input)

noncomputable def bitsCell : Fin logPowerMachine.stackCount :=
  (Fintype.equivFin (BitMachineComposition.Stack
    ETHParameterScaleMachineLogCopy.machine MatrixUnaryPower.machine))
    (.inr (.inl MatrixUnaryPower.machine.input))

private theorem edgeCell_ne_output : edgeCell ≠ logPowerMachine.output := by
  intro h
  have hh := (Fintype.equivFin (BitMachineComposition.Stack
    ETHParameterScaleMachineLogCopy.machine MatrixUnaryPower.machine)).injective h
  exact Sum.inl_ne_inr hh

private theorem bitsCell_ne_output : bitsCell ≠ logPowerMachine.output := by
  intro h
  have hh := (Fintype.equivFin (BitMachineComposition.Stack
    ETHParameterScaleMachineLogCopy.machine MatrixUnaryPower.machine)).injective h
  exact power_input_ne_output (Sum.inl_injective (Sum.inr_injective hh))

/-- In one actual program, after both nested charged transfers, `e`,
`b`, `H`, and the exact v12 selector-sample count coexist in disjoint banks.
The two prior outputs that were transferred are empty; the full remaining
stack function is the displayed `rightCfg` of actual submachine runs. -/
theorem edge_to_count_four_banks (t e lambda : ℕ) :
    ∃ (a b : ℕ),
      a ≤ 2*e+2 + (UnaryBinaryEncoding.coefficient+6)*(e+1)^2 +
        2*paddedEdgeBits e+2 + 16*paddedEdgeCount e ∧
      b ≤ 1 + MatrixAddressMachine.exactTime (paddedEdgeCount e)
        (fixedWidth t) (fixedTail t lambda) ∧
      let A := logPowerMachine
      let B := selectorCountMachine t lambda
      let ca := A.run a (A.init (List.replicate e true))
      let cb := B.run b (B.init (List.replicate (paddedEdgeCount e) true))
      let final := ((advance (program A B))^[
        a + 2*paddedEdgeCount e+2+b])
          (rawInit (.inl A.input) (.inl A.start)
            (A.initial,B.initial,none) (List.replicate e true))
      final = rightCfg A B ca.var
        (Function.update ca.stk A.output []) cb ∧
      final.l = none ∧
      final.stk (.inl edgeCell) = List.replicate e true ∧
      final.stk (.inl bitsCell) =
        List.replicate (paddedEdgeBits e) true ∧
      final.stk (.inr (.inl B.input)) =
        List.replicate (paddedEdgeCount e) true ∧
      final.stk (.inr (.inl B.output)) =
        List.replicate (selectorCount t (paddedEdgeBits e) lambda) true := by
  let A := logPowerMachine
  let B := selectorCountMachine t lambda
  obtain ⟨a,b,ha,hb,hAhalt,_,hBhalt,hBout,hrun⟩ :=
    composition_full_run A B (log_power_outputs e)
      (selector_count_outputs t (paddedEdgeBits e) lambda)
  have hrun' : ((advance (program A B))^[
        a + 2*paddedEdgeCount e+2+b])
          (rawInit (.inl A.input) (.inl A.start)
            (A.initial,B.initial,none) (List.replicate e true)) =
      rightCfg A B (A.run a (A.init (List.replicate e true))).var
        (Function.update (A.run a (A.init (List.replicate e true))).stk A.output [])
        (B.run b (B.init (List.replicate (paddedEdgeCount e) true))) := by
    simpa only [List.length_replicate] using hrun
  refine ⟨a,b,ha,?_,?_⟩
  · simpa only [paddedEdgeCount] using hb
  · dsimp only
    refine ⟨hrun', ?_, ?_, ?_, ?_, ?_⟩
    · rw [hrun']
      exact rightCfg_halt A B _ _ _ hBhalt
    · rw [hrun', rightCfg_left_bank,
        Function.update_of_ne edgeCell_ne_output]
      exact logPower_halt_preserves_edge e a hAhalt
    · rw [hrun', rightCfg_left_bank,
        Function.update_of_ne bitsCell_ne_output]
      simpa only [padded_bits_eq_clog] using
        logPower_halt_preserves_bits e a hAhalt
    · rw [hrun', rightCfg_right_bank]
      exact selector_count_halt_preserves_H t (paddedEdgeBits e) lambda b hBhalt
    · rw [hrun', rightCfg_right_bank]
      exact hBout

#print axioms edge_to_count_four_banks

end Paper2.YaoParameterBank
