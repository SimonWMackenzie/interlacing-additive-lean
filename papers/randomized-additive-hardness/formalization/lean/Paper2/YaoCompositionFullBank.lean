import Paper2.YaoSelectorCountMachine
import EthInapproximability.CurrentPaper.BitMachineCompositionArithmetic

/-! Exact final stack configuration for the already concrete two-pass
machine composition. Output-only `OutputsWithin` is deliberately not used
as a substitute for physical bank placement. -/

namespace Paper2.YaoParameterBank

set_option maxRecDepth 2048

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachine
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineComposition
open EthInapproximability.CurrentPaper.BitMachineCompositionArithmetic

theorem composition_full_run (A B : Machine)
    {input middle output : List Bool} {ta tb : ℕ}
    (ha : A.OutputsWithin input middle ta)
    (hb : B.OutputsWithin middle output tb) :
    ∃ (a b : ℕ), a ≤ ta ∧ b ≤ tb ∧
      (A.run a (A.init input)).l = none ∧
      (A.run a (A.init input)).stk A.output = middle ∧
      (B.run b (B.init middle)).l = none ∧
      (B.run b (B.init middle)).stk B.output = output ∧
      ((advance (program A B))^[a + 2 * middle.length + 2 + b])
        (rawInit (.inl A.input) (.inl A.start)
          (A.initial, B.initial, none) input) =
        rightCfg A B (A.run a (A.init input)).var
          (Function.update (A.run a (A.init input)).stk A.output [])
          (B.run b (B.init middle)) := by
  obtain ⟨a, haTime, haHalt, haOut, haFirst⟩ := first_halt A ha
  obtain ⟨b, hbTime, hbHalt, hbOut⟩ := hb
  let c := A.run a (A.init input)
  let d := B.run b (B.init middle)
  refine ⟨a, b, haTime, hbTime, haHalt, haOut, hbHalt, hbOut, ?_⟩
  have hleft := left_run A B (A.init input) a haFirst
  have htransfer := transfer_run A B c haHalt
  have hright := right_run A B c.var
    (Function.update c.stk A.output []) (B.init middle) b
  have hlen : (c.stk A.output).length = middle.length := congrArg List.length haOut
  change ((advance (program A B))^[a + 2 * middle.length + 2 + b])
      (rawInit (.inl A.input) (.inl A.start)
        (A.initial, B.initial, none) input) =
      rightCfg A B c.var (Function.update c.stk A.output []) d
  rw [rawInit_eq_left A B input]
  rw [show a + 2 * middle.length + 2 + b =
      b + (((c.stk A.output).length + 1 +
        ((c.stk A.output).length + 1)) + a) by omega]
  rw [Function.iterate_add_apply, Function.iterate_add_apply]
  rw [hleft, htransfer, haOut, hright]

theorem rightCfg_left_bank (A B : Machine)
    (v : Fin A.controlCount) (S : Fin A.stackCount → List Bool)
    (c : B.Config) (k : Fin A.stackCount) :
    (rightCfg A B v S c).stk (.inl k) = S k := by
  simp [rightCfg, renameCfg, liftCfg, stackSwap]

theorem rightCfg_right_bank (A B : Machine)
    (v : Fin A.controlCount) (S : Fin A.stackCount → List Bool)
    (c : B.Config) (k : Fin B.stackCount) :
    (rightCfg A B v S c).stk (.inr (.inl k)) = c.stk k := by
  simp [rightCfg, renameCfg, liftCfg, stackSwap]

theorem rightCfg_halt (A B : Machine)
    (v : Fin A.controlCount) (S : Fin A.stackCount → List Bool)
    (c : B.Config) (hc : c.l = none) :
    (rightCfg A B v S c).l = none := by
  simp [rightCfg, renameCfg, liftCfg, hc]

theorem composition_numbered_run (A B : Machine) (input : List Bool)
    (n : ℕ) :
    (composition A B).run n ((composition A B).init input) =
      renameCfg (Fintype.equivFin (BitMachineComposition.Stack A B))
        (Fintype.equivFin (BitMachineComposition.Label A B))
        (Fintype.equivFin (BitMachineComposition.Control A B))
        (((advance (program A B))^[n])
          (rawInit (.inl A.input) (.inl A.start)
            (A.initial,B.initial,none) input)) := by
  change (ofFinite (.inl A.input) (.inr (.inl B.output))
    (.inl A.start) (A.initial,B.initial,none)
    (program A B)).run n
      ((ofFinite (.inl A.input) (.inr (.inl B.output))
        (.inl A.start) (A.initial,B.initial,none)
        (program A B)).init input) = _
  rw [ofFinite_init]
  simpa only [BitMachineComposition.Control] using
    ofFinite_run (.inl A.input) (.inr (.inl B.output))
      (.inl A.start) (A.initial,B.initial,none)
      (program A B)
      (rawInit (.inl A.input) (.inl A.start)
        (A.initial,B.initial,none) input) n

#print axioms composition_full_run

end Paper2.YaoParameterBank
