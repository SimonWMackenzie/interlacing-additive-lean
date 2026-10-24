import EthInapproximability.CurrentPaper.BitMachineComposition

set_option maxRecDepth 4096

/-!
The ordinary output theorem for sequential machine composition hides its
intermediate stacks.  The Gauss cell controller needs to keep the parsed
current entry and row entry while a quotient subroutine runs.  This lemma
records the physical fact that composition only empties the first machine's
designated output stack; every other first-machine stack survives the second
call byte for byte.
-/

namespace CurrentAdditive.GaussCompositionRetained

open Turing
open EthInapproximability.CurrentPaper
open BitMachine BitMachineEncoding BitMachineComposition

theorem retained_left (A B : BitMachine.Machine)
    {input middle output : List Bool} {ta tb : Nat}
    (ha : A.OutputsWithin input middle ta)
    (hb : B.OutputsWithin middle output tb)
    (k : Fin A.stackCount) (hk : k ≠ A.output) :
    ∃ t ≤ ta + 2*middle.length + 2 + tb,
      let c := ((advance (program A B))^[t])
        (rawInit (Sum.inl A.input) (Sum.inl A.start)
          (A.initial, B.initial, none) input)
      c.l = none ∧
      c.stk (.inl k) = (A.run ta (A.init input)).stk k ∧
      c.stk (.inr (.inl B.output)) = output := by
  obtain ⟨a, ha_le, ha_halt, ha_out, ha_first⟩ :=
    BitMachineCompositionArithmetic.first_halt A ha
  obtain ⟨b, hb_le, hb_halt, hb_out⟩ := hb
  let c := A.run a (A.init input)
  have hrun :
      ((advance (program A B))^[b + (middle.length + 1 +
        (middle.length + 1) + a)])
        (rawInit (Sum.inl A.input) (Sum.inl A.start)
          (A.initial, B.initial, none) input) =
      rightCfg A B c.var (Function.update c.stk A.output [])
        (B.run b (B.init middle)) := by
    rw [rawInit_eq_left, Function.iterate_add_apply,
      Function.iterate_add_apply, left_run A B _ a ha_first]
    have hc : (c.stk A.output).length = middle.length :=
      congrArg List.length ha_out
    rw [← hc, transfer_run A B c ha_halt, ha_out, right_run]
  have hc_eq : c = A.run ta (A.init input) := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le ha_le
    rw [hd, run_add, run_halted A _ ha_halt]
  refine ⟨b + (middle.length + 1 + (middle.length + 1) + a), by omega, ?_⟩
  simp only [hrun]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [rightCfg, renameCfg, liftCfg, hb_halt,
      Option.map_none]
  · change (Function.update c.stk A.output []) k =
      (A.run ta (A.init input)).stk k
    simp only [Function.update_apply, hk, ite_false, hc_eq]
  · change (B.run b (B.init middle)).stk B.output = output
    exact hb_out

theorem retained_left_at_bound (A B : BitMachine.Machine)
    {input middle output : List Bool} {ta tb : Nat}
    (ha : A.OutputsWithin input middle ta)
    (hb : B.OutputsWithin middle output tb)
    (k : Fin A.stackCount) (hk : k ≠ A.output) :
    ((composition A B).run (ta + 2*middle.length + 2 + tb)
      ((composition A B).init input)).stk
        (Fintype.equivFin (Stack A B) (.inl k)) =
      (A.run ta (A.init input)).stk k := by
  obtain ⟨t,ht,hh,hbank,_⟩ :=
    retained_left A B ha hb k hk
  let C := composition A B
  let raw : TM2.Cfg (fun _ : Stack A B => Bool)
      (Label A B) (Control A B) :=
    rawInit (Sum.inl A.input : Stack A B)
    (Sum.inl A.start : Label A B)
    (A.initial, B.initial, none) input
  have hi := ofFinite_init (Sum.inl A.input)
    (Sum.inr (Sum.inl B.output)) (Sum.inl A.start)
    (A.initial, B.initial, none) (program A B) input
  have hr := ofFinite_run (Sum.inl A.input)
    (Sum.inr (Sum.inl B.output)) (Sum.inl A.start)
    (A.initial, B.initial, none) (program A B) raw t
  have hcfg : C.run t (C.init input) =
      renameCfg (Fintype.equivFin (Stack A B))
        (Fintype.equivFin (Label A B))
        (Fintype.equivFin (Control A B))
        (((advance (program A B))^[t]) raw) := by
    rw [show C.init input = _ from hi]
    simpa only [C, composition, raw] using hr
  have hhalt : (C.run t (C.init input)).l = none := by
    rw [hcfg]
    simpa only [renameCfg, Option.map_none] using
      congrArg (Option.map (Fintype.equivFin (Label A B))) hh
  have hword : (C.run t (C.init input)).stk
      (Fintype.equivFin (Stack A B) (.inl k)) =
      (A.run ta (A.init input)).stk k := by
    rw [hcfg]
    simpa only [renameCfg, Equiv.symm_apply_apply] using hbank
  obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le ht
  change (C.run (ta + 2*middle.length + 2 + tb)
    (C.init input)).stk _ = _
  rw [hd, BitMachine.run_add, BitMachine.run_halted C _ hhalt]
  exact hword

#print axioms retained_left
#print axioms retained_left_at_bound

end CurrentAdditive.GaussCompositionRetained
