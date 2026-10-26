import CurrentAdditive.GaussCellQuotient

set_option maxRecDepth 4096

namespace CurrentAdditive.GaussBranchBankAtBound

open EthInapproximability.CurrentPaper
open BitMachine BitMachineEncoding
open CurrentAdditive.CodeDCodec

open CurrentAdditive.GaussPhysical.GaussBranchSelect

private def branchTime (flag : Bool)
    (current column row pivot : RawRat) : Nat :=
  35*((CurrentAdditive.GaussPhysical.cellPacket
    flag current column row pivot).length+1)

noncomputable def wordIndex (j : Fin 12) :
    Fin machine.stackCount :=
  Fintype.equivFin Stack (.inl j)

theorem runAtRaw (input : List Bool) (t : Nat) :
    machine.run t (machine.init input) =
      renameCfg (Fintype.equivFin Stack)
        (Fintype.equivFin Label) (Fintype.equivFin Control)
        (run t (cfg (some (.inl (.scan 0))) none
          (fun _ => []) input [] [])) := by
  have hi := ofFinite_init
    (.inr 0 : Stack) (.inr 2 : Stack)
    (.inl (.scan 0) : Label) (none : Control) program input
  have hr := ofFinite_run
    (.inr 0 : Stack) (.inr 2 : Stack)
    (.inl (.scan 0) : Label) (none : Control) program
    (rawInit (.inr 0 : Stack) (.inl (.scan 0) : Label)
      (none : Control) input) t
  rw [show machine.init input = _ from hi]
  simpa only [machine, initial_cfg, run] using hr

theorem current_at_bound (flag : Bool)
    (current column row pivot : RawRat) :
    (machine.run (branchTime flag current column row pivot)
      (machine.init
        (CurrentAdditive.GaussPhysical.cellPacket
          flag current column row pivot))).stk
      (wordIndex 1) = encodeRawRat current := by
  let input := CurrentAdditive.GaussPhysical.cellPacket
    flag current column row pivot
  obtain ⟨t,ht,hh,_,hcurrent,_⟩ :=
    cellPacket_retains_context flag current column row pivot
  have hhalt : (machine.run t (machine.init input)).l = none := by
    rw [runAtRaw]
    simpa only [renameCfg, Option.map_none] using
      congrArg (Option.map (Fintype.equivFin Label)) hh
  obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le ht
  change (machine.run (branchTime flag current column row pivot)
    (machine.init input)).stk (wordIndex 1) = _
  simp only [branchTime]
  rw [hd, BitMachine.run_add,
    BitMachine.run_halted machine _ hhalt, runAtRaw]
  simpa only [wordIndex, renameCfg,
    Equiv.symm_apply_apply] using hcurrent

theorem row_at_bound_false
    (current column row pivot : RawRat) :
    (machine.run (branchTime false current column row pivot)
      (machine.init
        (CurrentAdditive.GaussPhysical.cellPacket
          false current column row pivot))).stk
      (wordIndex 3) = encodeRawRat row := by
  let input := CurrentAdditive.GaussPhysical.cellPacket
    false current column row pivot
  obtain ⟨t,ht,hh,_,_,hrow⟩ :=
    cellPacket_retains_context false current column row pivot
  have hhalt : (machine.run t (machine.init input)).l = none := by
    rw [runAtRaw]
    simpa only [renameCfg, Option.map_none] using
      congrArg (Option.map (Fintype.equivFin Label)) hh
  obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le ht
  change (machine.run (branchTime false current column row pivot)
    (machine.init input)).stk (wordIndex 3) = _
  simp only [branchTime]
  rw [hd, BitMachine.run_add,
    BitMachine.run_halted machine _ hhalt, runAtRaw]
  simpa only [wordIndex, renameCfg,
    Equiv.symm_apply_apply] using hrow

#print axioms runAtRaw
#print axioms current_at_bound
#print axioms row_at_bound_false

end CurrentAdditive.GaussBranchBankAtBound
