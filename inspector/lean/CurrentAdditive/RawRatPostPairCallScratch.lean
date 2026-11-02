import CurrentAdditive.RawRatPostMachinePairClock
import EthInapproximability.CurrentPaper.BitMachineComposition

namespace CurrentAdditive.RawRatPostPairCallScratch

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open RawRatPostMachinePair

noncomputable def pairedMachine (M : BitMachine.Machine)
    (s : Fin M.stackCount) (hs : s ≠ M.output) : BitMachine.Machine :=
  BitMachineEncoding.ofFinite (.inl M.input : Stack M) (.inr 4)
    (BitMachineRawSequence.leftLabel M.start)
    (M.initial,asmInitial) (program M s hs)

theorem initial_eq_raw (M : BitMachine.Machine) (input : List Bool) :
    BitMachineEncoding.rawInit (.inl M.input : Stack M)
      (BitMachineRawSequence.leftLabel (LB := AsmLabel) M.start)
      (M.initial,asmInitial) input =
    ⟨some (BitMachineRawSequence.leftLabel (LB := AsmLabel) M.start),
      (M.initial,asmInitial), initialBank M input⟩ := by
  unfold BitMachineEncoding.rawInit initialBank
  congr 1
  funext k
  cases k with
  | inl k => simp [BitMachine.Machine.init]
  | inr k => simp

theorem paired_outputs (M : BitMachine.Machine)
    (s : Fin M.stackCount) (hs : s ≠ M.output)
    (input q saved : List Bool) (T : Nat)
    (hM : M.OutputsWithin input q T)
    (hsv : (M.run T (M.init input)).stk s = saved) :
    (pairedMachine M s hs).OutputsWithin input
      (RawRatPairAssembler.pairWord q saved)
      (T + 6*(q.length+saved.length+2)+1) := by
  obtain ⟨t,ht,hr⟩ := post_outputs M s hs input q saved T hM hsv
  apply BitMachineEncoding.outputsWithin_of_raw_run
    (.inl M.input : Stack M) (.inr 4)
    (BitMachineRawSequence.leftLabel M.start)
    (M.initial,asmInitial) (program M s hs)
    input (RawRatPairAssembler.pairWord q saved) t
    (T + 6*(q.length+saved.length+2)+1) ht
  · rw [initial_eq_raw]
    exact hr.1
  · rw [initial_eq_raw]
    exact hr.2.1

theorem paired_other_at_bound (M : BitMachine.Machine)
    (s : Fin M.stackCount) (hs : s ≠ M.output)
    (input q saved : List Bool) (T : Nat)
    (hM : M.OutputsWithin input q T)
    (hsv : (M.run T (M.init input)).stk s = saved)
    (j : Fin M.stackCount) (hjo : j ≠ M.output) (hjs : j ≠ s) :
    ((pairedMachine M s hs).run
      (T + 6*(q.length+saved.length+2)+1)
      ((pairedMachine M s hs).init input)).stk
      (Fintype.equivFin (Stack M) (.inl j)) =
      (M.run T (M.init input)).stk j := by
  obtain ⟨t,ht,S',hr⟩ := post_run M s hs input q saved T hM hsv
  let P := pairedMachine M s hs
  have hi := BitMachineEncoding.ofFinite_init
    (.inl M.input : Stack M) (.inr 4)
    (BitMachineRawSequence.leftLabel M.start)
    (M.initial,asmInitial) (program M s hs) input
  rw [initial_eq_raw] at hi
  have hraw := BitMachineEncoding.ofFinite_run
    (.inl M.input : Stack M) (.inr 4)
    (BitMachineRawSequence.leftLabel M.start)
    (M.initial,asmInitial) (program M s hs)
    (BitMachineEncoding.rawInit (.inl M.input : Stack M)
      (BitMachineRawSequence.leftLabel M.start) (M.initial,asmInitial) input) t
  rw [initial_eq_raw, hr] at hraw
  have hrun : P.run t (P.init input) =
      BitMachineEncoding.renameCfg
        (Fintype.equivFin (Stack M))
        (Fintype.equivFin (BitMachineRawSequence.Label
          (Fin M.labelCount) AsmLabel))
        (Fintype.equivFin (Fin M.controlCount × AsmControl))
        ⟨none,(M.initial,asmInitial),
          finalBank M s hs input T q saved S'⟩ := by
    exact (congrArg (P.run t) hi).trans hraw
  have hhalt : (P.run t (P.init input)).l = none := by
    rw [hrun]
    rfl
  obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le ht
  rw [hd, BitMachine.run_add, BitMachine.run_halted P _ hhalt, hrun]
  simpa only [BitMachineEncoding.renameCfg, Equiv.symm_apply_apply] using
    final_other M s hs input T q saved S' j hjo hjs

noncomputable def postPair_then_call (M N : BitMachine.Machine)
    (s : Fin M.stackCount) (hs : s ≠ M.output) : BitMachine.Machine :=
  BitMachineComposition.composition (pairedMachine M s hs) N

theorem postPair_then_call_outputs (M N : BitMachine.Machine)
    (s : Fin M.stackCount) (hs : s ≠ M.output)
    (input q saved result : List Bool) (T U : Nat)
    (hM : M.OutputsWithin input q T)
    (hsv : (M.run T (M.init input)).stk s = saved)
    (hN : N.OutputsWithin
      (RawRatPairAssembler.pairWord q saved) result U) :
    (postPair_then_call M N s hs).OutputsWithin input result
      (T + 6*(q.length+saved.length+2)+1 +
        2*(RawRatPairAssembler.pairWord q saved).length+2+U) := by
  exact BitMachineComposition.composition_outputsWithin
    (pairedMachine M s hs) N (paired_outputs M s hs input q saved T hM hsv) hN

#print axioms paired_other_at_bound
#print axioms postPair_then_call_outputs

end CurrentAdditive.RawRatPostPairCallScratch
