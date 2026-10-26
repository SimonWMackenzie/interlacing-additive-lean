import CurrentAdditive.RawRatPostMachinePairReverseScratch
import EthInapproximability.CurrentPaper.BitMachineComposition

namespace CurrentAdditive.RawRatPostPairCallReverseScratch

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open RawRatPostMachinePairReverseScratch

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
      (RawRatPairAssembler.pairWord saved q)
      (T + 6*(q.length+saved.length+2)+1) := by
  obtain ⟨t,ht,hr⟩ := post_outputs M s hs input q saved T hM hsv
  apply BitMachineEncoding.outputsWithin_of_raw_run
    (.inl M.input : Stack M) (.inr 4)
    (BitMachineRawSequence.leftLabel M.start)
    (M.initial,asmInitial) (program M s hs)
    input (RawRatPairAssembler.pairWord saved q) t
    (T + 6*(q.length+saved.length+2)+1) ht
  · rw [initial_eq_raw]
    exact hr.1
  · rw [initial_eq_raw]
    exact hr.2.1

noncomputable def postPair_then_call (M N : BitMachine.Machine)
    (s : Fin M.stackCount) (hs : s ≠ M.output) : BitMachine.Machine :=
  BitMachineComposition.composition (pairedMachine M s hs) N

theorem postPair_then_call_outputs (M N : BitMachine.Machine)
    (s : Fin M.stackCount) (hs : s ≠ M.output)
    (input q saved result : List Bool) (T U : Nat)
    (hM : M.OutputsWithin input q T)
    (hsv : (M.run T (M.init input)).stk s = saved)
    (hN : N.OutputsWithin
      (RawRatPairAssembler.pairWord saved q) result U) :
    (postPair_then_call M N s hs).OutputsWithin input result
      (T + 6*(q.length+saved.length+2)+1 +
        2*(RawRatPairAssembler.pairWord saved q).length+2+U) := by
  exact BitMachineComposition.composition_outputsWithin
    (pairedMachine M s hs) N (paired_outputs M s hs input q saved T hM hsv) hN

#print axioms postPair_then_call_outputs

end CurrentAdditive.RawRatPostPairCallReverseScratch
