import CurrentAdditive.RawRatPostPairCallScratch
import CurrentAdditive.GaussCompositionRetained

namespace CurrentAdditive.RawRatPostPairCallScratch

open EthInapproximability.CurrentPaper
open RawRatPostMachinePair

theorem postPair_then_call_other_at_bound
    (M N : BitMachine.Machine)
    (s : Fin M.stackCount) (hs : s ≠ M.output)
    (input q saved result : List Bool) (T U : Nat)
    (hM : M.OutputsWithin input q T)
    (hsv : (M.run T (M.init input)).stk s = saved)
    (hN : N.OutputsWithin
      (RawRatPairAssembler.pairWord q saved) result U)
    (j : Fin M.stackCount) (hjo : j ≠ M.output) (hjs : j ≠ s) :
    ((postPair_then_call M N s hs).run
      (T + 6*(q.length+saved.length+2)+1 +
        2*(RawRatPairAssembler.pairWord q saved).length+2+U)
      ((postPair_then_call M N s hs).init input)).stk
      (Fintype.equivFin
        (BitMachineComposition.Stack (pairedMachine M s hs) N)
        (.inl (Fintype.equivFin (Stack M) (.inl j)))) =
      (M.run T (M.init input)).stk j := by
  let A := pairedMachine M s hs
  let k := Fintype.equivFin (Stack M) (.inl j)
  have hk : k ≠ A.output := by
    change Fintype.equivFin (Stack M) (.inl j) ≠
      Fintype.equivFin (Stack M) (.inr 4)
    intro heq
    cases (Fintype.equivFin (Stack M)).injective heq
  have ha := paired_outputs M s hs input q saved T hM hsv
  have hret := CurrentAdditive.GaussCompositionRetained.retained_left_at_bound
    A N ha hN k hk
  have hsrc := paired_other_at_bound M s hs input q saved T
    hM hsv j hjo hjs
  exact hret.trans hsrc

#print axioms postPair_then_call_other_at_bound

end CurrentAdditive.RawRatPostPairCallScratch
