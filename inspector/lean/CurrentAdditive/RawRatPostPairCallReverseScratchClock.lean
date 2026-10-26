import CurrentAdditive.RawRatPostPairCallReverseScratch
import CurrentAdditive.RawRatPostMachinePairClock

namespace CurrentAdditive.RawRatPostPairCallReverseScratch

open EthInapproximability.CurrentPaper

def pairResult (M : BitMachine.Machine) (s : Fin M.stackCount)
    (f : List Bool → List Bool) (c d : Nat) (input : List Bool) :
    List Bool :=
  RawRatPairAssembler.pairWord
    ((M.run (c*(input.length+1)^d) (M.init input)).stk s) (f input)

theorem paired_computes_polynomial (M : BitMachine.Machine)
    (s : Fin M.stackCount) (hs : s ≠ M.output)
    (f : List Bool → List Bool) (c d : Nat)
    (hM : M.ComputesWithin f (fun n => c*(n+1)^d)) :
    (pairedMachine M s hs).ComputesWithin (pairResult M s f c d)
      (fun n => (13+c*(12*M.pushBound+1))*(n+1)^(d+1)) := by
  intro input
  let T := c*(input.length+1)^d
  let saved := (M.run T (M.init input)).stk s
  apply BitMachine.outputsWithin_mono (pairedMachine M s hs)
    (paired_outputs M s hs input (f input) saved T (hM input) rfl)
  have hq := BitMachine.output_length_bound M (hM input)
  change (f input).length ≤ input.length + T*M.pushBound at hq
  have hsave := RawRatPostMachinePair.saved_length_bound M s input T
  have hfirst : T + 6*((f input).length+saved.length+2)+1 ≤
      T + 6*(2*(input.length+T*M.pushBound)+2)+1 := by
    dsimp [saved]
    omega
  exact hfirst.trans (RawRatPostMachinePair.input_clock_polynomial
    input.length c d M.pushBound)

theorem postPair_then_call_computes_polynomial
    (M N : BitMachine.Machine)
    (s : Fin M.stackCount) (hs : s ≠ M.output)
    (f g : List Bool → List Bool) (c d e k : Nat)
    (hM : M.ComputesWithin f (fun n => c*(n+1)^d))
    (hN : N.ComputesWithin g (fun n => e*(n+1)^k)) :
    (postPair_then_call M N s hs).ComputesWithin
      (g ∘ pairResult M s f c d)
      (fun n =>
        let cf := 13+c*(12*M.pushBound+1)
        (cf + 2*(cf*(pairedMachine M s hs).pushBound+1) +
          e*(cf*(pairedMachine M s hs).pushBound+1)^k) *
            (n+1)^((d+2)*(k+1))) := by
  let A := pairedMachine M s hs
  let hA := paired_computes_polynomial M s hs f c d hM
  intro input
  let w := pairResult M s f c d input
  let cf := 13+c*(12*M.pushBound+1)
  have hcomp := BitMachineComposition.composition_outputsWithin A N
    (hA input) (hN w)
  apply BitMachine.outputsWithin_mono (postPair_then_call M N s hs) hcomp
  have hlen := BitMachine.output_length_bound A (hA input)
  exact BitMachineCompositionArithmetic.composition_time_bound
    input.length cf (d+1) e k A.pushBound w.length hlen

#print axioms paired_computes_polynomial
#print axioms postPair_then_call_computes_polynomial

end CurrentAdditive.RawRatPostPairCallReverseScratch
