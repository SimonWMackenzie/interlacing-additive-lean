import CurrentAdditive.DeterministicETHPhysicalFixedBackend
import EthInapproximability.CurrentPaper.SourceFieldWriter

/-! One fixed back end for a dynamically chosen midpoint. The rectangle's
public threshold is already the integer numerator `2*budget+k`; its binary
payload is physically framed by `SourceFieldWriter`, so this machine does not
depend on the input formula or the iteration count. -/

namespace CurrentAdditive.DeterministicETHPhysicalDynamicBackend

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open CurrentAdditive.DeterministicETHComparator
open CurrentAdditive.DeterministicETHPhysicalFixedBackend

noncomputable def machine (Me : BitMachine.Machine) : BitMachine.Machine :=
  BitMachineComposition.composition Paper2.ASquare.Post.squareMachine
    (BitMachineComposition.composition AFront.Split.splitMachine
      (BitMachineComposition.composition (Paper2.Unit4Shell.PairMap.machine Me)
        (BitMachineComposition.composition Paper2.Unit4Shell.KofLoops.Swap.machine
          (BitMachineComposition.composition
            (Paper2.Unit4Shell.PairMap.machine SourceFieldWriter.fieldMachine)
            (BitMachineComposition.composition
              CurrentAdditive.DeterministicETHPairUnframe.machine
              Paper2.CmpOwner.machine)))))

noncomputable def clock (i : EncodedCommunication.Instance)
    (out : List Bool) (Te : ℕ) : ℕ :=
  let s := CurrentAdditive.DeterministicETHPhysicalFixedBackend.square i
  let x := CurrentAdditive.DeterministicETHPhysicalFixedBackend.matrix s
  let h := natField i.threshold
  let w1 := encodeInstance s
  let w2 := EncodedComplexity.pair x (natField i.threshold)
  let w3 := EncodedComplexity.pair out (natField i.threshold)
  let w4 := EncodedComplexity.pair i.threshold.bits (EncodedComplexity.pair out [])
  let w5 := EncodedComplexity.pair h (EncodedComplexity.pair out [])
  let w6 := EncodedComplexity.pair h out
  Paper2.ASquare.Post.fullBound i.rows i.cols i.threshold + 2*w1.length+2 +
    (3*(w1.length+1) + 2*w2.length+2 +
      (2*x.length+Te+2*out.length+6 + 2*w3.length+2 +
        (3*(w3.length+1) + 2*w4.length+2 +
          (2*i.threshold.bits.length + (4*i.threshold.bits.length+4) +
            2*h.length+6 + 2*w5.length+2 +
            (3*(w5.length+1) + 2*w6.length+2 +
              Paper2.CmpOwner.cmpTime h.length out.length)))))

theorem machine_outputs (Me : BitMachine.Machine)
    (i : EncodedCommunication.Instance) (hi : i.Valid)
    (out : List Bool) (Te : ℕ)
    (hMe : Me.OutputsWithin
      (CurrentAdditive.DeterministicETHPhysicalFixedBackend.matrix
        (CurrentAdditive.DeterministicETHPhysicalFixedBackend.square i)) out Te)
    (z : ℝ) (hz : Paper2.AModel.decodeDyadic out = some z) :
    (machine Me).OutputsWithin (encodeInstance i)
      [decide (z < (i.threshold:ℝ)/2)]
      (clock i out Te) := by
  let s := CurrentAdditive.DeterministicETHPhysicalFixedBackend.square i
  let x := CurrentAdditive.DeterministicETHPhysicalFixedBackend.matrix s
  let h := natField i.threshold
  have hSq : Paper2.ASquare.Post.squareMachine.OutputsWithin
      (encodeInstance i) (encodeInstance s)
      (Paper2.ASquare.Post.fullBound i.rows i.cols i.threshold) := by
    simpa only [s, CurrentAdditive.DeterministicETHPhysicalFixedBackend.square] using
      Paper2.ASquare.Post.full_outputs i hi
  have hSplit : AFront.Split.splitMachine.OutputsWithin
      (encodeInstance s) (EncodedComplexity.pair x (natField i.threshold))
      (3*((encodeInstance s).length+1)) := by
    simpa only [s, CurrentAdditive.DeterministicETHPhysicalFixedBackend.square,
      x, CurrentAdditive.DeterministicETHPhysicalFixedBackend.matrix] using
      AFront.Split.splitMachine_encodeInstance s
  have hEst : (Paper2.Unit4Shell.PairMap.machine Me).OutputsWithin
      (EncodedComplexity.pair x (natField i.threshold))
      (EncodedComplexity.pair out (natField i.threshold))
      (2*x.length+Te+2*out.length+6) :=
    Paper2.Unit4Shell.PairMap.machine_outputs Me x out (natField i.threshold) Te hMe
  have hSwap : Paper2.Unit4Shell.KofLoops.Swap.machine.OutputsWithin
      (EncodedComplexity.pair out (natField i.threshold))
      (EncodedComplexity.pair i.threshold.bits (EncodedComplexity.pair out []))
      (3*((EncodedComplexity.pair out (natField i.threshold)).length+1)) := by
    simpa [natField, EncodedComplexity.pair, List.append_assoc] using
      Paper2.Unit4Shell.KofLoops.Swap.machine_outputs out i.threshold.bits []
  have hHeader :
      (Paper2.Unit4Shell.PairMap.machine SourceFieldWriter.fieldMachine).OutputsWithin
        (EncodedComplexity.pair i.threshold.bits (EncodedComplexity.pair out []))
        (EncodedComplexity.pair h (EncodedComplexity.pair out []))
        (2*i.threshold.bits.length + (4*i.threshold.bits.length+4) +
          2*h.length+6) := by
    simpa only [h, natField] using
      Paper2.Unit4Shell.PairMap.machine_outputs SourceFieldWriter.fieldMachine
        i.threshold.bits (field i.threshold.bits)
        (EncodedComplexity.pair out [])
        (4*i.threshold.bits.length+4)
        (SourceFieldWriter.field_outputs i.threshold.bits)
  have hUnframe : CurrentAdditive.DeterministicETHPairUnframe.machine.OutputsWithin
      (EncodedComplexity.pair h (EncodedComplexity.pair out []))
      (EncodedComplexity.pair h out)
      (3*((EncodedComplexity.pair h (EncodedComplexity.pair out [])).length+1)) :=
    CurrentAdditive.DeterministicETHPairUnframe.outputs_pair h out []
  have hCmp : Paper2.CmpOwner.machine.OutputsWithin
      (EncodedComplexity.pair h out)
      [decide (z < (i.threshold:ℝ)/2)]
      (Paper2.CmpOwner.cmpTime h.length out.length) := by
    simpa [h, midpointHeader] using comparator_run 0 i.threshold out z hz
  have h67 := BitMachineComposition.composition_outputsWithin
    CurrentAdditive.DeterministicETHPairUnframe.machine Paper2.CmpOwner.machine
    hUnframe hCmp
  have h567 := BitMachineComposition.composition_outputsWithin
    (Paper2.Unit4Shell.PairMap.machine SourceFieldWriter.fieldMachine)
    (BitMachineComposition.composition
      CurrentAdditive.DeterministicETHPairUnframe.machine Paper2.CmpOwner.machine)
    hHeader h67
  have h4567 := BitMachineComposition.composition_outputsWithin
    Paper2.Unit4Shell.KofLoops.Swap.machine
    (BitMachineComposition.composition
      (Paper2.Unit4Shell.PairMap.machine SourceFieldWriter.fieldMachine)
      (BitMachineComposition.composition
        CurrentAdditive.DeterministicETHPairUnframe.machine Paper2.CmpOwner.machine))
    hSwap h567
  have h34567 := BitMachineComposition.composition_outputsWithin
    (Paper2.Unit4Shell.PairMap.machine Me)
    (BitMachineComposition.composition Paper2.Unit4Shell.KofLoops.Swap.machine
      (BitMachineComposition.composition
        (Paper2.Unit4Shell.PairMap.machine SourceFieldWriter.fieldMachine)
        (BitMachineComposition.composition
          CurrentAdditive.DeterministicETHPairUnframe.machine Paper2.CmpOwner.machine)))
    hEst h4567
  have h234567 := BitMachineComposition.composition_outputsWithin
    AFront.Split.splitMachine
    (BitMachineComposition.composition (Paper2.Unit4Shell.PairMap.machine Me)
      (BitMachineComposition.composition Paper2.Unit4Shell.KofLoops.Swap.machine
        (BitMachineComposition.composition
          (Paper2.Unit4Shell.PairMap.machine SourceFieldWriter.fieldMachine)
          (BitMachineComposition.composition
            CurrentAdditive.DeterministicETHPairUnframe.machine Paper2.CmpOwner.machine))))
    hSplit h34567
  have hAll := BitMachineComposition.composition_outputsWithin
    Paper2.ASquare.Post.squareMachine
    (BitMachineComposition.composition AFront.Split.splitMachine
      (BitMachineComposition.composition (Paper2.Unit4Shell.PairMap.machine Me)
        (BitMachineComposition.composition Paper2.Unit4Shell.KofLoops.Swap.machine
          (BitMachineComposition.composition
            (Paper2.Unit4Shell.PairMap.machine SourceFieldWriter.fieldMachine)
            (BitMachineComposition.composition
              CurrentAdditive.DeterministicETHPairUnframe.machine Paper2.CmpOwner.machine)))))
    hSq h234567
  simpa only [machine, clock, s, x, h] using hAll

#print axioms machine_outputs

end CurrentAdditive.DeterministicETHPhysicalDynamicBackend
