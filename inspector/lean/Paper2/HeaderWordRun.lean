import Paper2.FixedGapHeader
import Paper2.PairConcat
import Paper2.AFrontSplit
import Paper2.A4KofLoops
import Paper2.A4PairMap
import EthInapproximability.CurrentPaper.BitMachineComposition

/-!
# Physical fixed-gap header for a canonical encoded instance

This module starts with the actual four-field `encodeInstance` word. A fixed
split machine recovers its matrix and budget fields; a fixed swap machine
places the budget bits first; a physical pair-map computes the fixed-gap
header; and a fixed transducer concatenates the header and matrix word.
The theorem below charges every machine and intermediate-word transfer. It
does not claim that an unconstructed source sampler prints this input.
-/

noncomputable section

namespace Paper2.HeaderWordRun

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication

def headerMachine (k : ℕ) : BitMachine.Machine :=
  Classical.choose (FixedGapHeader.bitsHeader_polytime k)

def headerC (k : ℕ) : ℕ :=
  Classical.choose (Classical.choose_spec (FixedGapHeader.bitsHeader_polytime k))

def headerD (k : ℕ) : ℕ :=
  Classical.choose (Classical.choose_spec
    (Classical.choose_spec (FixedGapHeader.bitsHeader_polytime k)))

theorem headerRun (k : ℕ) (q : List Bool) :
    (headerMachine k).OutputsWithin q (FixedGapHeader.bitsHeader k q)
      (headerC k * (q.length + 1) ^ headerD k) :=
  Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (FixedGapHeader.bitsHeader_polytime k))) q

abbrev matrix (i : Instance) : List Bool :=
  AFront.Projection.matrixWord i.rows i.cols i.table

def splitWord (i : Instance) : List Bool :=
  EncodedComplexity.pair (matrix i) (natField i.threshold)

def swappedWord (i : Instance) : List Bool :=
  EncodedComplexity.pair i.threshold.bits (EncodedComplexity.pair (matrix i) [])

def mappedWord (k : ℕ) (i : Instance) : List Bool :=
  EncodedComplexity.pair (FixedGapHeader.bitsHeader k i.threshold.bits)
    (EncodedComplexity.pair (matrix i) [])

def headeredWord (k : ℕ) (i : Instance) : List Bool :=
  natField (2 * i.threshold + k) ++ matrix i

def machine (k : ℕ) : BitMachine.Machine :=
  BitMachineComposition.composition AFront.Split.splitMachine
    (BitMachineComposition.composition Paper2.Unit4Shell.KofLoops.Swap.machine
      (BitMachineComposition.composition
        (Paper2.Unit4Shell.PairMap.machine (headerMachine k)) PairConcat.machine))

def splitClock (i : Instance) : ℕ := 3 * ((encodeInstance i).length + 1)
def swapClock (i : Instance) : ℕ := 3 * ((splitWord i).length + 1)
def mapClock (k : ℕ) (i : Instance) : ℕ :=
  2 * i.threshold.bits.length +
    headerC k * (i.threshold.bits.length + 1) ^ headerD k +
    2 * (FixedGapHeader.bitsHeader k i.threshold.bits).length + 6
def concatClock (k : ℕ) (i : Instance) : ℕ :=
  3 * ((mappedWord k i).length + 1)

def clock (k : ℕ) (i : Instance) : ℕ :=
  splitClock i + 2 * (splitWord i).length + 2 +
    (swapClock i + 2 * (swappedWord i).length + 2 +
      (mapClock k i + 2 * (mappedWord k i).length + 2 +
        concatClock k i))

theorem splitRun (i : Instance) :
    AFront.Split.splitMachine.OutputsWithin (encodeInstance i)
      (splitWord i) (splitClock i) :=
  AFront.Split.splitMachine_encodeInstance i

theorem swapRun (i : Instance) :
    Paper2.Unit4Shell.KofLoops.Swap.machine.OutputsWithin
      (splitWord i) (swappedWord i) (swapClock i) := by
  simpa [splitWord, swappedWord, swapClock, matrix, natField,
    EncodedComplexity.pair, List.append_assoc] using
    Paper2.Unit4Shell.KofLoops.Swap.machine_outputs
      (matrix i) i.threshold.bits ([] : List Bool)

theorem mapRun (k : ℕ) (i : Instance) :
    (Paper2.Unit4Shell.PairMap.machine (headerMachine k)).OutputsWithin
      (swappedWord i) (mappedWord k i) (mapClock k i) := by
  exact Paper2.Unit4Shell.PairMap.machine_outputs
    (M := headerMachine k)
    i.threshold.bits (FixedGapHeader.bitsHeader k i.threshold.bits)
    (EncodedComplexity.pair (matrix i) [])
    (headerC k * (i.threshold.bits.length + 1) ^ headerD k)
    (headerRun k i.threshold.bits)

theorem concatRun (k : ℕ) (i : Instance) (hk : 0 < k) :
    PairConcat.machine.OutputsWithin (mappedWord k i)
      (headeredWord k i) (concatClock k i) := by
  have h := PairConcat.outputs (mappedWord k i)
  rw [show PairConcat.concat (mappedWord k i) = headeredWord k i by
    simpa [mappedWord, headeredWord, FixedGapHeader.bitsHeader_nat k i.threshold hk]
      using PairConcat.concat_pair
        (FixedGapHeader.bitsHeader k i.threshold.bits) (matrix i)] at h
  exact h

theorem machine_outputs (k : ℕ) (i : Instance) (hk : 0 < k) :
    (machine k).OutputsWithin (encodeInstance i)
      (headeredWord k i) (clock k i) := by
  let h34 := BitMachineComposition.composition_outputsWithin
    (A := Paper2.Unit4Shell.PairMap.machine (headerMachine k))
    (B := PairConcat.machine)
    (mapRun k i) (concatRun k i hk)
  let h234 := BitMachineComposition.composition_outputsWithin
    (A := Paper2.Unit4Shell.KofLoops.Swap.machine)
    (B := BitMachineComposition.composition
      (Paper2.Unit4Shell.PairMap.machine (headerMachine k)) PairConcat.machine)
    (swapRun i) h34
  let h123 := BitMachineComposition.composition_outputsWithin
    (A := AFront.Split.splitMachine)
    (B := BitMachineComposition.composition Paper2.Unit4Shell.KofLoops.Swap.machine
      (BitMachineComposition.composition
        (Paper2.Unit4Shell.PairMap.machine (headerMachine k)) PairConcat.machine))
    (splitRun i) h234
  exact h123

#print axioms machine_outputs

end Paper2.HeaderWordRun
