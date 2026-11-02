import EthInapproximability.CurrentPaper.SamplerWriterSecondCopy
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-!
# One fixed reset-and-copy sequence between exact sampler calls

From a bank retaining the second raw degree word and row length in the two
extra stacks, this program clears the first call's persistent modulus/length,
copies the second values into the sampler's actual cells, and copies scalar
`a` into the reversal-width cell. It is a single finite program with charged
transitions. It never writes the first-family or source payload cells.
-/

namespace EthInapproximability.CurrentPaper.SamplerWriterSecondSequence

open Turing BitMachineEncoding
open SamplerWriterSecondInit SamplerWriterSecondCopy

abbrev Stack := SamplerWriterSecondInit.Stack
abbrev CopyLabel := BitMachineCopy.Label
abbrev CopyControl := Option Bool
abbrev ClearLabel := SamplerWriterSecondInit.Label
abbrev ClearControl := SamplerWriterSecondInit.Control

abbrev PairLabel := BitMachineRawSequence.Label ClearLabel CopyLabel
abbrev PairControl := BitMachineRawSequence.Control ClearControl CopyControl
abbrev TripleLabel := BitMachineRawSequence.Label PairLabel CopyLabel
abbrev TripleControl := BitMachineRawSequence.Control PairControl CopyControl
abbrev Label := BitMachineRawSequence.Label TripleLabel CopyLabel
abbrev Control := BitMachineRawSequence.Control TripleControl CopyControl

def pairProgram : PairLabel → TM2.Stmt (fun _ : Stack => Bool) PairLabel PairControl :=
  BitMachineRawSequence.program SamplerWriterSecondInit.program
    (SamplerWriterSecondCopy.program degreeSlots) .scan ((), none) none

def tripleProgram : TripleLabel → TM2.Stmt (fun _ : Stack => Bool)
    TripleLabel TripleControl :=
  BitMachineRawSequence.program pairProgram
    (SamplerWriterSecondCopy.program lengthSlots) .scan (((), none), none) none

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  BitMachineRawSequence.program tripleProgram
    (SamplerWriterSecondCopy.program widthSlots) .scan ((((), none), none), none) none

def afterClear (S : Stack → List Bool) : Stack → List Bool :=
  BitMachineClearBank.cleared SamplerWriterSecondInit.clearing S

def afterDegree (S : Stack → List Bool) (degree : List Bool) : Stack → List Bool :=
  Function.update (afterClear S) SamplerWriterSecondInit.degreeCell degree

def afterLength (S : Stack → List Bool) (degree length : List Bool) : Stack → List Bool :=
  Function.update (afterDegree S degree) SamplerWriterSecondInit.lengthCell length

def finalBank (S : Stack → List Bool) (degree length width : List Bool) :
    Stack → List Bool :=
  Function.update (afterLength S degree length)
    (.inl SamplerWriterPayloadFrame.reverseWidthCell) width

private theorem clear_foreign (S : Stack → List Bool) (j : Stack)
    (hd : j ≠ SamplerWriterSecondInit.degreeCell)
    (hl : j ≠ SamplerWriterSecondInit.lengthCell) :
    afterClear S j = S j := by
  apply BitMachineClearBank.cleared_foreign
  intro i
  fin_cases i
  · exact Ne.symm hd
  · exact Ne.symm hl

theorem run_sequence (S : Stack → List Bool)
    (degree length width : List Bool)
    (hd : S SamplerWriterSecondInit.nextDegree = degree)
    (hl : S SamplerWriterSecondInit.nextLength = length)
    (hw : S (.inl (.inl (.inl (.inl 24)))) = width)
    (h37 : S (.inl (.inl (.inl (.inl 37)))) = [])
    (h38 : S (.inl (.inl (.inl (.inl 38)))) = [])
    (h39 : S (.inl (.inl (.inl (.inl 39)))) = [])
    (h32 : S (.inl SamplerWriterPayloadFrame.reverseWidthCell) = []) :
    ∃ t ≤ (S SamplerWriterSecondInit.degreeCell).length +
        (S SamplerWriterSecondInit.lengthCell).length + 4 +
        (2 * degree.length + 2) + (2 * length.length + 2) +
        (2 * width.length + 2) + 3,
      ((advance program)^[t])
        (⟨some (.inl (.inl (.inl 0))),
          (((((), none), none), none), none), S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) Label Control) =
        ⟨none, (((((), none), none), none), none), finalBank S degree length width⟩ := by
  let S₀ := afterClear S
  let S₁ := afterDegree S degree
  let S₂ := afterLength S degree length
  let S₃ := finalBank S degree length width
  have hclear := SamplerWriterSecondInit.run_halt S
  have hd0 : S₀ (degreeSlots 0) = degree := by
    simpa [S₀, degreeSlots] using (clear_foreign S _ (by decide) (by decide)).trans hd
  have hd1 : S₀ (degreeSlots 1) = [] := by
    exact SamplerWriterSecondInit.cleared_degree S
  have hd2 : S₀ (degreeSlots 2) = [] := by
    simpa [S₀, degreeSlots] using (clear_foreign S _ (by decide) (by decide)).trans h37
  obtain ⟨td, htd, hrd⟩ := copy_run degreeSlots S₀ degree hd0 hd1 hd2
  have hl0 : S₁ (lengthSlots 0) = length := by
    simpa [S₁, afterDegree, lengthSlots, Function.update_of_ne (by decide :
      SamplerWriterSecondInit.nextLength ≠ SamplerWriterSecondInit.degreeCell)]
      using (clear_foreign S _ (by decide) (by decide)).trans hl
  have hl1 : S₁ (lengthSlots 1) = [] := by
    simpa [S₁, afterDegree, lengthSlots,
      Function.update_of_ne (by decide :
        SamplerWriterSecondInit.lengthCell ≠ SamplerWriterSecondInit.degreeCell)]
      using SamplerWriterSecondInit.cleared_length S
  have hl2 : S₁ (lengthSlots 2) = [] := by
    simpa [S₁, afterDegree, lengthSlots,
      Function.update_of_ne (by decide :
        (.inl (.inl (.inl (.inl 38))) : Stack) ≠ SamplerWriterSecondInit.degreeCell)]
      using (clear_foreign S _ (by decide) (by decide)).trans h38
  obtain ⟨tl, htl, hrl⟩ := copy_run lengthSlots S₁ length hl0 hl1 hl2
  have hw0 : S₂ (widthSlots 0) = width := by
    simpa [S₂, afterLength, afterDegree, widthSlots,
      Function.update_of_ne (by decide :
        (.inl (.inl (.inl (.inl 24))) : Stack) ≠ SamplerWriterSecondInit.lengthCell),
      Function.update_of_ne (by decide :
        (.inl (.inl (.inl (.inl 24))) : Stack) ≠ SamplerWriterSecondInit.degreeCell)]
      using (clear_foreign S _ (by decide) (by decide)).trans hw
  have hw1 : S₂ (widthSlots 1) = [] := by
    simpa [S₂, afterLength, afterDegree, widthSlots,
      Function.update_of_ne (by decide :
        (.inl SamplerWriterPayloadFrame.reverseWidthCell : Stack) ≠
          SamplerWriterSecondInit.lengthCell),
      Function.update_of_ne (by decide :
        (.inl SamplerWriterPayloadFrame.reverseWidthCell : Stack) ≠
          SamplerWriterSecondInit.degreeCell)]
      using (clear_foreign S _ (by decide) (by decide)).trans h32
  have hw2 : S₂ (widthSlots 2) = [] := by
    simpa [S₂, afterLength, afterDegree, widthSlots,
      Function.update_of_ne (by decide :
        (.inl (.inl (.inl (.inl 39))) : Stack) ≠ SamplerWriterSecondInit.lengthCell),
      Function.update_of_ne (by decide :
        (.inl (.inl (.inl (.inl 39))) : Stack) ≠ SamplerWriterSecondInit.degreeCell)]
      using (clear_foreign S _ (by decide) (by decide)).trans h39
  obtain ⟨tw, htw, hrw⟩ := copy_run widthSlots S₂ width hw0 hw1 hw2
  have hp := BitMachineRawSequence.runs
    SamplerWriterSecondInit.program (SamplerWriterSecondCopy.program degreeSlots)
    0 .scan ((), none) ((), none) none none S S₀ S₁
    ((S SamplerWriterSecondInit.degreeCell).length +
      (S SamplerWriterSecondInit.lengthCell).length + 4) td hclear hrd
  obtain ⟨tp, htp, hrp⟩ := hp
  have ht := BitMachineRawSequence.runs pairProgram
    (SamplerWriterSecondCopy.program lengthSlots)
    (.inl 0) .scan (((), none), none) (((), none), none) none none
    S S₁ S₂ tp tl hrp hrl
  obtain ⟨tt, htt, hrt⟩ := ht
  have hq := BitMachineRawSequence.runs tripleProgram
    (SamplerWriterSecondCopy.program widthSlots)
    (.inl (.inl 0)) .scan ((((), none), none), none)
    ((((), none), none), none) none none S S₂ S₃ tt tw hrt hrw
  obtain ⟨t, htime, hr⟩ := hq
  refine ⟨t, ?_, ?_⟩
  · omega
  · exact hr

end EthInapproximability.CurrentPaper.SamplerWriterSecondSequence
