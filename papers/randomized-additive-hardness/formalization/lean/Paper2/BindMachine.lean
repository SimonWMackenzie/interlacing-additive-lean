import Paper2.BindSplit
import Paper2.BindLaw
import Paper2.A4PairMap
import Paper2.NPTruncRun
import EthInapproximability.CurrentPaper.BitMachineComposition

/-!
# Physical two-stage selected-tape composition

On one exact outer tape, the retain-splitter frames A's prescribed first
block while carrying every remaining bit unchanged; pair-map executes A on
that framed first block; the ordinary truncation machine cuts the retained
suffix to B's prescribed length for A's actual output; B then runs on its
exact selected pair. All three transfer reversals are charged below.
-/

noncomputable section

namespace Paper2.SelectedTape.Bind

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedComplexity

def prefixFn (t : List Bool) (r : ℕ) (h : r ≤ t.length) : Fin r → Bool :=
  fun i => (t.take r)[i.val]'(by rw [List.length_take, Nat.min_eq_left h]; exact i.isLt)

theorem ofFn_prefixFn (t : List Bool) (r : ℕ) (h : r ≤ t.length) :
    List.ofFn (prefixFn t r h) = t.take r := by
  apply List.ext_getElem
  · simp [h]
  · intro i hi hj
    simp [prefixFn]

def machine (A B : Algorithm) : BitMachine.Machine :=
  BitMachineComposition.composition (splitMachine A)
    (BitMachineComposition.composition
      (Paper2.Unit4Shell.PairMap.machine A.machine)
      (BitMachineComposition.composition
        (NPOwner1.Trunc.machine idMachine B.cR B.dR) B.machine))

def output (A B : Algorithm) (x outer : List Bool) : List Bool :=
  mixedOutput A B x
    (outer.take (A.tapeLength x)) (outer.drop (A.tapeLength x))

def firstWord (A : Algorithm) (x outer : List Bool) : List Bool :=
  outer.take (A.tapeLength x)
def restWord (A : Algorithm) (x outer : List Bool) : List Bool :=
  outer.drop (A.tapeLength x)
def sourceWord (A : Algorithm) (x outer : List Bool) : List Bool :=
  A.output x (firstWord A x outer)
def secondWord (A B : Algorithm) (x outer : List Bool) : List Bool :=
  (restWord A x outer).take (B.tapeLength (sourceWord A x outer))
def mid1 (A : Algorithm) (x outer : List Bool) : List Bool :=
  pair (pair x (firstWord A x outer)) (restWord A x outer)
def mid2 (A : Algorithm) (x outer : List Bool) : List Bool :=
  pair (sourceWord A x outer) (restWord A x outer)
def mid3 (A B : Algorithm) (x outer : List Bool) : List Bool :=
  pair (sourceWord A x outer) (secondWord A B x outer)

def stage2Clock (A : Algorithm) (x outer : List Bool) : ℕ :=
  2 * (pair x (firstWord A x outer)).length +
    A.cT * (x.length + 1) ^ A.dT +
    2 * (sourceWord A x outer).length + 6
def stage3Clock (A B : Algorithm) (x outer : List Bool) : ℕ :=
  NPOwner1.Trunc.timeBound B.cR B.dR idC idD idMachine.pushBound
    (mid2 A x outer).length
def stage4Clock (A B : Algorithm) (x outer : List Bool) : ℕ :=
  B.cT * ((sourceWord A x outer).length + 1) ^ B.dT

def clock (A B : Algorithm) (x outer : List Bool) : ℕ :=
  splitClock A (pair x outer) + 2 * (mid1 A x outer).length + 2 +
    (stage2Clock A x outer + 2 * (mid2 A x outer).length + 2 +
      (stage3Clock A B x outer + 2 * (mid3 A B x outer).length + 2 +
        stage4Clock A B x outer))

theorem machine_outputs (A B : Algorithm) (x : List Bool)
    (t : Fin (outerLength A B x.length) → Bool) :
    (machine A B).OutputsWithin (pair x (List.ofFn t))
      (output A B x (List.ofFn t))
      (clock A B x (List.ofFn t)) := by
  let outer := List.ofFn t
  have houter : outer.length = outerLength A B x.length := List.length_ofFn
  have hfirstLen : A.tapeLength x ≤ outer.length := by
    rw [houter]
    have h := source_plus_suffix A B x.length
    simpa [Algorithm.tapeLength] using Nat.le.intro h
  let first : Fin (A.tapeLength x) → Bool :=
    prefixFn outer (A.tapeLength x) hfirstLen
  have hfirst : List.ofFn first = firstWord A x outer :=
    ofFn_prefixFn outer (A.tapeLength x) hfirstLen
  have hrestLen : (restWord A x outer).length = suffixLength A B x.length := by
    simp [restWord, List.length_drop, houter]
    have h := source_plus_suffix A B x.length
    change A.tapeLength x + suffixLength A B x.length = outerLength A B x.length at h
    omega
  let y := sourceWord A x outer
  have hy : y = A.output x (List.ofFn first) := by
    simp [y, sourceWord, hfirst]
  have hB : B.tapeLength y ≤ (restWord A x outer).length := by
    rw [hy, hrestLen]
    exact classifier_le_suffix A B x first
  let second : Fin (B.tapeLength y) → Bool :=
    prefixFn (restWord A x outer) (B.tapeLength y) hB
  have hsecond : List.ofFn second = secondWord A B x outer := by
    simpa [secondWord, y] using
      ofFn_prefixFn (restWord A x outer) (B.tapeLength y) hB
  have h1 : (splitMachine A).OutputsWithin (pair x outer)
      (mid1 A x outer) (splitClock A (pair x outer)) :=
    split_outputs A x outer
  have h2 : (Paper2.Unit4Shell.PairMap.machine A.machine).OutputsWithin
      (mid1 A x outer) (mid2 A x outer) (stage2Clock A x outer) := by
    have hrun : A.machine.OutputsWithin
        (pair x (firstWord A x outer))
        (A.output x (firstWord A x outer))
        (A.cT * (x.length + 1) ^ A.dT) :=
      (congrArg (fun s : List Bool => A.machine.OutputsWithin
        (pair x s) (A.output x s) (A.cT * (x.length + 1) ^ A.dT)) hfirst).mp
        (A.runs x first)
    exact Paper2.Unit4Shell.PairMap.machine_outputs A.machine
      (pair x (firstWord A x outer)) y (restWord A x outer)
      (A.cT * (x.length + 1) ^ A.dT)
      (by simpa [y, sourceWord] using hrun)
  have h3 : (NPOwner1.Trunc.machine idMachine B.cR B.dR).OutputsWithin
      (mid2 A x outer) (mid3 A B x outer) (stage3Clock A B x outer) := by
    have h := NPOwner1.Trunc.machine_outputs idMachine B.cR B.dR id idC idD idRuns
      (mid2 A x outer)
    change (NPOwner1.Trunc.machine idMachine B.cR B.dR).OutputsWithin
      (pair (sourceWord A x outer) (restWord A x outer))
      (NPOwner1.Trunc.result B.cR B.dR id
        (pair (sourceWord A x outer) (restWord A x outer)))
      (stage3Clock A B x outer) at h
    rw [NPOwner1.Trunc.result_pair] at h
    simpa [mid2, mid3, secondWord, sourceWord, stage3Clock,
      Algorithm.tapeLength] using h
  have h4 : B.machine.OutputsWithin (mid3 A B x outer)
      (output A B x outer) (stage4Clock A B x outer) := by
    have hrun : B.machine.OutputsWithin
        (pair y (secondWord A B x outer))
        (B.output y (secondWord A B x outer))
        (B.cT * (y.length + 1) ^ B.dT) :=
      (congrArg (fun s : List Bool => B.machine.OutputsWithin
        (pair y s) (B.output y s) (B.cT * (y.length + 1) ^ B.dT)) hsecond).mp
        (B.runs y second)
    simpa [mid3, output, mixedOutput, sourceWord, firstWord, restWord,
      secondWord, y, stage4Clock] using hrun
  have h34 := BitMachineComposition.composition_outputsWithin
    (A := NPOwner1.Trunc.machine idMachine B.cR B.dR) (B := B.machine) h3 h4
  have h234 := BitMachineComposition.composition_outputsWithin
    (A := Paper2.Unit4Shell.PairMap.machine A.machine)
    (B := BitMachineComposition.composition
      (NPOwner1.Trunc.machine idMachine B.cR B.dR) B.machine) h2 h34
  have h1234 := BitMachineComposition.composition_outputsWithin
    (A := splitMachine A)
    (B := BitMachineComposition.composition
      (Paper2.Unit4Shell.PairMap.machine A.machine)
      (BitMachineComposition.composition
        (NPOwner1.Trunc.machine idMachine B.cR B.dR) B.machine)) h1 h234
  exact h1234

#print axioms machine_outputs

end Paper2.SelectedTape.Bind
