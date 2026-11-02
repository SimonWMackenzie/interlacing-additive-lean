import Paper2.BindRetainRun
import Paper2.BindEnvelope

/-!
# Exact physical split of A's source block from the retained B block

The counter is `A.cR * (|x|+1)^A.dR`, calculated inside the fixed machine.
The output is a nested framed word suitable for `PairMap A.machine`; the
unused suffix remains verbatim rather than being deleted by truncation.
-/

noncomputable section

namespace Paper2.SelectedTape.Bind

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedComplexity

def idMachine : BitMachine.Machine :=
  Classical.choose ComplexityReductionClosure.polytime_id
def idC : ℕ :=
  Classical.choose (Classical.choose_spec ComplexityReductionClosure.polytime_id)
def idD : ℕ :=
  Classical.choose (Classical.choose_spec
    (Classical.choose_spec ComplexityReductionClosure.polytime_id))
theorem idRuns :
    idMachine.ComputesWithin id (fun n => idC * (n + 1) ^ idD) :=
  Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec ComplexityReductionClosure.polytime_id))

def splitMachine (A : Algorithm) : BitMachine.Machine :=
  Retain.machine idMachine A.cR A.dR

def splitClock (A : Algorithm) (w : List Bool) : ℕ :=
  Retain.timeBound A.cR A.dR idC idD idMachine.pushBound w.length

theorem split_outputs (A : Algorithm) (x tape : List Bool) :
    (splitMachine A).OutputsWithin (pair x tape)
      (pair (pair x (tape.take (A.tapeLength x)))
        (tape.drop (A.tapeLength x)))
      (splitClock A (pair x tape)) := by
  have h := Retain.machine_outputs idMachine A.cR A.dR id idC idD idRuns
    (pair x tape)
  rw [Retain.result_pair] at h
  simpa [splitMachine, splitClock, Algorithm.tapeLength] using h

theorem split_clock_poly (A : Algorithm) :
    Paper2.Unit4Shell.Poly.PolyIn id (fun n =>
      Retain.timeBound A.cR A.dR idC idD idMachine.pushBound n) := by
  unfold Retain.timeBound
  repeat (first
    | exact Paper2.Unit4Shell.Poly.self
    | exact Paper2.Unit4Shell.Poly.const _
    | apply Paper2.Unit4Shell.Poly.add
    | apply Paper2.Unit4Shell.Poly.mul
    | apply Paper2.Unit4Shell.Poly.pow)

#print axioms split_outputs
#print axioms split_clock_poly

end Paper2.SelectedTape.Bind
