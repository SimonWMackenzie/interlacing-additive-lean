import CurrentAdditive.V40PreparedSearchClock
import CurrentAdditive.V40RawSearchEngine

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace CurrentAdditive.V40RawFirstPassingSearch

open EthInapproximability.CurrentPaper V39GeneratedConstruction
open V40ActualPreparedSearch

noncomputable section

attribute [local irreducible] D22GeneratedTestMachine.testMachine
  D22GeneratedTestMachine.clockCoefficient D22GeneratedTestMachine.clockDegree

def machine (p : SourceConstants) : BitMachine.Machine := V40RawSearchEngine.machine (tester p) p

def results := V40RawSearchEngine.results
def times := V40RawSearchEngine.times
def batchCap := V40RawSearchEngine.batchCap
def clock (p : SourceConstants) (floor n m : Nat) : Nat :=
  batchCap floor n m + loopCap p floor n m + 1

/-- The fixed machine computes the exact first passing exponent from the
original three-field input. The only input hypotheses are graph promises. -/
theorem raw_outputs (p : SourceConstants) (floor n m : Nat)
    (hn : 0 < n) (hlow : n ≤ 2 * m) (hdegree : 2 * m ≤ p.degree * n) :
    (machine p).OutputsWithin (V40SearchInitialization.input floor n m)
      (List.replicate (publicLogFrom p floor n m hn hlow hdegree) true)
      (clock p floor n m) := by
  exact V40RawSearchEngine.raw_outputs (tester p) p
    (D22GeneratedTestMachine.clockCoefficient p) (D22GeneratedTestMachine.clockDegree p)
    floor n m hn hlow hdegree (by
      intro L hL
      have h := D22GeneratedTestMachine.test_outputs_le_upper p n m L (publicUpperLog p floor n) hn hL
      simpa only [tester, D22GeneratedTestMachine.testInput, V40ThreeFieldPacket.bytes,
        V40ThreeFieldPacket.words, V40DeterministicBoundedSearch.test,
        V40PreparedSearchEngine.testCap] using h)

end
end CurrentAdditive.V40RawFirstPassingSearch
