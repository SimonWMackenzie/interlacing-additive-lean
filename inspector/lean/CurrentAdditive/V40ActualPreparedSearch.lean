import CurrentAdditive.V40PreparedSearchEngine
import CurrentAdditive.V40PredicateBody
import CurrentAdditive.V40DeterministicBoundedSearch
import CurrentAdditive.D22GeneratedTestMachine

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 8192

namespace CurrentAdditive.V40ActualPreparedSearch

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open V39GeneratedConstruction V38Schedule
open CurrentAdditive.MinimumRatioContext

noncomputable section

attribute [local irreducible] D22GeneratedTestMachine.testMachine
  D22GeneratedTestMachine.clockCoefficient D22GeneratedTestMachine.clockDegree



@[irreducible] def tester (p : SourceConstants) : BitMachine.Machine := D22GeneratedTestMachine.testMachine p
abbrev Stack (p : SourceConstants) := V40PredicateBody.Stack (tester p)
abbrev Bank (p : SourceConstants) := Stack p → List Bool

def low (p : SourceConstants) := V40PredicateBody.low (tester p)

def state (p : SourceConstants) (B : Bank p) (L : Nat) : Bank p :=
  V40FirstPassingController.bank B (low p 2) (low p 9) L

def program (p : SourceConstants) := V40FirstPassingController.program
  (V40PredicateBody.program (tester p)) (V40PredicateBody.entry (tester p))
  (V40PredicateBody.initial (tester p)) (low p 2) (low p 9)

abbrev Label (p : SourceConstants) := V40FirstPassingController.Label
      (BitMachineRawSequence.Label
        (BitMachineRawSequence.Label V40ThreeFieldPacket.Label (MachineInvokeFull.LabelFull (tester p))) Bool)

def entry (p : SourceConstants) : Label p :=
  Sum.inl (V40PredicateBody.entry (tester p))

def initial (p : SourceConstants) := (V40PredicateBody.initial (tester p), (none : Option Bool))

def requestCap (n m U : Nat) := 2 * (n + m + U) + 3

def testCap (p : SourceConstants) (n m U : Nat) :=
  D22GeneratedTestMachine.clockCoefficient p * (2 ^ U + n + m + 1) ^
    D22GeneratedTestMachine.clockDegree p

def stepCap (p : SourceConstants) (n m U : Nat) :=
  4 * requestCap n m U + MachineInvokeFull.uniformBound (tester p)
    (List.replicate (requestCap n m U) true) (testCap p n m U) + 12



/-- The actual physical tester instantiates the generic preserving loop.
No numerical-test, completion, or final-state premise is left to the caller. -/
theorem prepared_run (p : SourceConstants) (B : Bank p) (floor n m : Nat)
    (hn : 0 < n) (hlow : n ≤ 2 * m) (hdegree : 2 * m ≤ p.degree * n)
    (h0 : B (low p 0) = List.replicate n true)
    (h1 : B (low p 1) = List.replicate m true)
    (hblank : ∀ i : Fin 6, B ⟨i.val + 3, by omega⟩ = [])
    (hscratch : B (low p 31) = [])
    (hhigh : ∀ i, B ((V40PredicateBody.callSlots (tester p)).machine i) = []) :
    ∃ t ≤ (publicUpperLog p floor n - V40DeterministicBoundedSearch.start floor n + 1) *
        (stepCap p n m (publicUpperLog p floor n) + 1),
      ((advance (program p))^[t])
        (⟨some (entry p), initial p, state p B (V40DeterministicBoundedSearch.start floor n)⟩ :
          TM2.Cfg (fun _ : Stack p => Bool) _ _) =
        ⟨none, (V40PredicateBody.initial (tester p), some true),
          state p B (publicLogFrom p floor n m hn hlow hdegree)⟩ := by
  exact V40PreparedSearchEngine.prepared_run (tester p) p
    (D22GeneratedTestMachine.clockCoefficient p) (D22GeneratedTestMachine.clockDegree p)
    B floor n m hn hlow hdegree h0 h1 hblank hscratch hhigh (by
      intro L hL
      have h := D22GeneratedTestMachine.test_outputs_le_upper p n m L (publicUpperLog p floor n) hn hL
      simpa only [tester, D22GeneratedTestMachine.testInput, V40ThreeFieldPacket.bytes,
        V40ThreeFieldPacket.words, V40DeterministicBoundedSearch.test,
        V40PreparedSearchEngine.testCap] using h)
theorem selected_ge_two (p : SourceConstants) (floor n m : Nat)
    (hn : 0 < n) (hlow : n ≤ 2 * m) (hdegree : 2 * m ≤ p.degree * n) :
    2 ≤ publicLogFrom p floor n m hn hlow hdegree := by
  let L := publicLogFrom p floor n m hn hlow hdegree
  have ht := (publicLogFrom_spec p floor n m hn hlow hdegree).2
  have hs := passing_s_ge_four _ _ _ _ _ ht
  change 4 ≤ generatedS L at hs
  by_contra h
  have hL : L = 0 ∨ L = 1 := by omega
  rcases hL with hL | hL <;> simp [hL, generatedS, quarterCeil] at hs

end
end CurrentAdditive.V40ActualPreparedSearch
