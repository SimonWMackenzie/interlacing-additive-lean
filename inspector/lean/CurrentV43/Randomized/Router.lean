import CurrentV43.Randomized.Source
import CurrentV43.Parametric.Carrier

namespace CurrentV43.RandomizedRate
noncomputable section
open CurrentAdditive Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition
open Unit4Shell.T10Finite Unit4Shell.Asymptotics
open V42RandomizedETHEndpoint
set_option maxHeartbeats 2000000
set_option maxRecDepth 32768

/-- The charged all-input router preserves every sparse formula's
satisfiability and sends every raw word to a sufficiently large valid formula. -/
def router (cs cutoff : ℕ) (hcutoff : 1 ≤ cutoff) : PhysicalConcat.Producer where
  machine := AEth4.route3 (cs+2) cutoff
  result := fun w => EncodedCNF.encode (routedSource cs cutoff hcutoff w).val
  clock := AEth4.route3Time (cs+2) cutoff
  outputs w := by
    have h := AEth4.route3_outputs (cs+2) cutoff hcutoff w
    rw [AEth4.route3Out_eq] at h
    exact h

/-- Routing copies and transforms only the formula component. The random
tape reaches the same fixed downstream program without being changed. -/
def routerTapeMachine (cs cutoff : ℕ) (hcutoff : 1 ≤ cutoff) :=
  Unit4Shell.PairMap.machine (router cs cutoff hcutoff).machine

def routerTapeClock (cs cutoff : ℕ) (hcutoff : 1 ≤ cutoff) (w : List Bool) :=
  2*w.length+(router cs cutoff hcutoff).clock w+
    2*((router cs cutoff hcutoff).result w).length+6

theorem routerTape_outputs (cs cutoff : ℕ) (hcutoff : 1 ≤ cutoff) (w tape : List Bool) :
    (routerTapeMachine cs cutoff hcutoff).OutputsWithin (EncodedComplexity.pair w tape)
      (EncodedComplexity.pair ((router cs cutoff hcutoff).result w) tape)
      (routerTapeClock cs cutoff hcutoff w) :=
  Unit4Shell.PairMap.machine_outputs _ _ _ tape _ ((router cs cutoff hcutoff).outputs w)

/-- On every sufficiently large promised input, routing is literally the
identity, which makes the original variable count control the final clock. -/
theorem router_result_large (cs cutoff : ℕ) (hcutoff : 1 ≤ cutoff)
    (Φ : ValidFormula) (hsp : Φ.val.clauses.length ≤ cs*Φ.val.variables)
    (hN : cutoff ≤ Φ.val.variables) :
    (router cs cutoff hcutoff).result (EncodedCNF.encode Φ.val) = EncodedCNF.encode Φ.val := by
  change EncodedCNF.encode (AEth4.routed4 (cs+2) cutoff (EncodedCNF.encode Φ.val)) = _
  rw [AEth4.routed4_encode (cs+2) cutoff Φ.val Φ.property
    (hsp.trans (Nat.mul_le_mul_right _ (by omega))) hN]

#print axioms routerTape_outputs
#print axioms router_result_large
end
end CurrentV43.RandomizedRate
