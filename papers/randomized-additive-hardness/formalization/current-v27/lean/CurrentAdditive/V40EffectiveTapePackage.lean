import Paper2.ETapeETH
import CurrentAdditive.V39SourceCutClock

/-! Generic effective-tape packaging only. The final endpoint must supply
its concrete source-cut/request/classifier machine runs and extension proof;
this module does not assert that a completed decider exists. -/
namespace CurrentAdditive.V40RandomizedETHEndpoint
noncomputable section
open Paper2 EthInapproximability.CurrentPaper
open EncodedComplexity
set_option maxHeartbeats 200000

def sourceCarrier (cutoff j m : ℕ) : ℕ :=
  AEth4.tapeCA (AEth4.phiLen cutoff) (7+j) m

/-- The length machine, length runtime and subexponential tape bound are
reused exactly from the effective source cutter's existing carrier. -/
def withSourceCarrier (cutoff j : ℕ) (machine : BitMachine.Machine)
    (time : List Bool → ℕ) (output : List Bool → List Bool → List Bool)
    (runs : ∀ w (t : Fin (sourceCarrier cutoff j w.length) → Bool),
      machine.OutputsWithin (pair w (List.ofFn t)) (output w (List.ofFn t)) (time w))
    (extend : ∀ w (t u : List Bool), t.length=sourceCarrier cutoff j w.length →
      machine.OutputsWithin (pair w (t++u)) (output w t) (time w)) : AEth2.ETape.Algorithm where
  tapeLen := sourceCarrier cutoff j
  lenMachine := AEth4.CAMachine (AEth4.phiLen cutoff) (7+j)
  lenTime := AEth4.CAtime (AEth4.phiLen cutoff) (7+j)
  lenC := (AEth4.BT+30)*(AEth4.phiLen cutoff+1)^2
  lenE := 2
  lenRuns := AEth4.CAMachine_outputs _ _
  lenPoly := AEth4.CAtime_poly _ _
  tapeSubexp := AEth4.tapeCA_subexp _ _
  machine := machine
  time := time
  output := output
  runs := runs
  extend := extend

theorem withSourceCarrier_probability (cutoff j : ℕ) (machine : BitMachine.Machine)
    (time : List Bool → ℕ) (output : List Bool → List Bool → List Bool)
    (runs : ∀ w (t : Fin (sourceCarrier cutoff j w.length) → Bool),
      machine.OutputsWithin (pair w (List.ofFn t)) (output w (List.ofFn t)) (time w))
    (extend : ∀ w (t u : List Bool), t.length=sourceCarrier cutoff j w.length →
      machine.OutputsWithin (pair w (t++u)) (output w t) (time w))
    (w : List Bool) (event : List Bool → Prop) :
    (withSourceCarrier cutoff j machine time output runs extend).prob w event=
      (Unit4Shell.Definitions.uniformTape (sourceCarrier cutoff j w.length)).prob
        (fun t => event (output w (List.ofFn t))) := rfl

#print axioms withSourceCarrier
#print axioms withSourceCarrier_probability
end
end CurrentAdditive.V40RandomizedETHEndpoint
