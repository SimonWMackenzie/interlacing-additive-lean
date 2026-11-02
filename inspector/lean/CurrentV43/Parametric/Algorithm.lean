import CurrentV43.Parametric.Carrier

set_option autoImplicit false
namespace CurrentV43.FairBitAlgorithm
noncomputable section
open Paper2 EthInapproximability.CurrentPaper CurrentAdditive

/-- A uniform fair-bit algorithm with an input-dependent, physically
printed finite carrier.  Each field describes the same actual machine.
The complete charge is defined separately so that length generation and
initial random input framing cannot disappear from a runtime theorem. -/
structure Algorithm where
  carrier : PhysicalConcat.Producer
  tapeLength : List Bool → Nat
  carrier_result : ∀ w, carrier.result w=List.replicate (tapeLength w) true
  machine : BitMachine.Machine
  output : List Bool → List Bool → List Bool
  time : List Bool → Nat
  runs : ∀ (w : List Bool) (tape : Fin (tapeLength w)→Bool),
    machine.OutputsWithin (EncodedComplexity.pair w (List.ofFn tape))
      (output w (List.ofFn tape)) (time w)

def Algorithm.prob (A : Algorithm) (w : List Bool) (event : List Bool→Prop) : ℝ :=
  (Unit4Shell.Definitions.uniformTape (A.tapeLength w)).prob
    (fun tape => event (A.output w (List.ofFn tape)))

/-- One transition per fair bit, a linear bound for inserting the input
field and raw random block, the physical carrier printer, and the actual
execution are all included. -/
def Algorithm.totalTime (A : Algorithm) (w : List Bool) : Nat :=
  A.carrier.clock w+A.tapeLength w+4*(w.length+A.tapeLength w+1)+A.time w

theorem Algorithm.carrier_runs (A : Algorithm) (w : List Bool) :
    A.carrier.machine.OutputsWithin w (List.replicate (A.tapeLength w) true) (A.carrier.clock w) := by
  rw [←A.carrier_result]
  exact A.carrier.outputs w

theorem Algorithm.runs_total (A : Algorithm) (w : List Bool) (tape : Fin (A.tapeLength w)→Bool) :
    A.machine.OutputsWithin (EncodedComplexity.pair w (List.ofFn tape))
      (A.output w (List.ofFn tape)) (A.totalTime w) := by
  apply BitMachine.outputsWithin_mono _ (A.runs w tape)
  unfold Algorithm.totalTime
  omega

theorem Algorithm.carrier_time_le (A : Algorithm) (w : List Bool) : A.carrier.clock w≤A.totalTime w := by
  unfold Algorithm.totalTime
  omega

theorem Algorithm.random_bits_le (A : Algorithm) (w : List Bool) : A.tapeLength w≤A.totalTime w := by
  unfold Algorithm.totalTime
  omega

theorem Algorithm.initial_word_length_le (A : Algorithm) (w : List Bool)
    (tape : Fin (A.tapeLength w)→Bool) :
    (EncodedComplexity.pair w (List.ofFn tape)).length≤A.totalTime w := by
  rw [EncodedComplexity.pair_length,List.length_ofFn]
  unfold Algorithm.totalTime
  omega

#print axioms Algorithm.carrier_runs
#print axioms Algorithm.runs_total
end
end CurrentV43.FairBitAlgorithm
