import CurrentAdditive.QuarticPairSecond

/-!
# The v27 square printer plus formula header on one fixed machine

The first step physically projects the selected bank from its pair with the
encoded formula. The next step runs the v27 square printer, and the proved
header suffix writes the estimator word. Every handoff has an explicit cost.
-/

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open EthInapproximability.CurrentPaper
open Paper2

noncomputable def headerFromBank27 (M : BitMachine.Machine) : BitMachine.Machine :=
  headerMachine27 (BitMachineComposition.composition PairSecond.machine M)

theorem headerFromBank27_outputs (M : BitMachine.Machine)
    (Φ : EncodedCNF.Formula)
    (hk : 1 ≤ Paper2.Unit4Shell.Asymptotics.kOf Φ.variables)
    (bank : List Bool) (i : EncodedCommunication.Instance) (T₀ : ℕ)
    (hM : M.OutputsWithin bank
      (EncodedCommunication.encodeInstance (Paper2.ASquare.squareInstance i)) T₀) :
    (headerFromBank27 M).OutputsWithin
      (EncodedComplexity.pair (EncodedCNF.encode Φ) bank)
      (Paper2.HeaderWordRun.headeredWord
        (Paper2.Unit4Shell.Asymptotics.kOf Φ.variables)
        (Paper2.ASquare.squareInstance i))
      (headerClock27 Φ bank i
        ((EncodedCNF.encode Φ).length + 2 + 2 * bank.length + 2 + T₀)) := by
  have hproj := PairSecond.machine_outputs (EncodedCNF.encode Φ) bank
  have hfirst := BitMachineComposition.composition_outputsWithin
    PairSecond.machine M hproj hM
  exact headerMachine27_outputs _ Φ hk bank i _ hfirst

#print axioms headerFromBank27_outputs

end Paper2.CurrentAdditive.QuarticClassEndpoint
