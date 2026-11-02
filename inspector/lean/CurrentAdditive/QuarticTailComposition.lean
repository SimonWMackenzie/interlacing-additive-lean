import CurrentAdditive.QuarticHeaderFromBank
import Paper2.E6Cls

/-!
# Physical v27 square-header and estimator composition

This is a machine-composition lemma for the exact current selector.  Its two
input machines are a physical prefix-to-bank constructor and the checked v27
square printer.  The lemma does not assert either input machine exists.
-/

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open EthInapproximability.CurrentPaper
open Paper2

noncomputable def tailFromPrefix27 (cut printer : BitMachine.Machine) :
    BitMachine.Machine :=
  BitMachineComposition.composition cut (headerFromBank27 printer)

theorem tailFromPrefix27_outputs (cut printer : BitMachine.Machine)
    (Φ : EncodedCNF.Formula)
    (hk : 1 ≤ Paper2.Unit4Shell.Asymptotics.kOf Φ.variables)
    (raw bank : List Bool) (i : EncodedCommunication.Instance)
    (Tcut Tprint : ℕ)
    (hcut : cut.OutputsWithin
      (EncodedComplexity.pair (EncodedCNF.encode Φ) raw)
      (EncodedComplexity.pair (EncodedCNF.encode Φ) bank) Tcut)
    (hprint : printer.OutputsWithin bank
      (EncodedCommunication.encodeInstance (Paper2.ASquare.squareInstance i)) Tprint) :
    (tailFromPrefix27 cut printer).OutputsWithin
      (EncodedComplexity.pair (EncodedCNF.encode Φ) raw)
      (Paper2.HeaderWordRun.headeredWord
        (Paper2.Unit4Shell.Asymptotics.kOf Φ.variables)
        (Paper2.ASquare.squareInstance i))
      (Tcut + 2 * (EncodedComplexity.pair (EncodedCNF.encode Φ) bank).length + 2 +
        headerClock27 Φ bank i
          ((EncodedCNF.encode Φ).length + 2 + 2 * bank.length + 2 + Tprint)) := by
  have hh := headerFromBank27_outputs printer Φ hk bank i Tprint hprint
  exact BitMachineComposition.composition_outputsWithin cut
    (headerFromBank27 printer) hcut hh

noncomputable def classifyTail27 (cut printer : BitMachine.Machine)
    (C : Paper2.SelectedTape.Algorithm) : BitMachine.Machine :=
  BitMachineComposition.composition
    (Paper2.Unit4Shell.PairMap.machine (tailFromPrefix27 cut printer))
    (Paper2.AEth5.clsStage C)

theorem classifyTail27_outputs (cut printer : BitMachine.Machine)
    (C : Paper2.SelectedTape.Algorithm) (Φ : EncodedCNF.Formula)
    (hk : 1 ≤ Paper2.Unit4Shell.Asymptotics.kOf Φ.variables)
    (raw bank block : List Bool) (i : EncodedCommunication.Instance)
    (Tcut Tprint Y : ℕ)
    (hcut : cut.OutputsWithin
      (EncodedComplexity.pair (EncodedCNF.encode Φ) raw)
      (EncodedComplexity.pair (EncodedCNF.encode Φ) bank) Tcut)
    (hprint : printer.OutputsWithin bank
      (EncodedCommunication.encodeInstance (Paper2.ASquare.squareInstance i)) Tprint)
    (hY : block.length ≤ Y)
    (hfit : C.tapeLength
      (Paper2.HeaderWordRun.headeredWord
        (Paper2.Unit4Shell.Asymptotics.kOf Φ.variables)
        (Paper2.ASquare.squareInstance i)) ≤ block.length) :
    let w := Paper2.HeaderWordRun.headeredWord
      (Paper2.Unit4Shell.Asymptotics.kOf Φ.variables)
      (Paper2.ASquare.squareInstance i)
    (classifyTail27 cut printer C).OutputsWithin
      (EncodedComplexity.pair
        (EncodedComplexity.pair (EncodedCNF.encode Φ) raw) block)
      (C.output w (block.take (C.tapeLength w)))
      (2 * (EncodedComplexity.pair (EncodedCNF.encode Φ) raw).length +
          (Tcut + 2 * (EncodedComplexity.pair (EncodedCNF.encode Φ) bank).length + 2 +
            headerClock27 Φ bank i
              ((EncodedCNF.encode Φ).length + 2 + 2 * bank.length + 2 + Tprint)) +
          2 * w.length + 6 +
        2 * (EncodedComplexity.pair w block).length + 2 +
        Paper2.AEth5.clsTime C w.length Y) := by
  intro w
  have ht := tailFromPrefix27_outputs cut printer Φ hk raw bank i Tcut Tprint hcut hprint
  have hp := Paper2.Unit4Shell.PairMap.machine_outputs
    (M := tailFromPrefix27 cut printer)
    (EncodedComplexity.pair (EncodedCNF.encode Φ) raw) w block _ ht
  have hc := Paper2.AEth5.clsStage_outputs C w block Y hY hfit
  exact BitMachineComposition.composition_outputsWithin
    (Paper2.Unit4Shell.PairMap.machine (tailFromPrefix27 cut printer))
    (Paper2.AEth5.clsStage C) hp hc

#print axioms tailFromPrefix27_outputs
#print axioms classifyTail27_outputs

end Paper2.CurrentAdditive.QuarticClassEndpoint
