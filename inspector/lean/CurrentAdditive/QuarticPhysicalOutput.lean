import CurrentAdditive.QuarticFormulaDecision

/-!
The exact v27 prefix-to-bank run and square printer feed the fixed source
decision machine.  The theorem is physical: all three stages are
`BitMachine.OutputsWithin` runs on the actual words.
-/

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open EthInapproximability.CurrentPaper
open Paper2

theorem sourceDecision_from_bank27 (cut printer : BitMachine.Machine)
    (C : Paper2.SelectedTape.Algorithm) (K N₁ : ℕ)
    (hN₁ : 1 ≤ N₁) (Φ : EncodedCNF.Formula)
    (hroute : Paper2.AEth4.routed4 K N₁ (EncodedCNF.encode Φ) = Φ)
    (hk : 1 ≤ Paper2.Unit4Shell.Asymptotics.kOf Φ.variables)
    (tape bank : List Bool) (i : EncodedCommunication.Instance)
    (Tcut Tprint Y : ℕ)
    (hcut : cut.OutputsWithin
      (EncodedComplexity.pair (EncodedCNF.encode Φ)
        (tape.take (Paper2.AEth3.cutLen Φ)))
      (EncodedComplexity.pair (EncodedCNF.encode Φ) bank) Tcut)
    (hprint : printer.OutputsWithin bank
      (EncodedCommunication.encodeInstance (Paper2.ASquare.squareInstance i)) Tprint)
    (hY : ((tape.take (2 ^ C.cR * Paper2.AEth3.cutLen Φ)).drop
      (Paper2.AEth3.cutLen Φ)).length ≤ Y)
    (hfit : C.tapeLength
      (Paper2.HeaderWordRun.headeredWord
        (Paper2.Unit4Shell.Asymptotics.kOf Φ.variables)
        (Paper2.ASquare.squareInstance i)) ≤
      ((tape.take (2 ^ C.cR * Paper2.AEth3.cutLen Φ)).drop
        (Paper2.AEth3.cutLen Φ)).length) :
    let raw := tape.take (Paper2.AEth3.cutLen Φ)
    let block := (tape.take (2 ^ C.cR * Paper2.AEth3.cutLen Φ)).drop
      (Paper2.AEth3.cutLen Φ)
    let w := Paper2.HeaderWordRun.headeredWord
      (Paper2.Unit4Shell.Asymptotics.kOf Φ.variables)
      (Paper2.ASquare.squareInstance i)
    let Ttail := Tcut + 2 * (EncodedComplexity.pair
      (EncodedCNF.encode Φ) bank).length + 2 +
      headerClock27 Φ bank i
        ((EncodedCNF.encode Φ).length + 2 + 2 * bank.length + 2 + Tprint)
    (sourceDecision27 (tailFromPrefix27 cut printer) C K N₁).OutputsWithin
      (EncodedComplexity.pair (EncodedCNF.encode Φ) tape)
      (C.output w (block.take (C.tapeLength w)))
      (sourceDecisionClock27 C (EncodedCNF.encode Φ) (Paper2.AEth3.fOut Φ)
        raw block w
        (Paper2.AEth5.twoCutTime K N₁ C.cR (EncodedCNF.encode Φ))
        (sourceCoreClock27 Φ raw Ttail) Y) := by
  intro raw block w Ttail
  have htail := tailFromPrefix27_outputs cut printer Φ hk raw bank i
    Tcut Tprint hcut hprint
  exact sourceDecision_formula27 (tailFromPrefix27 cut printer) C K N₁
    hN₁ Φ hroute tape w Ttail Y htail hY hfit

#print axioms sourceDecision_from_bank27

end Paper2.CurrentAdditive.QuarticClassEndpoint
