import CurrentAdditive.QuarticAnyDecision

/-! The v27 cutter, square printer, and classifier compose on every word. -/

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open EthInapproximability.CurrentPaper
open Paper2

theorem sourceDecision_any_from_bank27
    (cut printer : BitMachine.Machine)
    (C : Paper2.SelectedTape.Algorithm) (K N₁ : ℕ)
    (hN₁ : 1 ≤ N₁) (x tape bank : List Bool)
    (i : EncodedCommunication.Instance)
    (Tcut Tprint Y : ℕ) :
    let Φ := Paper2.AEth4.routed4 K N₁ x
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
    (1 ≤ Paper2.Unit4Shell.Asymptotics.kOf Φ.variables) →
    cut.OutputsWithin
      (EncodedComplexity.pair (EncodedCNF.encode Φ) raw)
      (EncodedComplexity.pair (EncodedCNF.encode Φ) bank) Tcut →
    printer.OutputsWithin bank
      (EncodedCommunication.encodeInstance (Paper2.ASquare.squareInstance i)) Tprint →
    block.length ≤ Y →
    C.tapeLength w ≤ block.length →
    (sourceDecision27 (tailFromPrefix27 cut printer) C K N₁).OutputsWithin
      (EncodedComplexity.pair x tape)
      (C.output w (block.take (C.tapeLength w)))
      (sourceDecisionClock27 C x (Paper2.AEth3.fOut Φ)
        raw block w
        (Paper2.AEth5.twoCutTime K N₁ C.cR x)
        (sourceCoreClock27 Φ raw Ttail) Y) := by
  intro Φ raw block w Ttail hk hcut hprint hY hfit
  have htail := tailFromPrefix27_outputs cut printer Φ hk raw bank i
    Tcut Tprint hcut hprint
  exact sourceDecision_any27 (tailFromPrefix27 cut printer) C K N₁
    hN₁ x tape w Ttail Y htail hY hfit

#print axioms sourceDecision_any_from_bank27

end Paper2.CurrentAdditive.QuarticClassEndpoint
