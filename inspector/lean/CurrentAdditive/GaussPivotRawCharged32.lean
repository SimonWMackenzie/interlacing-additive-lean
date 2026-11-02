import CurrentAdditive.GaussPivotRawInput32

namespace CurrentAdditive.GaussPivotRawCharged32

open EthInapproximability.CurrentPaper
open CurrentAdditive.GaussStepFields32

noncomputable section

theorem raw_pivot_to_packet_charged {m k : Nat}
    (s : GaussControlTrace.State m k)
    (hr : s.r < m) (hc : s.c < k)
    (pivot : Fin m)
    (hp : CurrentAdditive.SequentialTotality.pivotTyped
      s.B s.r ⟨s.c,hc⟩ = some pivot)
    (hcount : s.r = s.pivots.length)
    (foreign : Stack → List Bool)
    (hblank : ∀ q : Fin 4,
      foreign (GaussBranchFields32.dest q) = [])
    (htag : foreign 20 = [true])
    (h22 : foreign 22 = GaussPhysical.encodeTypedMatrix
      (GaussControlTrace.step s).B)
    (h25 : foreign 25 = [])
    (h23 : foreign 23 = []) (h24 : foreign 24 = [])
    (h26 : foreign 26 = []) (h27 : foreign 27 = [])
    (h28 : foreign 28 = [])
    (hempty : ∀ j : Fin
      (SourceListMachineWriter.framingMachine true).stackCount,
      foreign (GaussPivotFraming32.locate j) = []) :
    ∃ t ≤ GaussPivotRawClock32.clock s foreign hr hc
        (GaussPivotRawClock32.inputBankCharge s foreign),
      (run t (BitMachineInline.cfg (Label.parse false) eParse
        (some (.afterParse false))
        (GaussStepParseRun32.raw s foreign))).l = some .done ∧
      (run t (BitMachineInline.cfg (Label.parse false) eParse
        (some (.afterParse false))
        (GaussStepParseRun32.raw s foreign))).stk 14 =
        GaussControlTrace.statePacket (GaussControlTrace.step s) := by
  exact GaussPivotRawClock32.raw_pivot_to_packet_bound
    s hr hc pivot hp hcount foreign hblank htag h22 h25 h23 h24
    h26 h27 h28 hempty _ (GaussPivotRawInput32.bank_le_charge s foreign)

#print axioms raw_pivot_to_packet_charged

end
end CurrentAdditive.GaussPivotRawCharged32
