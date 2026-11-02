import CurrentAdditive.GaussStepInactivePacket32

/-! The fixed Fin32 field controller, started with the actual Bank4 state,
implements the semantic transition on the two branches that do not pivot.
The pivot branch still needs its physical matrix/request and list-field join. -/

namespace CurrentAdditive.GaussInactiveSemanticStep32

noncomputable section

open EthInapproximability.CurrentPaper
open CurrentAdditive.GaussStepFields32

theorem terminal_row {m k : Nat}
    (s : GaussControlTrace.State m k) (hr : ¬ s.r < m)
    (foreign : Stack → List Bool)
    (hblank : ∀ p : Fin 4,
      foreign (GaussBranchFields32.dest p) = [])
    (h25 : foreign 25 = []) :
    ∃ t,
      (run t (BitMachineInline.cfg (Label.parse true) eParse
        (some (.afterParse true))
        (GaussStepParseRun32.raw s foreign))).l = some .done ∧
      (run t (BitMachineInline.cfg (Label.parse true) eParse
        (some (.afterParse true))
        (GaussStepParseRun32.raw s foreign))).stk 14 =
        GaussControlTrace.statePacket (GaussControlTrace.step s) := by
  simpa [GaussControlTrace.step, hr] using
    GaussStepInactivePacket32.terminal_packet s foreign hblank h25

theorem terminal_column {m k : Nat}
    (s : GaussControlTrace.State m k)
    (hr : s.r < m) (hc : ¬ s.c < k)
    (foreign : Stack → List Bool)
    (hblank : ∀ p : Fin 4,
      foreign (GaussBranchFields32.dest p) = [])
    (h25 : foreign 25 = []) :
    ∃ t,
      (run t (BitMachineInline.cfg (Label.parse true) eParse
        (some (.afterParse true))
        (GaussStepParseRun32.raw s foreign))).l = some .done ∧
      (run t (BitMachineInline.cfg (Label.parse true) eParse
        (some (.afterParse true))
        (GaussStepParseRun32.raw s foreign))).stk 14 =
        GaussControlTrace.statePacket (GaussControlTrace.step s) := by
  simpa [GaussControlTrace.step, hr, hc] using
    GaussStepInactivePacket32.terminal_packet s foreign hblank h25

theorem no_pivot {m k : Nat}
    (s : GaussControlTrace.State m k)
    (hr : s.r < m) (hc : s.c < k)
    (hp : CurrentAdditive.SequentialTotality.pivotTyped
      s.B s.r ⟨s.c, hc⟩ = none)
    (foreign : Stack → List Bool)
    (hblank : ∀ p : Fin 4,
      foreign (GaussBranchFields32.dest p) = [])
    (htag : foreign 20 = [false])
    (h25 : foreign 25 = []) :
    ∃ t,
      (run t (BitMachineInline.cfg (Label.parse false) eParse
        (some (.afterParse false))
        (GaussStepParseRun32.raw s foreign))).l = some .done ∧
      (run t (BitMachineInline.cfg (Label.parse false) eParse
        (some (.afterParse false))
        (GaussStepParseRun32.raw s foreign))).stk 14 =
        GaussControlTrace.statePacket (GaussControlTrace.step s) := by
  have h := GaussStepInactivePacket32.noPivot_packet s foreign
    hblank htag h25
  simpa [GaussControlTrace.step, hr, hc, hp,
    GaussBranchFields32.noPivotState] using h

#print axioms terminal_row
#print axioms terminal_column
#print axioms no_pivot

end
end CurrentAdditive.GaussInactiveSemanticStep32
