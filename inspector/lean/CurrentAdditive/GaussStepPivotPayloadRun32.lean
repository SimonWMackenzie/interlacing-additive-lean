import CurrentAdditive.GaussStepPivotPairRun32

/-! Charged framing of the recorded pivot pair inside the fixed controller. -/

namespace CurrentAdditive.GaussStepPivotPayloadRun32

noncomputable section

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding
open CurrentAdditive.GaussStepFields32

private theorem done_step (c : GaussPivotPayload32.Config)
    (h : c.l = some .done) :
    GaussPivotPayload32.run 1 c = ⟨none,c.var,c.stk⟩ := by
  cases c with
  | mk l v S =>
    cases l with
    | none => cases h
    | some l =>
      cases l <;> try cases h
      rfl

theorem payload_phase (pair : List Bool)
    (S : Stack → List Bool)
    (h28 : S 28 = pair) (h31 : S 31 = []) (h26 : S 26 = [])
    (hempty : ∀ j : Fin (SourceListMachineWriter.framingMachine true).stackCount,
      S (GaussPivotFraming32.locate j) = []) :
    ∃ t ≤ (2*pair.length+3) +
        (UnaryBinaryEncoding.coefficient+7)*(pair.length+1)^2 + 1 +
        (2*(SourceListMachineWriter.result true pair).length+3)+1,
      (run t ⟨some (.payload (.copyIn .scan)),
        ePayload (((),none),(SourceListMachineWriter.framingMachine true).initial),S⟩).l =
        some .afterPayload ∧
      (run t ⟨some (.payload (.copyIn .scan)),
        ePayload (((),none),(SourceListMachineWriter.framingMachine true).initial),S⟩).stk 26 =
        SourceListMachineWriter.result true pair ∧
      ∀ j : Stack,
        (j.val < 8 ∨ 16 ≤ j.val) →
        j ≠ 26 → j ≠ 28 → j ≠ 31 →
        (run t ⟨some (.payload (.copyIn .scan)),
          ePayload (((),none),(SourceListMachineWriter.framingMachine true).initial),S⟩).stk j =
          S j := by
  let c0 : GaussPivotPayload32.Config :=
    ⟨some (.copyIn .scan),(((),none),(SourceListMachineWriter.framingMachine true).initial),S⟩
  obtain ⟨a,ha,hl,hout,hpres⟩ :=
    GaussPivotPayload32.physical_payload pair S h28 h31 h26 hempty
  have hlocal : GaussPivotPayload32.run (a+1) c0 =
      ⟨none,(GaussPivotPayload32.run a c0).var,
        (GaussPivotPayload32.run a c0).stk⟩ := by
    rw [GaussPivotPayload32.run_add (show
      GaussPivotPayload32.run a c0 = GaussPivotPayload32.run a c0
      from rfl) 1]
    exact done_step _ hl
  obtain ⟨u,hu,hglobal⟩ :=
    GaussStepPhaseLift32.payload_lift c0 (a+1)
      (by rw [hlocal])
  have he : run u ⟨some (.payload (.copyIn .scan)),
      ePayload (((),none),(SourceListMachineWriter.framingMachine true).initial),S⟩ =
      ⟨some .afterPayload,
        ePayload (GaussPivotPayload32.run a c0).var,
        (GaussPivotPayload32.run a c0).stk⟩ := by
    simpa [BitMachineInline.cfg,hlocal,c0] using hglobal
  refine ⟨u, by omega, ?_, ?_, ?_⟩
  · rw [he]
  · rw [he]
    exact hout
  · intro j hj h26' h28' h31'
    rw [he]
    exact hpres j hj h26' h28' h31'

#print axioms payload_phase

end
end CurrentAdditive.GaussStepPivotPayloadRun32
