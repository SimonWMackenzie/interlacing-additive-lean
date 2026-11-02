import CurrentAdditive.GaussPivotPayloadExact32

/-! Exact global pair-framing endpoint with context preservation. -/

namespace CurrentAdditive.GaussStepPivotPayloadExactRun32

noncomputable section

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding
open CurrentAdditive.GaussStepFields32

private noncomputable abbrev W :=
  SourceListMachineWriter.framingMachine true

def result (pair : List Bool) (S : Stack → List Bool)
    (c : W.Config) : Config :=
  ⟨some .afterPayload,
    ePayload (((),none),W.initial),
    GaussPivotPayload32.afterOut
      (SourceListMachineWriter.result true pair)
      (GaussPivotPayloadExact32.workerResult pair S c)⟩

theorem payload_exact (pair : List Bool)
    (S : Stack → List Bool)
    (h28 : S 28 = pair) (h31 : S 31 = [])
    (hempty : ∀ j : Fin W.stackCount,
      S (GaussPivotFraming32.locate j) = []) :
    ∃ t ≤ (2*pair.length+3)+
        (UnaryBinaryEncoding.coefficient+7)*(pair.length+1)^2+1+
        (2*(SourceListMachineWriter.result true pair).length+3)+1,
      ∃ c : W.Config,
        run t ⟨some (.payload (.copyIn .scan)),
          ePayload (((),none),W.initial),S⟩ = result pair S c := by
  obtain ⟨a,ha,c,hlocal⟩ :=
    GaussPivotPayloadExact32.physical_exact pair S h28 h31 hempty
  let c0 : GaussPivotPayload32.Config :=
    ⟨some (.copyIn .scan),(((),none),W.initial),S⟩
  have hhalt : GaussPivotPayload32.run (a+1) c0 =
      ⟨none,(((),none),W.initial),
        GaussPivotPayload32.afterOut
          (SourceListMachineWriter.result true pair)
          (GaussPivotPayloadExact32.workerResult pair S c)⟩ := by
    change ((advance GaussPivotPayload32.program)^[a+1]) c0 = _
    rw [Function.iterate_succ_apply',
      ← GaussPivotPayload32.run,hlocal]
    rfl
  obtain ⟨u,hu,hglobal⟩ :=
    GaussStepPhaseLift32.payload_lift c0 (a+1)
      (by rw [hhalt])
  exact ⟨u,by omega,c,
    by simpa [BitMachineInline.cfg,hhalt,result,c0] using hglobal⟩

theorem result26 (pair : List Bool) (S : Stack → List Bool)
    (c : W.Config) (h26 : S 26 = []) :
    (result pair S c).stk 26 =
      SourceListMachineWriter.result true pair :=
  GaussPivotPayloadExact32.final26 pair S c h26

theorem result31 (pair : List Bool) (S : Stack → List Bool)
    (c : W.Config) : (result pair S c).stk 31 = [] :=
  GaussPivotPayloadExact32.final31_empty pair S c

theorem result_preserves (pair : List Bool)
    (S : Stack → List Bool) (c : W.Config) (j : Stack)
    (hj : j.val < 8 ∨ 16 ≤ j.val)
    (h28 : j ≠ 28) (h26 : j ≠ 26) (h31 : j ≠ 31) :
    (result pair S c).stk j = S j :=
  GaussPivotPayloadExact32.final_preserves pair S c j hj h28 h26 h31

#print axioms payload_exact
#print axioms result26
#print axioms result_preserves

end
end CurrentAdditive.GaussStepPivotPayloadExactRun32
