import CurrentAdditive.GaussStepPivotAppendRun32

/-! Charged framing of the updated V2 pivot-list count. -/

namespace CurrentAdditive.GaussStepPivotHeaderRun32

noncomputable section

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding
open CurrentAdditive.GaussStepFields32

private theorem done_step (c : GaussPivotHeader32.Config)
    (h : c.l = some .done) :
    GaussPivotHeader32.run 1 c = ⟨none,c.var,c.stk⟩ := by
  cases c with
  | mk l v S =>
    cases l with
    | none => cases h
    | some l =>
      cases l <;> try cases h
      rfl

theorem header_phase (unary : List Bool)
    (S : Stack → List Bool)
    (h5 : S 5 = unary) (h31 : S 31 = []) (h30 : S 30 = [])
    (hempty : ∀ j : Fin
      (SourceListMachineWriter.framingMachine false).stackCount,
      S (GaussPivotFraming32.locate j) = []) :
    ∃ t ≤ (2*unary.length+3)+
        (UnaryBinaryEncoding.coefficient+7)*(unary.length+1)^2 + 1 +
        (2*(SourceListMachineWriter.result false unary).length+3)+1,
      (run t ⟨some (.header (.copyIn .scan)),
        eHeader (((),none),
          (SourceListMachineWriter.framingMachine false).initial),S⟩).l =
        some .afterHeader ∧
      (run t ⟨some (.header (.copyIn .scan)),
        eHeader (((),none),
          (SourceListMachineWriter.framingMachine false).initial),S⟩).stk 30 =
        SourceListMachineWriter.result false unary := by
  let c0 : GaussPivotHeader32.Config :=
    ⟨some (.copyIn .scan),
      (((),none),(SourceListMachineWriter.framingMachine false).initial),S⟩
  obtain ⟨a,ha,hl,hout⟩ :=
    GaussPivotHeader32.physical_payload unary S h5 h31 h30 hempty
  have hlocal : GaussPivotHeader32.run (a+1) c0 =
      ⟨none,(GaussPivotHeader32.run a c0).var,
        (GaussPivotHeader32.run a c0).stk⟩ := by
    rw [GaussPivotHeader32.run_add (show
      GaussPivotHeader32.run a c0 = GaussPivotHeader32.run a c0
      from rfl) 1]
    exact done_step _ hl
  obtain ⟨u,hu,hglobal⟩ :=
    GaussStepPhaseLift32.header_lift c0 (a+1)
      (by rw [hlocal])
  have he : run u ⟨some (.header (.copyIn .scan)),
      eHeader (((),none),
        (SourceListMachineWriter.framingMachine false).initial),S⟩ =
      ⟨some .afterHeader,
        eHeader (GaussPivotHeader32.run a c0).var,
        (GaussPivotHeader32.run a c0).stk⟩ := by
    simpa [BitMachineInline.cfg,hlocal,c0] using hglobal
  refine ⟨u, by omega, ?_, ?_⟩
  · rw [he]
  · rw [he]
    exact hout

#print axioms header_phase

end
end CurrentAdditive.GaussStepPivotHeaderRun32
