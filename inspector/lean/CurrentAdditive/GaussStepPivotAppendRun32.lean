import CurrentAdditive.GaussStepPivotPayloadRun32

/-! Charged append of the framed pivot pair to the V2 body. -/

namespace CurrentAdditive.GaussStepPivotAppendRun32

noncomputable section

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding
open CurrentAdditive.GaussStepFields32

private theorem done_step (c : GaussPivotAppend32.Config)
    (h : c.l = some .done) :
    GaussPivotAppend32.run 1 c = ⟨none,c.var,c.stk⟩ := by
  cases c with
  | mk l v S =>
    cases l with
    | none => cases h
    | some l =>
      cases l <;> try cases h
      rfl

theorem append_phase (body payload : List Bool)
    (S : Stack → List Bool)
    (h23 : S 23 = body) (h26 : S 26 = payload)
    (h27 : S 27 = []) (h24 : S 24 = []) (h31 : S 31 = []) :
    ∃ t ≤ (2*body.length+3)+
        (4*body.length+2*payload.length+7)+1,
      (run t ⟨some (.append (.copyBodyDirect .scan)),
        eAppend ((),none),S⟩).l = some .afterAppend ∧
      (run t ⟨some (.append (.copyBodyDirect .scan)),
        eAppend ((),none),S⟩).stk 27 = body++payload := by
  let c0 : GaussPivotAppend32.Config :=
    ⟨some (.copyBodyDirect .scan),((),none),S⟩
  obtain ⟨a,ha,hl,hout⟩ :=
    GaussPivotAppend32.physical_extend body payload S
      h23 h26 h27 h24 h31
  have hlocal : GaussPivotAppend32.run (a+1) c0 =
      ⟨none,(GaussPivotAppend32.run a c0).var,
        (GaussPivotAppend32.run a c0).stk⟩ := by
    rw [GaussPivotAppend32.run_add (show
      GaussPivotAppend32.run a c0 = GaussPivotAppend32.run a c0
      from rfl) 1]
    exact done_step _ hl
  obtain ⟨u,hu,hglobal⟩ :=
    GaussStepPhaseLift32.append_lift c0 (a+1)
      (by rw [hlocal])
  have he : run u ⟨some (.append (.copyBodyDirect .scan)),
      eAppend ((),none),S⟩ =
      ⟨some .afterAppend,
        eAppend (GaussPivotAppend32.run a c0).var,
        (GaussPivotAppend32.run a c0).stk⟩ := by
    simpa [BitMachineInline.cfg,hlocal,c0] using hglobal
  refine ⟨u, by omega, ?_, ?_⟩
  · rw [he]
  · rw [he]
    exact hout

#print axioms append_phase

end
end CurrentAdditive.GaussStepPivotAppendRun32
