import CurrentAdditive.GaussPivotHeaderExact32

/-! Exact global count-header endpoint with context preservation. -/

namespace CurrentAdditive.GaussStepPivotHeaderExactRun32

noncomputable section

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding
open CurrentAdditive.GaussStepFields32

private noncomputable abbrev W :=
  SourceListMachineWriter.framingMachine false

def result (unary : List Bool) (S : Stack → List Bool)
    (c : W.Config) : Config :=
  ⟨some .afterHeader,
    eHeader (((),none),W.initial),
    GaussPivotHeader32.afterOut
      (SourceListMachineWriter.result false unary)
      (GaussPivotHeaderExact32.workerResult unary S c)⟩

theorem header_exact (unary : List Bool)
    (S : Stack → List Bool)
    (h5 : S 5 = unary) (h31 : S 31 = []) (h30 : S 30 = [])
    (hempty : ∀ j : Fin W.stackCount,
      S (GaussPivotFraming32.locate j) = []) :
    ∃ t ≤ (2*unary.length+3)+
        (UnaryBinaryEncoding.coefficient+7)*(unary.length+1)^2+1+
        (2*(SourceListMachineWriter.result false unary).length+3)+1,
      ∃ c : W.Config,
        run t ⟨some (.header (.copyIn .scan)),
          eHeader (((),none),W.initial),S⟩ = result unary S c := by
  obtain ⟨a,ha,c,hlocal⟩ :=
    GaussPivotHeaderExact32.physical_exact unary S h5 h31 h30 hempty
  let c0 : GaussPivotHeader32.Config :=
    ⟨some (.copyIn .scan),(((),none),W.initial),S⟩
  have hhalt : GaussPivotHeader32.run (a+1) c0 =
      ⟨none,(((),none),W.initial),
        GaussPivotHeader32.afterOut
          (SourceListMachineWriter.result false unary)
          (GaussPivotHeaderExact32.workerResult unary S c)⟩ := by
    change ((advance GaussPivotHeader32.program)^[a+1]) c0 = _
    rw [Function.iterate_succ_apply',
      ← GaussPivotHeader32.run,hlocal]
    rfl
  obtain ⟨u,hu,hglobal⟩ :=
    GaussStepPhaseLift32.header_lift c0 (a+1)
      (by rw [hhalt])
  exact ⟨u,by omega,c,
    by simpa [BitMachineInline.cfg,hhalt,result,c0] using hglobal⟩

theorem result30 (unary : List Bool) (S : Stack → List Bool)
    (c : W.Config) (h30 : S 30 = []) :
    (result unary S c).stk 30 =
      SourceListMachineWriter.result false unary :=
  GaussPivotHeaderExact32.final30 unary S c h30

theorem result31 (unary : List Bool) (S : Stack → List Bool)
    (c : W.Config) : (result unary S c).stk 31 = [] :=
  GaussPivotHeaderExact32.final31_empty unary S c

theorem result_preserves (unary : List Bool)
    (S : Stack → List Bool) (c : W.Config) (j : Stack)
    (hj : j.val < 8 ∨ 16 ≤ j.val)
    (h5 : j ≠ 5) (h30 : j ≠ 30) (h31 : j ≠ 31) :
    (result unary S c).stk j = S j :=
  GaussPivotHeaderExact32.final_preserves unary S c j hj h5 h30 h31

#print axioms header_exact
#print axioms result30
#print axioms result_preserves

end
end CurrentAdditive.GaussStepPivotHeaderExactRun32
