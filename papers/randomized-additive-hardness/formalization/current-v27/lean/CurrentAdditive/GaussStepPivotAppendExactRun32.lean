import CurrentAdditive.GaussPivotAppendExact32

/-! Exact global append endpoint with unchanged context banks exposed. -/

namespace CurrentAdditive.GaussStepPivotAppendExactRun32

noncomputable section

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding
open CurrentAdditive.GaussStepFields32

def result (body payload : List Bool)
    (S : Stack → List Bool) : Config :=
  let c := GaussPivotAppend32.appendFrame
    (GaussPivotAppend32.afterBody body S)
    ⟨none,((),none),
      GaussPivotAppendExact32.stageTarget body payload
        (GaussPivotAppend32.afterBody body S)⟩
  ⟨some .afterAppend,eAppend ((),none),c.stk⟩

theorem append_exact (body payload : List Bool)
    (S : Stack → List Bool)
    (h23 : S 23 = body) (h26 : S 26 = payload)
    (h27 : S 27 = []) (h24 : S 24 = []) (h31 : S 31 = []) :
    ∃ t ≤ (2*body.length+3)+
        (4*body.length+2*payload.length+7)+1,
      run t ⟨some (.append (.copyBodyDirect .scan)),
        eAppend ((),none),S⟩ = result body payload S := by
  obtain ⟨a,ha,hlocal⟩ :=
    GaussPivotAppendExact32.extend_exact body payload S
      h23 h26 h27 h24 h31
  let c0 : GaussPivotAppend32.Config :=
    ⟨some (.copyBodyDirect .scan),((),none),S⟩
  let target := GaussPivotAppend32.appendFrame
    (GaussPivotAppend32.afterBody body S)
    ⟨none,((),none),
      GaussPivotAppendExact32.stageTarget body payload
        (GaussPivotAppend32.afterBody body S)⟩
  have hhalt : GaussPivotAppend32.run (a+1) c0 =
      ⟨none,((),none),target.stk⟩ := by
    change ((advance GaussPivotAppend32.program)^[a+1]) c0 = _
    rw [Function.iterate_succ_apply',
      ← GaussPivotAppend32.run,hlocal]
    rfl
  obtain ⟨u,hu,hglobal⟩ :=
    GaussStepPhaseLift32.append_lift c0 (a+1)
      (by rw [hhalt])
  refine ⟨u,by omega,?_⟩
  simpa [BitMachineInline.cfg,hhalt,result,target,c0] using hglobal

theorem result27 (body payload : List Bool)
    (S : Stack → List Bool) :
    (result body payload S).stk 27 = body++payload := by
  change (BitMachineStackEmbedding.bank
    GaussPivotAppend32.appendSlot
    (GaussPivotAppend32.afterBody body S)
    (GaussPivotAppendExact32.stageTarget body payload
      (GaussPivotAppend32.afterBody body S)))
      (GaussPivotAppend32.appendSlot
        (9:CurrentAdditive.CodeDAppendAtEnd15.Stack)) = _
  rw [BitMachineStackEmbedding.bank_at]
  simp [GaussPivotAppendExact32.stageTarget]

theorem result_preserves (body payload : List Bool)
    (S : Stack → List Bool) (j : Stack)
    (h23 : j ≠ 23) (h27 : j ≠ 27) (h31 : j ≠ 31)
    (hj : ¬ ∃ q : CurrentAdditive.CodeDAppendAtEnd15.Stack,
      GaussPivotAppend32.appendSlot q = j) :
    (result body payload S).stk j = S j := by
  exact GaussPivotAppendExact32.extend_preserves
    body payload S j h23 h27 h31 hj

theorem result24 (body payload : List Bool)
    (S : Stack → List Bool) (h24 : S 24 = []) :
    (result body payload S).stk 24 = [] := by
  change (BitMachineStackEmbedding.bank
    GaussPivotAppend32.appendSlot
    (GaussPivotAppend32.afterBody body S)
    (GaussPivotAppendExact32.stageTarget body payload
      (GaussPivotAppend32.afterBody body S)))
      (GaussPivotAppend32.appendSlot
        (11:CurrentAdditive.CodeDAppendAtEnd15.Stack)) = []
  rw [BitMachineStackEmbedding.bank_at]
  have h := SourceClausePreservingBroadcast.other_preserved
    (23 : Stack) 31 [27] body S 24
    (by decide) (by decide) (by simp)
  simp [GaussPivotAppendExact32.stageTarget,
    GaussPivotAppend32.localBank,GaussPivotAppend32.appendSlot,
    GaussPivotAppend32.afterBody,h.trans h24]

theorem result31 (body payload : List Bool)
    (S : Stack → List Bool) :
    (result body payload S).stk 31 = [] := by
  change (BitMachineStackEmbedding.bank
    GaussPivotAppend32.appendSlot
    (GaussPivotAppend32.afterBody body S)
    (GaussPivotAppendExact32.stageTarget body payload
      (GaussPivotAppend32.afterBody body S)))
      (GaussPivotAppend32.appendSlot
        (14:CurrentAdditive.CodeDAppendAtEnd15.Stack)) = []
  rw [BitMachineStackEmbedding.bank_at]
  simp [GaussPivotAppendExact32.stageTarget,
    GaussPivotAppend32.localBank,GaussPivotAppend32.appendSlot,
    GaussPivotAppend32.afterBody,
    SourceClausePreservingBroadcast.temp_empty]

#print axioms append_exact
#print axioms result27
#print axioms result_preserves
#print axioms result24
#print axioms result31

end
end CurrentAdditive.GaussStepPivotAppendExactRun32
