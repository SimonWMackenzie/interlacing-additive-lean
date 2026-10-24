import CurrentAdditive.GaussPivotPairToFinish32
import CurrentAdditive.GaussStepPivotSplitRun32

/-! The fixed Fin32 pivot writer consumes the stored V2 pivot list, strips
its count header, appends the selected pivot, and emits the exact Bank4 state. -/

namespace CurrentAdditive.GaussPivotSplitToFinish32

noncomputable section

open EthInapproximability.CurrentPaper
open CurrentAdditive.GaussStepFields32

theorem split_to_packet {m k : Nat}
    (B' : Fin m → Fin k → ℚ) (c : Nat)
    (ps : List (Fin m × Fin k)) (p : Fin m × Fin k)
    (S : Stack → List Bool)
    (h4 : S 4 = GaussPhysical.encodeTypedMatrix B')
    (h5 : S 5 = List.replicate (ps ++ [p]).length true)
    (h6 : S 6 = List.replicate c true)
    (h17 : S 17 = List.replicate p.1.val true)
    (h18 : S 18 = List.replicate p.2.val true)
    (h19 : S 19 = GaussControlTrace.pivotsPacket ps)
    (h23 : S 23 = []) (h24 : S 24 = [])
    (h25 : S 25 = []) (h26 : S 26 = [])
    (h27 : S 27 = []) (h28 : S 28 = [])
    (h29 : S 29 = []) (h30 : S 30 = []) (h31 : S 31 = [])
    (hempty : ∀ j : Fin
      (SourceListMachineWriter.framingMachine true).stackCount,
      S (GaussPivotFraming32.locate j) = []) :
    ∃ t,
      (run t ⟨some (.split (.copy .scan)),
        eSplit (((),none),(none,none)),S⟩).l = some .done ∧
      (run t ⟨some (.split (.copy .scan)),
        eSplit (((),none),(none,none)),S⟩).stk 14 =
        GaussControlTrace.statePacket
          (⟨B',(ps ++ [p]).length,c,ps ++ [p]⟩ :
            GaussControlTrace.State m k) := by
  let start : Config :=
    ⟨some (.split (.copy .scan)),eSplit (((),none),(none,none)),S⟩
  obtain ⟨a,ha,v,hsplit⟩ :=
    GaussStepPivotSplitRun32.split_phase ps S h19 h23 h24 h25 h31
  let C := GaussStepPivotSplitRun32.result ps S v
  have hrunC : run a start = C := hsplit
  have hnext : run 1 C =
      ⟨some (.pair (.inl (.emit 0))),ePair none,C.stk⟩ := by
    change run 1 (GaussStepPivotSplitRun32.result ps S v) = _
    rfl
  have hpres (j : Stack) (h19' : j ≠ 19) (h23' : j ≠ 23)
      (h24' : j ≠ 24) (h25' : j ≠ 25) (h31' : j ≠ 31) :
      C.stk j = S j :=
    GaussStepPivotSplitRun32.result_preserves ps S v j
      h19' h23' h24' h25' h31'
  have h4C : C.stk 4 = GaussPhysical.encodeTypedMatrix B' :=
    (hpres 4 (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans h4
  have h5C : C.stk 5 = List.replicate (ps ++ [p]).length true :=
    (hpres 5 (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans h5
  have h6C : C.stk 6 = List.replicate c true :=
    (hpres 6 (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans h6
  have h17C : C.stk 17 = List.replicate p.1.val true :=
    (hpres 17 (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans h17
  have h18C : C.stk 18 = List.replicate p.2.val true :=
    (hpres 18 (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans h18
  have h23C : C.stk 23 = SourceListEncoding.fields
      (ps.map GaussControlTrace.pivotPacket) :=
    GaussStepPivotSplitRun32.result_body ps S v
  have h24C : C.stk 24 = [] :=
    GaussStepPivotSplitRun32.result24_empty ps S v
  have h26C : C.stk 26 = [] :=
    (hpres 26 (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans h26
  have h27C : C.stk 27 = [] :=
    (hpres 27 (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans h27
  have h28C : C.stk 28 = [] :=
    (hpres 28 (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans h28
  have h29C : C.stk 29 = [] :=
    (hpres 29 (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans h29
  have h30C : C.stk 30 = [] :=
    (hpres 30 (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans h30
  have h31C : C.stk 31 = [] :=
    GaussStepPivotSplitRun32.result31_empty ps S v
  have hemptyC : ∀ j : Fin
      (SourceListMachineWriter.framingMachine true).stackCount,
      C.stk (GaussPivotFraming32.locate j) = [] := by
    intro j
    rw [hpres (GaussPivotFraming32.locate j)
      (by fin_cases j <;> decide)
      (by fin_cases j <;> decide)
      (by fin_cases j <;> decide)
      (by fin_cases j <;> decide)
      (by fin_cases j <;> decide)]
    exact hempty j
  obtain ⟨b,hend,hpacket⟩ :=
    GaussPivotPairToFinish32.pair_to_packet B' c ps p C.stk
      h4C h5C h6C h23C h24C h26C h27C
      h17C h18C h28C h29C h30C h31C hemptyC
  refine ⟨a+1+b, ?_, ?_⟩
  · rw [show a+1+b = a+(1+b) by omega,
      run_add hrunC (1+b),run_add hnext b]
    exact hend
  · rw [show a+1+b = a+(1+b) by omega,
      run_add hrunC (1+b),run_add hnext b]
    exact hpacket

#print axioms split_to_packet

end
end CurrentAdditive.GaussPivotSplitToFinish32
