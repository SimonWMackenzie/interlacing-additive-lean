import Paper2.YaoFrameConstantsJoin

/-! One more charged fixed-control phase physically writes payload cell width
`K=2^t*2^t` while retaining the actual preceding scalar bank. -/

namespace Paper2.YaoEntryParameterJoin

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineSubroutine
open EthInapproximability.CurrentPaper.BitMachineComposition
open Paper2.YaoParameterBank
open Paper2.YaoParameterLoader
open Paper2.YaoLowerBound
open Paper2.YaoLookup

abbrev BaseLabel (t lambda : ℕ) :=
  BitMachineRawSequence.Label (StageOneLabel t lambda) (ConstantLabel t)
abbrev BaseControl (t lambda : ℕ) := StageOneControl t lambda × ConstantControl
abbrev Stack (t lambda : ℕ) := JoinedStack t lambda ⊕ Fin 1
abbrev FirstLabel (t lambda : ℕ) := BaseLabel t lambda ⊕ Unit
abbrev FirstControl (t lambda : ℕ) := BaseControl t lambda × Unit

noncomputable def firstProgram (t lambda : ℕ)
    (v0 : StageOneControl t lambda) : FirstLabel t lambda →
      TM2.Stmt (fun _ : Stack t lambda => Bool)
        (FirstLabel t lambda) (FirstControl t lambda)
  | .inl l => liftStmt none (joinedProgram t lambda v0 l)
  | .inr () => .halt

noncomputable def program (t lambda : ℕ)
    (v0 : StageOneControl t lambda) :=
  BitMachineRawSequence.program (firstProgram t lambda v0)
    (SourceClauseFixedUnary.program (.inr (0 : Fin 1) : Stack t lambda)
      (fixedPayloadK t))
    (0 : SourceClauseFixedUnary.Label (fixedPayloadK t))
    ((v0,((),())),()) ()

theorem physical_payload_width_join (t lambda e z g ell p : ℕ) :
    ∃ (a b frameSteps priorSteps total : ℕ),
      a ≤ 2*e+2 + (UnaryBinaryEncoding.coefficient+6)*(e+1)^2 +
        2*paddedEdgeBits e+2 + 16*paddedEdgeCount e ∧
      b ≤ 1 + MatrixAddressMachine.exactTime (paddedEdgeCount e)
        (fixedWidth t) (fixedTail t lambda) ∧
      frameSteps ≤ a + 2*paddedEdgeCount e+2+b ∧
      priorSteps ≤ frameSteps + fixedQ t + fixedK t + 4 ∧
      total ≤ priorSteps + fixedPayloadK t + 2 ∧
      let f := frameRun t lambda frameSteps
        (frameStart t lambda e z g ell p)
      let S : JoinedStack t lambda → List Bool := Sum.elim f.stk (fun _ => [])
      let U := Function.update (Function.update S (.inr (0 : Fin 2))
        (List.replicate (fixedQ t) true)) (.inr (1 : Fin 2))
        (List.replicate (fixedK t) true)
      let V : Stack t lambda → List Bool := Sum.elim U (fun _ => [])
      let W := Function.update V (.inr (0 : Fin 1))
        (List.replicate (fixedPayloadK t) true)
      ((advance (program t lambda
        ((frameStart t lambda e z g ell p).var,())))^[total])
        (⟨some (.inl (.inl (.inl (.inl (.inl (.inl ScalarA.start)))))),
          (((((frameStart t lambda e z g ell p).var,()),((),())),()),()),
          Sum.elim
            (Sum.elim (frameStart t lambda e z g ell p).stk (fun _ => []))
            (fun _ => [])⟩ : TM2.Cfg (fun _ : Stack t lambda => Bool) _ _) =
        ⟨none, (((((frameStart t lambda e z g ell p).var,()),((),())),()),()), W⟩ ∧
      (∀ j : JoinedStack t lambda, W (.inl j) = U j) ∧
      W (.inr 0) = List.replicate (fixedPayloadK t) true ∧
      W (.inl (.inl (.inl (.inl bitsCell)))) =
        List.replicate (paddedEdgeBits e) true ∧
      W (.inl (.inl (.inr 0))) = List.replicate z true ∧
      W (.inl (.inl (.inr 1))) = List.replicate g true ∧
      W (.inl (.inr 0)) = List.replicate (fixedQ t) true ∧
      W (.inl (.inl (.inl (.inr (.inl (ScalarB t lambda).input))))) =
        List.replicate (paddedEdgeCount e) true ∧
      W (.inl (.inl (.inl (.inr (.inl (ScalarB t lambda).output))))) =
        List.replicate (selectorCount t (paddedEdgeBits e) lambda) true ∧
      W (.inl (.inl (.inr 2))) = List.replicate ell true ∧
      W (.inl (.inl (.inr 3))) = List.replicate p true := by
  obtain ⟨a,b,n,m,ha,hb,hn,hm,hrun,_,hBits,hH,hSel,hLabels,hQ,_⟩ :=
    frame_constants_join t lambda e z g ell p
  let c0 := frameStart t lambda e z g ell p
  let f := frameRun t lambda n c0
  let U : JoinedStack t lambda → List Bool :=
    Function.update
      (Function.update (Sum.elim f.stk (fun _ => [])) (.inr (0 : Fin 2))
        (List.replicate (fixedQ t) true)) (.inr (1 : Fin 2))
        (List.replicate (fixedK t) true)
  let empty : Fin 1 → List Bool := fun _ => []
  let V : Stack t lambda → List Bool := Sum.elim U empty
  let W := Function.update V (.inr (0 : Fin 1))
    (List.replicate (fixedPayloadK t) true)
  let v0 : StageOneControl t lambda := (c0.var,())
  have hhalt :
      (((advance (joinedProgram t lambda v0))^[m])
        (⟨some (.inl (.inl (.inl (.inl ScalarA.start)))),
          (v0,((),())), Sum.elim c0.stk (fun _ => [])⟩ :
          TM2.Cfg (fun _ : JoinedStack t lambda => Bool)
            (BaseLabel t lambda) (BaseControl t lambda))).l = none := by
    rw [hrun]
  obtain ⟨j,hj,hA⟩ := lift_outputs
    (joinedProgram t lambda v0) (firstProgram t lambda v0) none
    (by intro l; rfl) () empty
    (⟨some (.inl (.inl (.inl (.inl ScalarA.start)))),
      (v0,((),())), Sum.elim c0.stk (fun _ => [])⟩ :
      TM2.Cfg (fun _ : JoinedStack t lambda => Bool)
        (BaseLabel t lambda) (BaseControl t lambda)) m hhalt
  rw [hrun] at hA
  have hA' : ((advance (firstProgram t lambda v0))^[j])
      (⟨some (.inl (.inl (.inl (.inl (.inl ScalarA.start))))),
        ((v0,((),())),()),
        Sum.elim (Sum.elim c0.stk (fun _ => [])) empty⟩ :
        TM2.Cfg (fun _ : Stack t lambda => Bool)
          (FirstLabel t lambda) (FirstControl t lambda)) =
      ⟨none, (((v0,((),())),())), V⟩ := by
    simpa only [liftCfg, V, empty, Option.map_none] using hA
  have hB := SourceClauseFixedUnary.run
    (.inr (0 : Fin 1) : Stack t lambda) V (fixedPayloadK t) (by rfl)
  obtain ⟨total,htotal,hjoined⟩ := BitMachineRawSequence.runs
    (firstProgram t lambda v0)
    (SourceClauseFixedUnary.program (.inr (0 : Fin 1) : Stack t lambda)
      (fixedPayloadK t))
    (.inl (.inl (.inl (.inl (.inl ScalarA.start)))))
    (0 : SourceClauseFixedUnary.Label (fixedPayloadK t))
    ((v0,((),())),()) ((v0,((),())),()) () ()
    (Sum.elim (Sum.elim c0.stk (fun _ => [])) empty)
    V W j (fixedPayloadK t + 1) hA' hB
  have hpres (k : JoinedStack t lambda) : W (.inl k) = U k := by
    change (Function.update V (.inr (0 : Fin 1))
      (List.replicate (fixedPayloadK t) true)) (.inl k) = U k
    rw [Function.update_of_ne (by simp)]
    rfl
  refine ⟨a,b,n,m,total,ha,hb,hn,hm,by omega,?_⟩
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [program, c0, f, U, V, W, empty, v0,
      BitMachineRawSequence.leftLabel] using hjoined
  · exact hpres
  · change (Function.update V (.inr (0 : Fin 1))
      (List.replicate (fixedPayloadK t) true)) (.inr 0) = _
    exact Function.update_self _ _ _
  · change W (.inl (.inl (.inl (.inl bitsCell)))) = _
    rw [hpres]
    exact hBits
  · change W (.inl (.inl (.inr 0))) = _
    rw [hpres]
    simpa only [labelBanks, Matrix.cons_val_zero] using hLabels 0
  · change W (.inl (.inl (.inr 1))) = _
    rw [hpres]
    have hg : labelBanks z g ell p 1 = List.replicate g true := rfl
    exact (hLabels 1).trans hg
  · change W (.inl (.inr 0)) = _
    rw [hpres]
    exact hQ
  · change W (.inl (.inl (.inl (.inr (.inl (ScalarB t lambda).input))))) = _
    rw [hpres]
    exact hH
  · change W (.inl (.inl (.inl (.inr (.inl (ScalarB t lambda).output))))) = _
    rw [hpres]
    exact hSel
  · change W (.inl (.inl (.inr 2))) = _
    rw [hpres]
    have he : labelBanks z g ell p 2 = List.replicate ell true := rfl
    exact (hLabels 2).trans he
  · change W (.inl (.inl (.inr 3))) = _
    rw [hpres]
    have hp : labelBanks z g ell p 3 = List.replicate p true := rfl
    exact (hLabels 3).trans hp

#print axioms physical_payload_width_join

end Paper2.YaoEntryParameterJoin
