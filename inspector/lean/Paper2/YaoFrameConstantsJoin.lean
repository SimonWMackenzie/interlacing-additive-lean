import Paper2.YaoFixedScalars

/-! One raw finite-control program joins the exact all-bank edge/label frame
to two fixed-t unary writers. The arithmetic address phase remains separate.
-/

namespace Paper2.YaoParameterBank

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineSubroutine
open EthInapproximability.CurrentPaper.BitMachineComposition
open Paper2.YaoParameterLoader
open Paper2.YaoLowerBound
open Paper2.YaoLookup

abbrev JoinedStack (t lambda : ℕ) := FrameStack t lambda ⊕ Fin 2
abbrev StageOneLabel (t lambda : ℕ) := FrameLabel t lambda ⊕ Unit
abbrev StageOneControl (t lambda : ℕ) := FrameControl t lambda × Unit

noncomputable def stageOneProgram (t lambda : ℕ) :
    StageOneLabel t lambda →
      TM2.Stmt (fun _ : JoinedStack t lambda => Bool)
        (StageOneLabel t lambda) (StageOneControl t lambda)
  | .inl l => liftStmt none (frameProgram t lambda l)
  | .inr () => .halt

noncomputable def constantsOn (t lambda : ℕ) :=
  BitMachineRawSequence.program
    (SourceClauseFixedUnary.program (.inr (0 : Fin 2) : JoinedStack t lambda) (fixedQ t))
    (SourceClauseFixedUnary.program (.inr (1 : Fin 2) : JoinedStack t lambda) (fixedK t))
    (0 : SourceClauseFixedUnary.Label (fixedK t)) () ()

noncomputable def joinedProgram (t lambda : ℕ) (v0 : StageOneControl t lambda) :=
  BitMachineRawSequence.program
    (stageOneProgram t lambda) (constantsOn t lambda)
    (.inl (0 : SourceClauseFixedUnary.Label (fixedQ t)))
    v0 ((),())

theorem frame_constants_join (t lambda e z g ell p : ℕ) :
    ∃ (a b frameSteps total : ℕ),
      a ≤ 2*e+2 + (UnaryBinaryEncoding.coefficient+6)*(e+1)^2 +
        2*paddedEdgeBits e+2 + 16*paddedEdgeCount e ∧
      b ≤ 1 + MatrixAddressMachine.exactTime (paddedEdgeCount e)
        (fixedWidth t) (fixedTail t lambda) ∧
      frameSteps ≤ a + 2*paddedEdgeCount e+2+b ∧
      total ≤ frameSteps + fixedQ t + fixedK t + 4 ∧
      let f := frameRun t lambda frameSteps
        (frameStart t lambda e z g ell p)
      let S : JoinedStack t lambda → List Bool :=
        Sum.elim f.stk (fun _ => [])
      let U := Function.update (Function.update S (.inr (0 : Fin 2))
        (List.replicate (fixedQ t) true)) (.inr (1 : Fin 2))
        (List.replicate (fixedK t) true)
      ((advance (joinedProgram t lambda
        ((frameStart t lambda e z g ell p).var,())))^[total])
        (⟨some (.inl (.inl (.inl (.inl ScalarA.start)))),
          (((frameStart t lambda e z g ell p).var,()),((),())),
          Sum.elim (frameStart t lambda e z g ell p).stk (fun _ => [])⟩ :
          TM2.Cfg (fun _ : JoinedStack t lambda => Bool) _ _) =
        ⟨none, (((frameStart t lambda e z g ell p).var,()),((),())), U⟩ ∧
      U (.inl (.inl (.inl edgeCell))) = List.replicate e true ∧
      U (.inl (.inl (.inl bitsCell))) =
        List.replicate (paddedEdgeBits e) true ∧
      U (.inl (.inl (.inr (.inl (ScalarB t lambda).input)))) =
        List.replicate (paddedEdgeCount e) true ∧
      U (.inl (.inl (.inr (.inl (ScalarB t lambda).output)))) =
        List.replicate (selectorCount t (paddedEdgeBits e) lambda) true ∧
      (∀ j : Fin 4, U (.inl (.inr j)) = (labelBanks z g ell p) j) ∧
      U (.inr 0) = List.replicate (fixedQ t) true ∧
      U (.inr 1) = List.replicate (fixedK t) true := by
  obtain ⟨a,b,n,ha,hb,hn,_,hhalt,hE,hBits,hH,hSel,hLabels⟩ :=
    framed_four_banks t lambda e z g ell p
  let c0 := frameStart t lambda e z g ell p
  let f := frameRun t lambda n c0
  let empty : Fin 2 → List Bool := fun _ => []
  let S : JoinedStack t lambda → List Bool := Sum.elim f.stk empty
  let U := Function.update (Function.update S (.inr (0 : Fin 2))
    (List.replicate (fixedQ t) true)) (.inr (1 : Fin 2))
    (List.replicate (fixedK t) true)
  obtain ⟨m,hm,hA⟩ := lift_outputs
    (frameProgram t lambda) (stageOneProgram t lambda) none
    (by intro l; rfl) () empty c0 n hhalt
  have hc0label : c0.l = some (.inl (.inl ScalarA.start)) := by rfl
  have hflabel : f.l = none := hhalt
  have hA0 : ((advance (stageOneProgram t lambda))^[m])
      (liftCfg none () empty c0) = liftCfg none () empty f := by
    simpa only [f, frameRun] using hA
  have hA' : ((advance (stageOneProgram t lambda))^[m])
      (⟨some (.inl (.inl (.inl ScalarA.start))), (c0.var,()),
        Sum.elim c0.stk empty⟩ : TM2.Cfg (fun _ : JoinedStack t lambda => Bool)
          (StageOneLabel t lambda) (StageOneControl t lambda)) =
      ⟨none, (f.var,()), S⟩ := by
    simpa only [liftCfg, hc0label, hflabel, S, Option.map_none] using hA0
  obtain ⟨k,hk,hB⟩ := fixed_Q_K_ambient t
    (.inr (0 : Fin 2) : JoinedStack t lambda)
    (.inr (1 : Fin 2) : JoinedStack t lambda)
    (by simp) S (by rfl) (by rfl)
  obtain ⟨total,htotal,hrun⟩ := BitMachineRawSequence.runs
    (stageOneProgram t lambda) (constantsOn t lambda)
    (.inl (.inl (.inl ScalarA.start)))
    (.inl (0 : SourceClauseFixedUnary.Label (fixedQ t)))
    (c0.var,()) (f.var,()) ((),()) ((),())
    (Sum.elim c0.stk empty) S U m k hA' hB
  refine ⟨a,b,n,total,ha,hb,hn,by omega,?_⟩
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [joinedProgram, c0, f, S, U, empty,
      BitMachineRawSequence.leftLabel] using hrun
  · simpa [U, S, Function.update] using hE
  · simpa [U, S, Function.update] using hBits
  · simpa [U, S, Function.update] using hH
  · simpa [U, S, Function.update] using hSel
  · intro j
    simpa [U, S, Function.update] using hLabels j
  · simp [Function.update]
  · simp [Function.update]

#print axioms frame_constants_join

end Paper2.YaoParameterBank
