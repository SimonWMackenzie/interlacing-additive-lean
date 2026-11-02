import Paper2.YaoSelectorAddressJoin

/-! The selector arithmetic executes after the actual all-bank producer in
one raw finite controller. The four operands are the retained physical cells,
not separately supplied parameter certificates. -/

namespace Paper2.YaoEntryParameterJoin

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineComposition
open EthInapproximability.CurrentPaper.BitMachineSubroutine
open Paper2.YaoParameterBank
open Paper2.YaoParameterLoader
open Paper2.YaoLowerBound
open Paper2.YaoLookup

abbrev WidthLabel (t lambda : ℕ) :=
  BitMachineRawSequence.Label (FirstLabel t lambda)
    (SourceClauseFixedUnary.Label (fixedPayloadK t))
abbrev WidthControl (t lambda : ℕ) := FirstControl t lambda × Unit
abbrev LiftWidthLabel (t lambda : ℕ) := WidthLabel t lambda ⊕ Unit
abbrev LiftWidthControl (t lambda : ℕ) := WidthControl t lambda × Unit

noncomputable def widthStartLabel (t lambda : ℕ) : WidthLabel t lambda :=
  .inl (.inl (.inl (.inl (.inl (.inl ScalarA.start)))))

def widthInitialControl (t lambda : ℕ)
    (stageV0 : StageOneControl t lambda) : WidthControl t lambda :=
  (((stageV0,((),())),()),())

noncomputable def widthInitial (t lambda e z g ell p : ℕ) :=
  (⟨some (widthStartLabel t lambda),
    widthInitialControl t lambda ((frameStart t lambda e z g ell p).var,()),
    Sum.elim
      (Sum.elim (frameStart t lambda e z g ell p).stk (fun _ => []))
      (fun _ => [])⟩ :
    TM2.Cfg (fun _ : Stack t lambda => Bool)
      (WidthLabel t lambda) (WidthControl t lambda))

noncomputable def liftWidthProgram (t lambda : ℕ)
    (stageV0 : StageOneControl t lambda) : LiftWidthLabel t lambda →
      TM2.Stmt (fun _ : SelectorStack t lambda => Bool)
        (LiftWidthLabel t lambda) (LiftWidthControl t lambda)
  | .inl l => liftStmt none (program t lambda stageV0 l)
  | .inr () => .halt

noncomputable def selectorJoinedProgram (t lambda : ℕ)
    (stageV0 : StageOneControl t lambda) :=
  BitMachineRawSequence.program
    (liftWidthProgram t lambda stageV0) (selectorProgram t lambda)
    (0,.outer)
    (widthInitialControl t lambda stageV0,()) false

theorem physical_selector_single_join (t lambda e z g ell p : ℕ) :
    ∃ (a b n m widthSteps selectorSteps total : ℕ),
      a ≤ 2*e+2 + (UnaryBinaryEncoding.coefficient+6)*(e+1)^2 +
        2*paddedEdgeBits e+2 + 16*paddedEdgeCount e ∧
      b ≤ 1 + MatrixAddressMachine.exactTime (paddedEdgeCount e)
        (fixedWidth t) (fixedTail t lambda) ∧
      n ≤ a + 2*paddedEdgeCount e+2+b ∧
      m ≤ n + fixedQ t + fixedK t + 4 ∧
      widthSteps ≤ m + fixedPayloadK t + 2 ∧
      selectorSteps ≤ MatrixTemplateAddressSetup.bound
        0 0 z (fixedQ t) g (paddedEdgeBits e) ∧
      total ≤ widthSteps + selectorSteps + 1 ∧
      let f := frameRun t lambda n (frameStart t lambda e z g ell p)
      let U := Function.update
        (Function.update (Sum.elim f.stk (fun _ => [])) (.inr (0 : Fin 2))
          (List.replicate (fixedQ t) true)) (.inr (1 : Fin 2))
          (List.replicate (fixedK t) true)
      let W : Stack t lambda → List Bool :=
        Function.update (Sum.elim U (fun _ => [])) (.inr (0 : Fin 1))
          (List.replicate (fixedPayloadK t) true)
      let S : SelectorStack t lambda → List Bool := Sum.elim W (fun _ => [])
      let T := Function.update
        (Function.update S (selectorSlot t lambda 10)
          (List.replicate (z * fixedQ t + g) true))
        (selectorSlot t lambda 11)
        (List.replicate ((z * fixedQ t + g) * paddedEdgeBits e) true)
      ((advance (selectorJoinedProgram t lambda
        ((frameStart t lambda e z g ell p).var,())))^[total])
        (⟨some (.inl (.inl (widthStartLabel t lambda))),
          ((widthInitialControl t lambda
            ((frameStart t lambda e z g ell p).var,()),()),false),
          Sum.elim (widthInitial t lambda e z g ell p).stk (fun _ => [])⟩ :
          TM2.Cfg (fun _ : SelectorStack t lambda => Bool) _ _) =
        ⟨none,((widthInitialControl t lambda
          ((frameStart t lambda e z g ell p).var,()),()),false),T⟩ ∧
      T (selectorSlot t lambda 11) =
        List.replicate ((z * fixedQ t + g) * paddedEdgeBits e) true ∧
      (∀ j : Stack t lambda, T (.inl j) = W j) ∧
      T (.inl (.inl (.inl (.inl (.inr (.inl (ScalarB t lambda).input)))))) =
        List.replicate (paddedEdgeCount e) true ∧
      T (.inl (.inl (.inl (.inl (.inr (.inl (ScalarB t lambda).output)))))) =
        List.replicate (selectorCount t (paddedEdgeBits e) lambda) true ∧
      T (.inl (.inl (.inl (.inr 2)))) = List.replicate ell true ∧
      T (.inl (.inl (.inl (.inr 3)))) = List.replicate p true ∧
      T (.inl (.inl (.inl (.inl (.inl bitsCell))))) =
        List.replicate (paddedEdgeBits e) true ∧
      T (.inl (.inl (.inr 0))) = List.replicate (fixedQ t) true ∧
      T (.inl (.inr 0)) = List.replicate (fixedPayloadK t) true := by
  obtain ⟨a,b,n,m,k,ha,hb,hn,hm,hk,hrun,_,hK,hBits,hZ,hG,hQ,
    hH,hSel,hEll,hP⟩ :=
    physical_payload_width_join t lambda e z g ell p
  let c0 := widthInitial t lambda e z g ell p
  let f := frameRun t lambda n (frameStart t lambda e z g ell p)
  let U := Function.update
    (Function.update (Sum.elim f.stk (fun _ => [])) (.inr (0 : Fin 2))
      (List.replicate (fixedQ t) true)) (.inr (1 : Fin 2))
      (List.replicate (fixedK t) true)
  let W : Stack t lambda → List Bool :=
    Function.update (Sum.elim U (fun _ => [])) (.inr (0 : Fin 1))
      (List.replicate (fixedPayloadK t) true)
  let empty : Fin 8 → List Bool := fun _ => []
  let S : SelectorStack t lambda → List Bool := Sum.elim W empty
  let T := Function.update
    (Function.update S (selectorSlot t lambda 10)
      (List.replicate (z * fixedQ t + g) true))
    (selectorSlot t lambda 11)
    (List.replicate ((z * fixedQ t + g) * paddedEdgeBits e) true)
  let stageV0 : StageOneControl t lambda :=
    ((frameStart t lambda e z g ell p).var,())
  let widthV0 := widthInitialControl t lambda stageV0
  have hrun' : ((advance (program t lambda stageV0))^[k]) c0 =
      ⟨none,widthV0,W⟩ := by
    simpa only [c0, widthInitial, stageV0, widthStartLabel,
      widthInitialControl, f, U, W] using hrun
  have hhalt : (((advance (program t lambda stageV0))^[k]) c0).l = none := by
    rw [hrun']
  obtain ⟨i,hi,hA⟩ := lift_outputs
    (program t lambda stageV0) (liftWidthProgram t lambda stageV0)
    none (by intro l; rfl) () empty c0 k hhalt
  have hA' : ((advance (liftWidthProgram t lambda stageV0))^[i])
      (⟨some (.inl (widthStartLabel t lambda)),(widthV0,()),
        Sum.elim c0.stk empty⟩ :
        TM2.Cfg (fun _ : SelectorStack t lambda => Bool)
          (LiftWidthLabel t lambda) (LiftWidthControl t lambda)) =
      ⟨none,(widthV0,()),S⟩ := by
    rw [hrun'] at hA
    simpa only [liftCfg, c0, widthInitial, S, Option.map_none] using hA
  obtain ⟨j,hj,hB⟩ := selector_address_phase t lambda e z g W
    hBits hZ hG hQ
  have hB' : ((advance (selectorProgram t lambda))^[j])
      (⟨some (0,.outer),false,S⟩ :
        TM2.Cfg (fun _ : SelectorStack t lambda => Bool)
          MatrixTemplateAddressSetup.Label Bool) =
      ⟨none,false,T⟩ := by
    simpa only [S,T,empty] using hB
  obtain ⟨total,htotal,hjoined⟩ := BitMachineRawSequence.runs
    (liftWidthProgram t lambda stageV0) (selectorProgram t lambda)
    (.inl (widthStartLabel t lambda)) (0,.outer)
    (widthV0,()) (widthV0,()) false false
    (Sum.elim c0.stk empty) S T i j hA' hB'
  have hkeep (x : Stack t lambda) : T (.inl x) = W x := by
    change (Function.update
      (Function.update S (selectorSlot t lambda 10)
        (List.replicate (z * fixedQ t + g) true))
      (selectorSlot t lambda 11)
      (List.replicate ((z * fixedQ t + g) * paddedEdgeBits e) true)) (.inl x) = W x
    rw [Function.update_of_ne (by simp [selectorSlot]),
      Function.update_of_ne (by simp [selectorSlot])]
    rfl
  refine ⟨a,b,n,m,k,j,total,ha,hb,hn,hm,hk,hj,by omega,?_⟩
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [selectorJoinedProgram, stageV0, widthV0,
      c0, f, U, W, S, T, empty,
      BitMachineRawSequence.leftLabel] using hjoined
  · change T (selectorSlot t lambda 11) = _
    simp [T]
  · exact hkeep
  · change T (.inl (.inl (.inl (.inl (.inr (.inl (ScalarB t lambda).input)))))) = _
    rw [hkeep]
    exact hH
  · change T (.inl (.inl (.inl (.inl (.inr (.inl (ScalarB t lambda).output)))))) = _
    rw [hkeep]
    exact hSel
  · change T (.inl (.inl (.inl (.inr 2)))) = _
    rw [hkeep]
    exact hEll
  · change T (.inl (.inl (.inl (.inr 3)))) = _
    rw [hkeep]
    exact hP
  · change T (.inl (.inl (.inl (.inl (.inl bitsCell))))) = _
    rw [hkeep]
    exact hBits
  · change T (.inl (.inl (.inr 0))) = _
    rw [hkeep]
    exact hQ
  · change T (.inl (.inr 0)) = _
    rw [hkeep]
    exact hK

#print axioms physical_selector_single_join

end Paper2.YaoEntryParameterJoin
