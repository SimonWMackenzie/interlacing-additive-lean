import Paper2.YaoPayloadBasePhase

/-! One literal finite-controller from basic unary e,z,g,ell,position to
both Yao offsets, count H, and stride. It composes the physical selector
controller with the four-pass payload arithmetic on untouched source banks.
Routing into `EntryCombined.entryInput` remains separate. -/

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

abbrev SelectorLabel (t lambda : ℕ) :=
  BitMachineRawSequence.Label (LiftWidthLabel t lambda)
    MatrixTemplateAddressSetup.Label
abbrev SelectorControl (t lambda : ℕ) := LiftWidthControl t lambda × Bool
abbrev LiftSelectorLabel (t lambda : ℕ) := SelectorLabel t lambda ⊕ Unit
abbrev LiftSelectorControl (t lambda : ℕ) := SelectorControl t lambda × Unit

noncomputable def selectorInitial (t lambda e z g ell p : ℕ) :
    TM2.Cfg (fun _ : SelectorStack t lambda => Bool)
      (SelectorLabel t lambda) (SelectorControl t lambda) :=
  let stageV0 : StageOneControl t lambda :=
    ((frameStart t lambda e z g ell p).var,())
  ⟨some (.inl (.inl (widthStartLabel t lambda))),
    ((widthInitialControl t lambda stageV0,()),false),
    Sum.elim (widthInitial t lambda e z g ell p).stk (fun _ => [])⟩

noncomputable def liftSelectorProgram (t lambda : ℕ)
    (stageV0 : StageOneControl t lambda) : LiftSelectorLabel t lambda →
      TM2.Stmt (fun _ : PayloadStack t lambda => Bool)
        (LiftSelectorLabel t lambda) (LiftSelectorControl t lambda)
  | .inl l => liftStmt none (selectorJoinedProgram t lambda stageV0 l)
  | .inr () => .halt

noncomputable def fullScalarProgram (t lambda : ℕ)
    (stageV0 : StageOneControl t lambda)
    (v0 : SelectorControl t lambda) :=
  BitMachineRawSequence.program
    (liftSelectorProgram t lambda stageV0) (payloadProgram t lambda)
    (0,.outer) (v0,()) false

theorem physical_full_scalar_join (t lambda e z g ell p : ℕ) :
    ∃ (a b n m widthSteps selectorSteps scalarSteps payloadSteps total : ℕ),
      a ≤ 2*e+2 + (UnaryBinaryEncoding.coefficient+6)*(e+1)^2 +
        2*paddedEdgeBits e+2 + 16*paddedEdgeCount e ∧
      b ≤ 1 + MatrixAddressMachine.exactTime (paddedEdgeCount e)
        (fixedWidth t) (fixedTail t lambda) ∧
      n ≤ a + 2*paddedEdgeCount e+2+b ∧
      m ≤ n + fixedQ t + fixedK t + 4 ∧
      widthSteps ≤ m + fixedPayloadK t + 2 ∧
      selectorSteps ≤ MatrixTemplateAddressSetup.bound
        0 0 z (fixedQ t) g (paddedEdgeBits e) ∧
      scalarSteps ≤ widthSteps + selectorSteps + 1 ∧
      payloadSteps ≤
        MatrixAddressMachine.exactTime (paddedEdgeCount e) (fixedK t) 0 +
        MatrixAddressMachine.exactTime ell (paddedEdgeCount e * fixedK t) p +
        MatrixAddressMachine.exactTime
          (selectorCount t (paddedEdgeBits e) lambda) (fixedQ t) 0 +
        MatrixAddressMachine.exactTime
          (selectorCount t (paddedEdgeBits e) lambda * fixedQ t)
          (paddedEdgeBits e)
          (ell * (paddedEdgeCount e * fixedK t) + p) ∧
      total ≤ scalarSteps + payloadSteps + 1 ∧
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
      let R₀ : PayloadStack t lambda → List Bool := Sum.elim T (fun _ => [])
      let R₁ := Function.update R₀ (fresh t lambda 3)
        (List.replicate (paddedEdgeCount e * fixedK t) true)
      let R₂ := Function.update R₁ (fresh t lambda 4)
        (List.replicate (ell * (paddedEdgeCount e * fixedK t) + p) true)
      let R₃ := Function.update R₂ (fresh t lambda 5)
        (List.replicate
          (selectorCount t (paddedEdgeBits e) lambda * fixedQ t) true)
      let R₄ := Function.update R₃ (fresh t lambda 6)
        (List.replicate (payloadBaseValue t lambda e ell p) true)
      ((advance (fullScalarProgram t lambda
        ((frameStart t lambda e z g ell p).var,())
        (selectorInitial t lambda e z g ell p).var))^[total])
        (⟨some (.inl (.inl (.inl (.inl (widthStartLabel t lambda))))),
          (((selectorInitial t lambda e z g ell p).var,()),false),
          Sum.elim (selectorInitial t lambda e z g ell p).stk (fun _ => [])⟩ :
          TM2.Cfg (fun _ : PayloadStack t lambda => Bool) _ _) =
        ⟨none,(((selectorInitial t lambda e z g ell p).var,()),false),R₄⟩ ∧
      R₄ (fresh t lambda 6) =
        List.replicate (payloadBaseValue t lambda e ell p) true ∧
      R₄ (.inl (selectorSlot t lambda 11)) =
        List.replicate ((z * fixedQ t + g) * paddedEdgeBits e) true ∧
      R₄ (bCell t lambda) = List.replicate (paddedEdgeBits e) true ∧
      R₄ (strideCell t lambda) = List.replicate (fixedK t) true ∧
      R₄ (hCell t lambda) = List.replicate (paddedEdgeCount e) true := by
  obtain ⟨a,b,n,m,w,s,j,ha,hb,hn,hm,hw,hs,hj,hrun,hOffset,hRetain,
    hH,hCount,hEll,hP,hB,hQ,hK⟩ :=
    physical_selector_single_join t lambda e z g ell p
  let c0 := selectorInitial t lambda e z g ell p
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
  let empty : Fin 7 → List Bool := fun _ => []
  let R₀ : PayloadStack t lambda → List Bool := Sum.elim T empty
  let R₁ := Function.update R₀ (fresh t lambda 3)
    (List.replicate (paddedEdgeCount e * fixedK t) true)
  let R₂ := Function.update R₁ (fresh t lambda 4)
    (List.replicate (ell * (paddedEdgeCount e * fixedK t) + p) true)
  let R₃ := Function.update R₂ (fresh t lambda 5)
    (List.replicate (selectorCount t (paddedEdgeBits e) lambda * fixedQ t) true)
  let R₄ := Function.update R₃ (fresh t lambda 6)
    (List.replicate (payloadBaseValue t lambda e ell p) true)
  let stageV0 : StageOneControl t lambda :=
    ((frameStart t lambda e z g ell p).var,())
  have hrun' : ((advance (selectorJoinedProgram t lambda stageV0))^[j]) c0 =
      ⟨none,c0.var,T⟩ := by
    simpa only [c0,selectorInitial,stageV0,f,U,W,S,T] using hrun
  have hhalt : (((advance (selectorJoinedProgram t lambda stageV0))^[j]) c0).l = none := by
    rw [hrun']
  obtain ⟨i,hi,hA⟩ := lift_outputs
    (selectorJoinedProgram t lambda stageV0)
    (liftSelectorProgram t lambda stageV0) none
    (by intro l; rfl) () empty c0 j hhalt
  have hlabel : c0.l = some (.inl (.inl (widthStartLabel t lambda))) := rfl
  have hA' : ((advance (liftSelectorProgram t lambda stageV0))^[i])
      (⟨some (.inl (.inl (.inl (widthStartLabel t lambda)))),(c0.var,()),
        Sum.elim c0.stk empty⟩ :
        TM2.Cfg (fun _ : PayloadStack t lambda => Bool)
          (LiftSelectorLabel t lambda) (LiftSelectorControl t lambda)) =
      ⟨none,(c0.var,()),R₀⟩ := by
    rw [hrun'] at hA
    simpa only [liftCfg,hlabel,R₀,Option.map_none] using hA
  have hH' : R₀ (hCell t lambda) = List.replicate (paddedEdgeCount e) true := by
    simpa only [R₀,hCell,fromJoined] using hH
  have hW : W (.inl (.inr (1 : Fin 2))) =
      List.replicate (fixedK t) true := by
    change (Function.update (Sum.elim U (fun _ => [])) (.inr (0 : Fin 1))
      (List.replicate (fixedPayloadK t) true)) (.inl (.inr 1)) = _
    rw [Function.update_of_ne (by simp)]
    change U (.inr 1) = _
    simp only [U, Function.update_self]
  have hK' : R₀ (strideCell t lambda) = List.replicate (fixedK t) true := by
    have hRetained := hRetain (.inl (.inr (1 : Fin 2)))
    simpa only [R₀,strideCell,fromJoined] using
      hRetained.trans hW
  have hCount' : R₀ (countCell t lambda) =
      List.replicate (selectorCount t (paddedEdgeBits e) lambda) true := by
    simpa only [R₀,countCell,fromJoined] using hCount
  have hEll' : R₀ (ellCell t lambda) = List.replicate ell true := by
    simpa only [R₀,ellCell,fromJoined] using hEll
  have hP' : R₀ (positionCell t lambda) = List.replicate p true := by
    simpa only [R₀,positionCell,fromJoined] using hP
  have hB' : R₀ (bCell t lambda) = List.replicate (paddedEdgeBits e) true := by
    simpa only [R₀,bCell,fromJoined] using hB
  have hQ' : R₀ (qCell t lambda) = List.replicate (fixedQ t) true := by
    simpa only [R₀,qCell,fromJoined] using hQ
  obtain ⟨k,hk,hPayload,hBase⟩ := physical_payload_base_phase
    t lambda e ell p R₀ hH' hK' hEll' hP' hCount' hQ' hB'
    (by intro x; rfl)
  have hPayload' : ((advance (payloadProgram t lambda))^[k])
      (⟨some (0,.outer),false,R₀⟩ : PayloadConfig t lambda) =
      ⟨none,false,R₄⟩ := by
    simpa only [payloadRun,R₀,R₁,R₂,R₃,R₄] using hPayload
  obtain ⟨total,htotal,hjoined⟩ := BitMachineRawSequence.runs
    (liftSelectorProgram t lambda stageV0) (payloadProgram t lambda)
    (.inl (.inl (.inl (widthStartLabel t lambda)))) (0,.outer)
    (c0.var,()) (c0.var,()) false false
    (Sum.elim c0.stk empty) R₀ R₄ i k hA' hPayload'
  have hkeep (x : SelectorStack t lambda) : R₄ (.inl x) = T x := by
    change (Function.update R₃ (fresh t lambda 6)
      (List.replicate (payloadBaseValue t lambda e ell p) true)) (.inl x) = T x
    rw [Function.update_of_ne (by simp [fresh])]
    change (Function.update R₂ (fresh t lambda 5)
      (List.replicate
        (selectorCount t (paddedEdgeBits e) lambda * fixedQ t) true)) (.inl x) = T x
    rw [Function.update_of_ne (by simp [fresh])]
    change (Function.update R₁ (fresh t lambda 4)
      (List.replicate (ell * (paddedEdgeCount e * fixedK t) + p) true))
      (.inl x) = T x
    rw [Function.update_of_ne (by simp [fresh])]
    change (Function.update R₀ (fresh t lambda 3)
      (List.replicate (paddedEdgeCount e * fixedK t) true))
      (.inl x) = T x
    rw [Function.update_of_ne (by simp [fresh])]
    rfl
  refine ⟨a,b,n,m,w,s,j,k,total,ha,hb,hn,hm,hw,hs,hj,hk,by omega,?_⟩
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [fullScalarProgram,c0,stageV0,R₀,R₁,R₂,R₃,R₄,
      f,U,W,S,T,empty,BitMachineRawSequence.leftLabel,hlabel] using hjoined
  · exact hBase
  · change R₄ (.inl (selectorSlot t lambda 11)) = _
    rw [hkeep]
    exact hOffset
  · simpa only [bCell,fromJoined] using
      (hkeep (.inl (.inl (.inl (.inl (.inl bitsCell)))))).trans hB
  · simpa only [strideCell,fromJoined] using
      (hkeep (.inl (.inl (.inr (1 : Fin 2))))).trans
        ((hRetain (.inl (.inr 1))).trans hW)
  · simpa only [hCell,fromJoined] using
      (hkeep (.inl (.inl (.inl (.inl (.inr
        (.inl (ScalarB t lambda).input))))))).trans hH

#print axioms physical_full_scalar_join

end Paper2.YaoEntryParameterJoin
