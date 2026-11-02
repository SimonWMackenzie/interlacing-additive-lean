import Paper2.YaoScalarRouting

/-! The scalar producer and charged five-copy router share one literal raw
controller. The full flat tape is an explicit, unchanged source bank. -/

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

abbrev ScalarLabel (t lambda : ℕ) :=
  BitMachineRawSequence.Label (LiftSelectorLabel t lambda) PayloadLabel
abbrev ScalarControl (t lambda : ℕ) := LiftSelectorControl t lambda × Bool
abbrev LiftScalarLabel (t lambda : ℕ) := ScalarLabel t lambda ⊕ Unit
abbrev LiftScalarControl (t lambda : ℕ) := ScalarControl t lambda × Unit

noncomputable def routedForeign (source : List Bool) : Fin 13 ⊕ Unit → List Bool
  | .inl 3 => source
  | _ => []

/-- Explicit inherited scalar-controller clock, followed by five linear
source-preserving copies. For fixed gap `t` and fixed local `lambda`, every
term is a primitive unary-machine bound in the basic unary input lengths. -/
noncomputable def scalarBudget (t lambda e z g ell p : ℕ) : ℕ :=
  (2*e+2 + (UnaryBinaryEncoding.coefficient+6)*(e+1)^2 +
    2*paddedEdgeBits e+2 + 16*paddedEdgeCount e) +
  (2*paddedEdgeCount e+2) +
  (1 + MatrixAddressMachine.exactTime (paddedEdgeCount e)
    (fixedWidth t) (fixedTail t lambda)) +
  (fixedQ t + fixedK t + 4) + (fixedPayloadK t + 2) +
  MatrixTemplateAddressSetup.bound 0 0 z (fixedQ t) g (paddedEdgeBits e) +
  1 +
  (MatrixAddressMachine.exactTime (paddedEdgeCount e) (fixedK t) 0 +
   MatrixAddressMachine.exactTime ell (paddedEdgeCount e * fixedK t) p +
   MatrixAddressMachine.exactTime
     (selectorCount t (paddedEdgeBits e) lambda) (fixedQ t) 0 +
   MatrixAddressMachine.exactTime
     (selectorCount t (paddedEdgeBits e) lambda * fixedQ t)
     (paddedEdgeBits e)
     (ell * (paddedEdgeCount e * fixedK t) + p)) + 1

noncomputable def routedBase {t lambda : ℕ} (S : PayloadStack t lambda → List Bool)
    (source : List Bool) : RouteStack t lambda → List Bool :=
  Sum.elim S (routedForeign source)

noncomputable def routedFinal {t lambda : ℕ} (S : PayloadStack t lambda → List Bool)
    (source : List Bool) : RouteStack t lambda → List Bool :=
  let E := routedBase S source
  let E₁ := Function.update E (routeTarget t lambda 0)
    (E (routeSource t lambda 0))
  let E₂ := Function.update E₁ (routeTarget t lambda 1)
    (E (routeSource t lambda 1))
  let E₃ := Function.update E₂ (routeTarget t lambda 2)
    (E (routeSource t lambda 2))
  let E₄ := Function.update E₃ (routeTarget t lambda 3)
    (E (routeSource t lambda 3))
  Function.update E₄ (routeTarget t lambda 4)
    (E (routeSource t lambda 4))

theorem routed_final_targets (t lambda : ℕ)
    (S : PayloadStack t lambda → List Bool) (source : List Bool)
    (j : Fin 5) :
    routedFinal S source (routeTarget t lambda j) =
      S (routeScalarSource t lambda j) := by
  fin_cases j <;> rfl

theorem routed_final_source (t lambda : ℕ)
    (S : PayloadStack t lambda → List Bool) (source : List Bool) :
    routedFinal S source (.inr (.inl 3)) = source := by
  rfl

noncomputable def liftScalarProgram (t lambda : ℕ)
    (stageV0 : StageOneControl t lambda)
    (v0 : SelectorControl t lambda) : LiftScalarLabel t lambda →
      TM2.Stmt (fun _ : RouteStack t lambda => Bool)
        (LiftScalarLabel t lambda) (LiftScalarControl t lambda)
  | .inl l => liftStmt none (fullScalarProgram t lambda stageV0 v0 l)
  | .inr () => .halt

noncomputable def routedParameterProgram (t lambda : ℕ)
    (stageV0 : StageOneControl t lambda)
    (v0 : SelectorControl t lambda) :=
  BitMachineRawSequence.program
    (liftScalarProgram t lambda stageV0 v0) (routeProgram t lambda)
    (0,.scan) (((v0,()),false),()) none

theorem route_after_scalar_program (t lambda : ℕ)
    (stageV0 : StageOneControl t lambda)
    (v0 : SelectorControl t lambda)
    (a : ScalarLabel t lambda)
    (S₀ S : PayloadStack t lambda → List Bool)
    (scalarSteps : ℕ)
    (hscalar : ((advance (fullScalarProgram t lambda stageV0 v0))^[scalarSteps])
        (⟨some a,((v0,()),false),S₀⟩ : TM2.Cfg (fun _ : PayloadStack t lambda => Bool)
          (ScalarLabel t lambda) (ScalarControl t lambda)) =
        ⟨none,((v0,()),false),S⟩)
    (source : List Bool) :
    ∃ (routeSteps total : ℕ),
      let E : RouteStack t lambda → List Bool :=
        Sum.elim S (routedForeign source)
      routeSteps ≤ ∑ j : Fin 5,
        (2*(E (routeSource t lambda j)).length+2) ∧
      total ≤ scalarSteps + routeSteps + 1 ∧
      let E₁ := Function.update E (routeTarget t lambda 0)
        (E (routeSource t lambda 0))
      let E₂ := Function.update E₁ (routeTarget t lambda 1)
        (E (routeSource t lambda 1))
      let E₃ := Function.update E₂ (routeTarget t lambda 2)
        (E (routeSource t lambda 2))
      let E₄ := Function.update E₃ (routeTarget t lambda 3)
        (E (routeSource t lambda 3))
      let E₅ := Function.update E₄ (routeTarget t lambda 4)
        (E (routeSource t lambda 4))
      ((advance (routedParameterProgram t lambda stageV0 v0))^[total])
        (⟨some (.inl (.inl a)),((((v0,()),false),()),none),
          Sum.elim S₀ (routedForeign source)⟩ :
          TM2.Cfg (fun _ : RouteStack t lambda => Bool) _ _) =
        ⟨none,((((v0,()),false),()),none),E₅⟩ := by
  let foreign := routedForeign source
  let c : TM2.Cfg (fun _ : PayloadStack t lambda => Bool)
      (ScalarLabel t lambda) (ScalarControl t lambda) :=
        ⟨some a,((v0,()),false),S₀⟩
  let E : RouteStack t lambda → List Bool := Sum.elim S foreign
  have hhalt : (((advance (fullScalarProgram t lambda stageV0 v0))^[scalarSteps]) c).l =
      none := by rw [hscalar]
  obtain ⟨liftSteps,hlift,hLift⟩ := lift_outputs
    (fullScalarProgram t lambda stageV0 v0)
    (liftScalarProgram t lambda stageV0 v0) none
    (by intro l; rfl) () foreign c scalarSteps hhalt
  have hLift' : ((advance (liftScalarProgram t lambda stageV0 v0))^[liftSteps])
      (⟨some (.inl a),(((v0,()),false),()),Sum.elim S₀ foreign⟩ :
        TM2.Cfg (fun _ : RouteStack t lambda => Bool)
          (LiftScalarLabel t lambda) (LiftScalarControl t lambda)) =
      ⟨none,(((v0,()),false),()),E⟩ := by
    rw [hscalar] at hLift
    simpa only [c,liftCfg,E,Option.map_none] using hLift
  obtain ⟨routeSteps,hroute,hRoute⟩ := route_all_five t lambda E
    (by intro j; fin_cases j <;> rfl)
    (by simp [E,routeScratch,foreign,routedForeign])
  let E₁ := Function.update E (routeTarget t lambda 0)
    (E (routeSource t lambda 0))
  let E₂ := Function.update E₁ (routeTarget t lambda 1)
    (E (routeSource t lambda 1))
  let E₃ := Function.update E₂ (routeTarget t lambda 2)
    (E (routeSource t lambda 2))
  let E₄ := Function.update E₃ (routeTarget t lambda 3)
    (E (routeSource t lambda 3))
  let E₅ := Function.update E₄ (routeTarget t lambda 4)
    (E (routeSource t lambda 4))
  have hRoute' : ((advance (routeProgram t lambda))^[routeSteps])
      (⟨some (0,.scan),none,E⟩ : RouteConfig t lambda) =
      ⟨none,none,E₅⟩ := by
    simpa only [routeRun,E₁,E₂,E₃,E₄,E₅] using hRoute
  obtain ⟨total,htotal,hjoined⟩ := BitMachineRawSequence.runs
    (liftScalarProgram t lambda stageV0 v0) (routeProgram t lambda)
    (.inl a) (0,.scan) (((v0,()),false),()) (((v0,()),false),()) none none
    (Sum.elim S₀ foreign) E E₅ liftSteps routeSteps hLift' hRoute'
  refine ⟨routeSteps,total,?_,by omega,?_⟩
  · simpa only [E,routeSource] using hroute
  · simpa only [routedParameterProgram,E,E₁,E₂,E₃,E₄,E₅,foreign,
      BitMachineRawSequence.leftLabel] using hjoined

#print axioms route_after_scalar_program
#print axioms routed_final_targets
#print axioms routed_final_source

theorem physical_routed_parameter_join
    (t lambda e z g ell p : ℕ) (source : List Bool) :
    ∃ (scalarSteps routeSteps total : ℕ)
      (S : PayloadStack t lambda → List Bool),
      scalarSteps ≤ scalarBudget t lambda e z g ell p ∧
      total ≤ scalarSteps + routeSteps + 1 ∧
      routeSteps ≤ 2*((z * fixedQ t + g) * paddedEdgeBits e +
        paddedEdgeBits e + payloadBaseValue t lambda e ell p +
        fixedK t + paddedEdgeCount e)+10 ∧
      let c0 := selectorInitial t lambda e z g ell p
      let stageV0 : StageOneControl t lambda :=
        ((frameStart t lambda e z g ell p).var,())
      let v0 := c0.var
      let S₀ : PayloadStack t lambda → List Bool :=
        Sum.elim c0.stk (fun _ => [])
      ((advance (routedParameterProgram t lambda stageV0 v0))^[total])
        (⟨some (.inl (.inl (.inl (.inl (.inl (.inl
          (widthStartLabel t lambda))))))),
          ((((v0,()),false),()),none),
          Sum.elim S₀ (routedForeign source)⟩ :
          TM2.Cfg (fun _ : RouteStack t lambda => Bool) _ _) =
        ⟨none,((((v0,()),false),()),none),routedFinal S source⟩ ∧
      routedFinal S source (routeTarget t lambda 0) =
        List.replicate ((z * fixedQ t + g) * paddedEdgeBits e) true ∧
      routedFinal S source (routeTarget t lambda 1) =
        List.replicate (paddedEdgeBits e) true ∧
      routedFinal S source (routeTarget t lambda 2) =
        List.replicate (payloadBaseValue t lambda e ell p) true ∧
      routedFinal S source (routeTarget t lambda 3) =
        List.replicate (fixedK t) true ∧
      routedFinal S source (routeTarget t lambda 4) =
        List.replicate (paddedEdgeCount e) true ∧
      routedFinal S source (.inr (.inl 3)) = source := by
  obtain ⟨a,b,n,m,w,s,j,k,scalarSteps,ha,hb,hn,hm,hw,hs,hj,hk,htotal,
    hscalar,hBase,hOffset,hB,hStride,hH⟩ :=
    physical_full_scalar_join t lambda e z g ell p
  let c0 := selectorInitial t lambda e z g ell p
  let stageV0 : StageOneControl t lambda :=
    ((frameStart t lambda e z g ell p).var,())
  let v0 := c0.var
  let f := frameRun t lambda n (frameStart t lambda e z g ell p)
  let U := Function.update
    (Function.update (Sum.elim f.stk (fun _ => [])) (.inr (0 : Fin 2))
      (List.replicate (fixedQ t) true)) (.inr (1 : Fin 2))
      (List.replicate (fixedK t) true)
  let W : Stack t lambda → List Bool :=
    Function.update (Sum.elim U (fun _ => [])) (.inr (0 : Fin 1))
      (List.replicate (fixedPayloadK t) true)
  let T := Function.update
    (Function.update (Sum.elim W (fun _ => [])) (selectorSlot t lambda 10)
      (List.replicate (z * fixedQ t + g) true))
    (selectorSlot t lambda 11)
    (List.replicate ((z * fixedQ t + g) * paddedEdgeBits e) true)
  let R₀ : PayloadStack t lambda → List Bool := Sum.elim T (fun _ => [])
  let R₁ := Function.update R₀ (fresh t lambda 3)
    (List.replicate (paddedEdgeCount e * fixedK t) true)
  let R₂ := Function.update R₁ (fresh t lambda 4)
    (List.replicate (ell * (paddedEdgeCount e * fixedK t) + p) true)
  let R₃ := Function.update R₂ (fresh t lambda 5)
    (List.replicate (selectorCount t (paddedEdgeBits e) lambda * fixedQ t) true)
  let R₄ := Function.update R₃ (fresh t lambda 6)
    (List.replicate (payloadBaseValue t lambda e ell p) true)
  let S₀ : PayloadStack t lambda → List Bool := Sum.elim c0.stk (fun _ => [])
  have hscalar' :
      ((advance (fullScalarProgram t lambda stageV0 v0))^[scalarSteps])
        (⟨some (.inl (.inl (.inl (.inl (widthStartLabel t lambda))))),
          ((v0,()),false),S₀⟩ :
          TM2.Cfg (fun _ : PayloadStack t lambda => Bool)
            (ScalarLabel t lambda) (ScalarControl t lambda)) =
        ⟨none,((v0,()),false),R₄⟩ := by
    simpa only [c0,stageV0,v0,f,U,W,T,R₀,R₁,R₂,R₃,R₄,S₀] using hscalar
  obtain ⟨routeSteps,total,hroute,hall,hjoined⟩ :=
    route_after_scalar_program t lambda stageV0 v0
      (.inl (.inl (.inl (.inl (widthStartLabel t lambda)))))
      S₀ R₄ scalarSteps hscalar' source
  have hroute' : routeSteps ≤ 2*((z * fixedQ t + g) * paddedEdgeBits e +
      paddedEdgeBits e + payloadBaseValue t lambda e ell p +
      fixedK t + paddedEdgeCount e)+10 := by
    have h0 : R₄ (routeScalarSource t lambda 0) =
        List.replicate ((z * fixedQ t + g) * paddedEdgeBits e) true := by
      simpa only [routeScalarSource] using hOffset
    have h1 : R₄ (routeScalarSource t lambda 1) =
        List.replicate (paddedEdgeBits e) true := by
      simpa only [routeScalarSource] using hB
    have h2 : R₄ (routeScalarSource t lambda 2) =
        List.replicate (payloadBaseValue t lambda e ell p) true := by
      simpa only [routeScalarSource] using hBase
    have h3 : R₄ (routeScalarSource t lambda 3) =
        List.replicate (fixedK t) true := by
      simpa only [routeScalarSource] using hStride
    have h4 : R₄ (routeScalarSource t lambda 4) =
        List.replicate (paddedEdgeCount e) true := by
      simpa only [routeScalarSource] using hH
    simp only [Fin.sum_univ_five] at hroute
    simp only [routeSource,Sum.elim_inl,List.length_replicate,
      h0,h1,h2,h3,h4] at hroute
    omega
  have hbudget : scalarSteps ≤ scalarBudget t lambda e z g ell p := by
    unfold scalarBudget
    omega
  refine ⟨scalarSteps,routeSteps,total,R₄,hbudget,hall,hroute',?_⟩
  dsimp only
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [c0,stageV0,v0,S₀,routedFinal,routedBase] using hjoined
  · rw [routed_final_targets]
    simpa only [routeScalarSource] using hOffset
  · rw [routed_final_targets]
    simpa only [routeScalarSource] using hB
  · rw [routed_final_targets]
    simpa only [routeScalarSource] using hBase
  · rw [routed_final_targets]
    simpa only [routeScalarSource] using hStride
  · rw [routed_final_targets]
    simpa only [routeScalarSource] using hH
  · exact routed_final_source t lambda R₄ source

#print axioms physical_routed_parameter_join

end Paper2.YaoEntryParameterJoin
