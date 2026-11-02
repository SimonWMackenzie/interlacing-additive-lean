import CurrentAdditive.FeatureGuardInvoke96

/-! The real depth guard dispatches to the complete descriptor step. An
ineligible descriptor makes no output/count change. Its guard flag and
invocation scratch are physically removed. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace CurrentAdditive.FeatureGuardedDescriptor96
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.MinimumRatioContext

def dispatchProgram {L V : Type}
    (P : L → TM2.Stmt (fun _ : Fin 96 => Bool) L V)
    (entry : L) (initial : V) :
    L ⊕ Unit → TM2.Stmt (fun _ : Fin 96 => Bool) (L ⊕ Unit) (V × Option Bool)
  | .inl l => BitMachineInline.stmt Sum.inl
      (fun v => (v,none)) Prod.fst none (P l)
  | .inr () => .pop 27 (fun v b => (v.1,b))
      (.branch (fun v => v.2.getD false)
        (.load (fun _ => (initial,none)) (.goto (fun _ => .inl entry))) .halt)

def dispatcher := dispatchProgram FeatureEligibleDescriptor96.program
  FeatureEligibleDescriptor96.start FeatureEligibleDescriptor96.control
def dispatcherControl := (FeatureEligibleDescriptor96.control,(none : Option Bool))

private def labelFor {L V : Type}
    (_P : L → TM2.Stmt (fun _ : Fin 96 => Bool) L V) (l : L) := l

def program := BitMachineRawSequence.program FeatureGuardInvoke96.program dispatcher
  (.inr ()) FeatureGuardInvoke96.control dispatcherControl
def start := labelFor program (BitMachineRawSequence.leftLabel FeatureGuardInvoke96.start)
def control := (FeatureGuardInvoke96.control,dispatcherControl)

def clock (j : Nat) (c : List (Nat × Nat)) (ys : List Nat)
    (body : List Bool) :=
  FeatureGuardInvoke96.clock c+FeatureEligibleDescriptor96.clock j c ys body+2

def output (j : Nat) (c : List (Nat × Nat)) (ys : List Nat)
    (body : List Bool) : List Bool :=
  if c.length<8192 then body++FeatureEligibleDescriptor96.extensions j c ys else body

def newCount (c : List (Nat × Nat)) (ys : List Nat) (count : List Bool) : List Bool :=
  if c.length<8192 then List.replicate ys.length true++count else count

theorem dispatch_true (S : Fin 96 → List Bool) (h27 : S 27=[]) :
    advance dispatcher
      ⟨some (.inr ()),dispatcherControl,Function.update S 27 [true]⟩ =
      ⟨some (.inl FeatureEligibleDescriptor96.start),dispatcherControl,S⟩ := by
  simp only [dispatcher,dispatchProgram,dispatcherControl,advance,TM2.step,
    Option.getD_some,TM2.stepAux,Function.update_self,List.head?_cons,
    List.tail_cons,Option.getD_some,cond_true]
  congr 1
  rw [Function.update_idem,← h27,Function.update_eq_self]

theorem dispatch_false (S : Fin 96 → List Bool) (h27 : S 27=[]) :
    advance dispatcher
      ⟨some (.inr ()),dispatcherControl,Function.update S 27 [false]⟩ =
      ⟨none,(FeatureEligibleDescriptor96.control,some false),S⟩ := by
  simp only [dispatcher,dispatchProgram,dispatcherControl,advance,TM2.step,
    Option.getD_some,TM2.stepAux,Function.update_self,List.head?_cons,
    List.tail_cons,Option.getD_some,cond_false]
  congr 1
  rw [Function.update_idem,← h27,Function.update_eq_self]

theorem run (S : Fin 96 → List Bool) (j : Nat)
    (c : List (Nat × Nat)) (ys : List Nat) (body count : List Bool)
    (h30 : S 30=SourceListEncoding.encode (FeatureInnerAlphabetRun64.labelWords ys))
    (h9 : S 9=body) (h12 : S 12=count) (h15 : S 15=j.bits)
    (h31 : S 31=List.replicate ys.length true)
    (h6 : S 6=CylinderFeatureCodec.encodeFeature c) (h16 : S 16=[])
    (hguard : ∀ k : Fin 96, 19≤k.val → k.val≤28 → S k=[])
    (hhigh : ∀ k : Fin 96, 32≤k.val → S k=[]) :
    ∃ t≤clock j c ys body,
      let z := ((advance program)^[t])
        (⟨some start,control,S⟩ : TM2.Cfg (fun _ : Fin 96 => Bool) _ _)
      z.l=none ∧ z.stk 9=output j c ys body ∧ z.stk 12=newCount c ys count ∧
      (∀ k : Fin 96, k.val<32 → k≠9 → k≠12 → z.stk k=S k) ∧
      (∀ k : Fin 96, 32≤k.val → z.stk k=[]) := by
  classical
  let flag := decide (c.length<8192)
  let SG := Function.update S (27 : Fin 96) [flag]
  obtain ⟨a,ha,haRun⟩ := FeatureGuardInvoke96.run S c h6 hguard
  have h27 : S 27=[] := hguard 27 (by decide) (by decide)
  have hd : ∃ b≤FeatureEligibleDescriptor96.clock j c ys body+1,
      ∃ v T,
      ((advance dispatcher)^[b])
        (⟨some (.inr ()),dispatcherControl,SG⟩ :
          TM2.Cfg (fun _ : Fin 96 => Bool) _ _) = ⟨none,v,T⟩ ∧
      T 9=output j c ys body ∧ T 12=newCount c ys count ∧
      (∀ k : Fin 96, k.val<32 → k≠9 → k≠12 → T k=S k) ∧
      (∀ k : Fin 96, 32≤k.val → T k=[]) := by
    by_cases hc : c.length<8192
    · obtain ⟨b,hb,hh,ho,hcCount,hp,hclear⟩ :=
        FeatureEligibleDescriptor96.run S j c ys body count
          h30 h9 h12 h15 h31 h6 h16 hhigh
      let I := ((advance FeatureEligibleDescriptor96.program)^[0])
        ⟨some FeatureEligibleDescriptor96.start,FeatureEligibleDescriptor96.control,S⟩
      obtain ⟨u,hu,huRun⟩ := BitMachineInline.outputs
        (Sum.inl : _ → _ ⊕ Unit) (fun v => (v,none)) Prod.fst
        (by intro v; rfl) none FeatureEligibleDescriptor96.program dispatcher
        (by intro l; rfl) I b hh
      let E := ((advance FeatureEligibleDescriptor96.program)^[b]) I
      have he : E=⟨none,E.var,E.stk⟩ := by
        have hhalt : E.l=none := hh
        cases h : E with
        | mk l v T => cases l with
          | none => rfl
          | some l => simp [h] at hhalt
      have hflag : flag=true := by simp [flag,hc]
      have hone := dispatch_true S h27
      have hrun : ((advance dispatcher)^[u+1])
          (⟨some (.inr ()),dispatcherControl,SG⟩ :
            TM2.Cfg (fun _ : Fin 96 => Bool) _ _) =
          ⟨none,(E.var,none),E.stk⟩ := by
        rw [Function.iterate_succ_apply]
        change ((advance dispatcher)^[u])
          (advance dispatcher ⟨some (.inr ()),dispatcherControl,SG⟩)=_
        rw [show SG=Function.update S 27 [true] by simp [SG,hflag],hone]
        have hr := huRun
        change ((advance dispatcher)^[u])
          ⟨some (.inl FeatureEligibleDescriptor96.start),dispatcherControl,S⟩ =
          BitMachineInline.cfg (Sum.inl : _ → _ ⊕ Unit) (fun v => (v,none)) none E at hr
        rw [he] at hr
        exact hr
      refine ⟨u+1,by omega,_,E.stk,hrun,?_,?_,hp,hclear⟩
      · simpa only [output,if_pos hc] using ho
      · simpa only [newCount,if_pos hc] using hcCount
    · have hflag : flag=false := by simp [flag,hc]
      refine ⟨1,by omega,(FeatureEligibleDescriptor96.control,some false),S,?_,?_,?_,?_,hhigh⟩
      · simpa only [Function.iterate_one,SG,hflag] using dispatch_false S h27
      · simpa [output,hc] using h9
      · simpa [newCount,hc] using h12
      · intro k _ _ _; rfl
  obtain ⟨b,hb,v,T,hbRun,h9T,h12T,hpT,hclearT⟩ := hd
  obtain ⟨t,ht,hfinal⟩ := BitMachineRawSequence.runs
    FeatureGuardInvoke96.program dispatcher FeatureGuardInvoke96.start (.inr ())
    FeatureGuardInvoke96.control FeatureGuardInvoke96.control dispatcherControl v
    S SG T a b haRun hbRun
  refine ⟨t,by unfold clock; omega,?_,?_,?_,?_,?_⟩
  · simpa only [program,start,labelFor,control] using congrArg TM2.Cfg.l hfinal
  · exact (congrArg (fun w => w.stk (9 : Fin 96)) hfinal).trans h9T
  · exact (congrArg (fun w => w.stk (12 : Fin 96)) hfinal).trans h12T
  · intro k hk hk9 hk12
    exact (congrArg (fun w => w.stk k) hfinal).trans (hpT k hk hk9 hk12)
  · intro k hk
    exact (congrArg (fun w => w.stk k) hfinal).trans (hclearT k hk)

#print axioms run
end CurrentAdditive.FeatureGuardedDescriptor96
