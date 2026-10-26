import CurrentAdditive.GaussGuardedFront64
import CurrentAdditive.GaussNextStateFieldsFrame64
import CurrentAdditive.GaussStepOutputTransfer

namespace CurrentAdditive.GaussWholeStepProgram
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
set_option maxSynthPendingDepth 128

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open GaussSearchGridInvoke (Bank low)

abbrev FrontControl := GaussGuardedFront64.Control
abbrev RewriteControl := GaussSearchGridInvoke.Control
abbrev FieldsControl := GaussNextStateFields64.Control
abbrev TransferControl := GaussStepOutputTransfer.Control
abbrev Control := FrontControl × RewriteControl × FieldsControl × TransferControl × Option Bool

inductive Label where
  | front (l : GaussGuardedFront64.Label)
  | afterFront | choosePivot
  | rewrite (l : GaussSearchGridInvoke.Label)
  | afterRewrite
  | fields (l : GaussNextStateFields64.Label)
  | afterFields
  | transfer (l : GaussStepOutputTransfer.Label)
  | done
  deriving Fintype

noncomputable instance : DecidableEq Label := Classical.decEq _

def frontInit := GaussGuardedFront64.eBase GaussGuardedFront64.baseInit
def control : Control := (frontInit,GaussSearchGridInvoke.control,
  GaussNextStateFields64.control,GaussStepOutputTransfer.control,none)
def eFront (v : FrontControl) : Control :=
  (v,GaussSearchGridInvoke.control,GaussNextStateFields64.control,GaussStepOutputTransfer.control,none)
def eRewrite (v : RewriteControl) : Control :=
  (frontInit,v,GaussNextStateFields64.control,GaussStepOutputTransfer.control,none)
def eFields (v : FieldsControl) : Control :=
  (frontInit,GaussSearchGridInvoke.control,v,GaussStepOutputTransfer.control,none)
def eTransfer (v : TransferControl) : Control :=
  (frontInit,GaussSearchGridInvoke.control,GaussNextStateFields64.control,v,none)

def readRewrite (v : Control) : RewriteControl := v.2.1
def readFields (v : Control) : FieldsControl := v.2.2.1
def readTransfer (v : Control) : TransferControl := v.2.2.2.1
def chosen (v : Control) : Option Bool := v.2.2.2.2
def setChosen (v : Control) (b : Option Bool) : Control :=
  (v.1,v.2.1,v.2.2.1,v.2.2.2.1,b)

def frontProgram := GaussCellCursorEmbedding.relocate low GaussGuardedFront64.program
def fieldsProgram := GaussCellCursorEmbedding.relocate low GaussNextStateFields64.program

def program : Label → TM2.Stmt (fun _ : Bank => Bool) Label Control
  | .front l => BitMachineInline.stmt Label.front eFront Prod.fst
      (some .afterFront) (frontProgram l)
  | .afterFront => .branch
      (fun v => match v.1.2.1.2 with | .choose _ => true | _ => false)
      (.goto (fun _ => .choosePivot)) (.goto (fun _ => .done))
  | .choosePivot => .pop (low 20) setChosen
      (.push (low 20) (fun v => (chosen v).getD false)
        (.branch (fun v => (chosen v).getD false)
          (.load (fun _ => eRewrite GaussSearchGridInvoke.control)
            (.goto (fun _ => .rewrite GaussSearchGridInvoke.start)))
          (.load (fun _ => eFields GaussNextStateFields64.control)
            (.goto (fun _ => .fields GaussNextStateFields64.start)))))
  | .rewrite l => BitMachineInline.stmt Label.rewrite eRewrite readRewrite
      (some .afterRewrite) (GaussSearchGridInvoke.program l)
  | .afterRewrite => .load (fun _ => eFields GaussNextStateFields64.control)
      (.goto (fun _ => .fields GaussNextStateFields64.start))
  | .fields l => BitMachineInline.stmt Label.fields eFields readFields
      (some .afterFields) (fieldsProgram l)
  | .afterFields => .load (fun _ => eTransfer GaussStepOutputTransfer.control)
      (.goto (fun _ => .transfer GaussStepOutputTransfer.start))
  | .transfer l => BitMachineInline.stmt Label.transfer eTransfer readTransfer
      (some .done) (GaussStepOutputTransfer.program l)
  | .done => .halt

def start : Label := .front (.base (BitMachineRawSequence.leftLabel (.copy .scan)))
abbrev Config := TM2.Cfg (fun _ : Bank => Bool) Label Control
def initial (word : List Bool) : Config := rawInit (low 30) start control word
def run (t : Nat) (C : Config) := ((advance program)^[t]) C

theorem run_add {C C' : Config} {t : Nat} (h : run t C=C') (u : Nat) :
    run (t+u) C=run u C' := by
  rw [Nat.add_comm,run,Function.iterate_add_apply]
  exact congrArg (run u) h

theorem terminal_dispatch (S : Bank → List Bool) :
    run 1 ⟨some .afterFront,eFront (GaussGuardedFront64.eTerminal ((),none)),S⟩=
      ⟨some .done,eFront (GaussGuardedFront64.eTerminal ((),none)),S⟩ := rfl

theorem active_dispatch (vf : GaussFlagSearch.Control) (S : Bank → List Bool) :
    run 1 ⟨some .afterFront,eFront (GaussGuardedFront64.eActive (GaussGuardedFront64.copyInit,.choose vf)),S⟩=
      ⟨some .choosePivot,eFront (GaussGuardedFront64.eActive (GaussGuardedFront64.copyInit,.choose vf)),S⟩ := rfl

theorem choose_pivot (b : Bool) (v : Control) (S : Bank → List Bool)
    (h20 : S (low 20)=[b]) :
    run 1 ⟨some .choosePivot,v,S⟩=
      if b then ⟨some (.rewrite GaussSearchGridInvoke.start),eRewrite GaussSearchGridInvoke.control,S⟩
      else ⟨some (.fields GaussNextStateFields64.start),eFields GaussNextStateFields64.control,S⟩ := by
  cases b <;>
    simp only [run,Function.iterate_one,advance,program,TM2.step,TM2.stepAux,h20,
      List.head?,List.tail,Option.getD_some,chosen,setChosen,cond_true,cond_false]
  all_goals congr 1; funext z; by_cases hz : z=low 20 <;> simp [Function.update_apply,hz,h20]

def machine : BitMachine.Machine := ofFinite (low 30) (low 62) start control program

#print axioms choose_pivot
end
end CurrentAdditive.GaussWholeStepProgram
