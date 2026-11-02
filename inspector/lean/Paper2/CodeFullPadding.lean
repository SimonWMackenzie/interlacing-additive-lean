import Paper2.CodeFullRepeatFuel
import EthInapproximability.CurrentPaper.BitMachineClearBank
import Mathlib.Tactic

/-! Fixed physical extension of the repeated interpreter: a normalized-done
status drains exactly the remaining serialized tape; failure still halts. -/

namespace Paper2.CodeFullPadding

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineClearBank
open Paper2.GeneratorCode Paper2.GeneratorSerialization

noncomputable section

abbrev Stack := CodeFullCleanStep.Stack
abbrev Control := CodeFullCleanStep.Control
abbrev Label := CodeFullCleanStep.Label ⊕ (Unit ⊕ (Unit ⊕ Unit))
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def padLabel : Label := .inr (.inr (.inl ()))
def endLabel : Label := .inr (.inr (.inr ()))
def routeLabel : Label := .inr (.inl ())
def tapeSlot : Stack := CodeHeaderDraw.d 0

def doneStatus (v : Control) : Bool :=
  (CodeDrawResultHandler.savedStatus v.1.1.1).isNone

noncomputable def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l =>
      BitMachineInline.stmt Sum.inl id id (some routeLabel)
        (CodeFullCleanStep.program l)
  | .inr (.inl ()) =>
      branch CodeFullRepeat.success
        (load (fun _ => CodeFullRepeat.entryControl)
          (goto (fun _ => .inl CodeFullRepeat.entryLabel)))
        (branch doneStatus (goto (fun _ => padLabel)) halt)
  | .inr (.inr (.inl ())) =>
      clearStep tapeSlot padLabel endLabel
  | .inr (.inr (.inr ())) => halt

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

def sourceCfg (c : CodeFullCleanStep.Config) : Config :=
  BitMachineInline.cfg Sum.inl id (some routeLabel) c

def routeCfg (v : Control) (S : Stack → List Bool) : Config :=
  ⟨some routeLabel,v,S⟩

def start (s : State) (tape : List Bool) (B R : Nat) : Config :=
  sourceCfg (CodeFullCleanStep.start s tape B R)

private theorem run_add (a b : Nat) (c : Config) :
    run (a+b) c = run b (run a c) := by
  change ((advance program)^[a+b]) c =
    ((advance program)^[b]) (((advance program)^[a]) c)
  rw [Nat.add_comm a b,Function.iterate_add_apply]

private theorem id_read : Function.LeftInverse (id : Control → Control) id := by
  intro v; rfl

private theorem source_program (l : CodeFullCleanStep.Label) :
    program (.inl l) = BitMachineInline.stmt Sum.inl id id
      (some routeLabel) (CodeFullCleanStep.program l) := rfl

theorem source_to_route (c d : CodeFullCleanStep.Config) (t : Nat)
    (hr : CodeFullCleanStep.run t c = d) (hd : d.l = none) :
    ∃ u ≤ t, run u (sourceCfg c) = routeCfg d.var d.stk := by
  have hh : (((advance CodeFullCleanStep.program)^[t]) c).l = none := by
    change (CodeFullCleanStep.run t c).l = none
    rw [hr]; exact hd
  obtain ⟨u,hu,hur⟩ := BitMachineInline.outputs Sum.inl id id
    id_read (some routeLabel) CodeFullCleanStep.program program
    source_program c t hh
  refine ⟨u,hu,?_⟩
  change run u (sourceCfg c) =
    BitMachineInline.cfg Sum.inl id (some routeLabel)
      (CodeFullCleanStep.run t c) at hur
  rw [hr] at hur
  simpa [routeCfg,BitMachineInline.cfg,hd] using hur

theorem route_done (v : Control) (S : Stack → List Bool)
    (hs : CodeFullRepeat.success v = false)
    (hd : doneStatus v = true) :
    run 1 (routeCfg v S) = ⟨some padLabel,v,S⟩ := by
  simp [run,routeCfg,program,routeLabel,padLabel,BitMachineEncoding.advance,
    TM2.step,TM2.stepAux,hs,hd]

theorem route_failure (v : Control) (S : Stack → List Bool)
    (hs : CodeFullRepeat.success v = false)
    (hd : doneStatus v = false) :
    run 1 (routeCfg v S) = ⟨none,v,S⟩ := by
  simp [run,routeCfg,program,routeLabel,BitMachineEncoding.advance,
    TM2.step,TM2.stepAux,hs,hd]

theorem route_success (v : Control) (S : Stack → List Bool)
    (hs : CodeFullRepeat.success v = true) :
    run 1 (routeCfg v S) =
      ⟨some (.inl CodeFullRepeat.entryLabel),
        CodeFullRepeat.entryControl,S⟩ := by
  simp [run,routeCfg,program,routeLabel,BitMachineEncoding.advance,
    TM2.step,TM2.stepAux,hs]

theorem route_to_start (v : Control) (S : Stack → List Bool)
    (s : State) (tape : List Bool) (B R : Nat)
    (hs : CodeFullRepeat.success v = true)
    (hbank : S = (CodeFullCleanStep.start s tape B R).stk) :
    run 1 (routeCfg v S) = start s tape B R := by
  rw [route_success v S hs]
  obtain ⟨hl,hv⟩ := CodeFullRepeat.entry_fixed s tape B R
  simp [start,sourceCfg,BitMachineInline.cfg,hl,hv,hbank]

theorem reenter_from_reached (s next : State) (tape residual : List Bool)
    (B R : Nat) (d : CodeAdminBranchJoin.Config) (t : Nat)
    (hr : CodeAdminBranchJoin.run t
      (CodeAdminBranchJoin.start s tape B R) = d)
    (hd : d.l = none)
    (hs : CodeFullRepeat.success ((d.var,none) : Control) = true)
    (hbank : (CodeInterpreterReset.final d.var d.stk).stk =
      (CodeAdminBranchJoin.start next residual B R).stk) :
    ∃ u ≤ t + CodeInterpreterReset.clock d.stk + 1,
      run u (start s tape B R) = start next residual B R := by
  obtain ⟨a,ha,har⟩ := CodeFullCleanStep.raw_clean_from_reached
    s tape B R d t hr hd
  let clean := CodeFullCleanStep.resetCfg
    (CodeInterpreterReset.final d.var d.stk)
  obtain ⟨b,hb,hbr⟩ := source_to_route
    (CodeFullCleanStep.start s tape B R) clean a har rfl
  have hroute := route_to_start clean.var clean.stk
    next residual B R hs hbank
  refine ⟨b+1,by omega,?_⟩
  rw [run_add b 1]
  change run 1 (run b
    (sourceCfg (CodeFullCleanStep.start s tape B R))) = _
  rw [hbr]
  exact hroute

theorem pad_run (v : CodeAdminBranchJoin.Control)
    (S : Stack → List Bool) :
    run ((S tapeSlot).length+1)
      ⟨some padLabel,(v,none),S⟩ =
      ⟨some endLabel,(v,none),Function.update S tapeSlot []⟩ := by
  exact clear_one_run program tapeSlot padLabel endLabel rfl v S

theorem pad_halt (v : CodeAdminBranchJoin.Control)
    (S : Stack → List Bool) :
    run ((S tapeSlot).length+2)
      ⟨some padLabel,(v,none),S⟩ =
      ⟨none,(v,none),Function.update S tapeSlot []⟩ := by
  have hpad := pad_run v S
  have hadd : run ((S tapeSlot).length+2)
      ⟨some padLabel,(v,none),S⟩ =
      run 1 (run ((S tapeSlot).length+1)
        ⟨some padLabel,(v,none),S⟩) := by
    change ((advance program)^[(S tapeSlot).length+2]) _ =
      ((advance program)^[1])
        (((advance program)^[(S tapeSlot).length+1]) _)
    rw [show (S tapeSlot).length+2 = 1+((S tapeSlot).length+1) by omega,
      Function.iterate_add_apply]
  rw [hadd,hpad]
  simp [run,program,endLabel,BitMachineEncoding.advance,TM2.step,TM2.stepAux]

#print axioms pad_halt

end
end Paper2.CodeFullPadding
