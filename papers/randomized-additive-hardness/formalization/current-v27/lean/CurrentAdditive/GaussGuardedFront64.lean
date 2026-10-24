import CurrentAdditive.GaussPreparedGuard64
import CurrentAdditive.GaussPhysicalSearchClock
import CurrentAdditive.GaussPivotPrepSave64
import CurrentAdditive.GaussPivotPrepSearchHigh64

namespace CurrentAdditive.GaussGuardedFront64

noncomputable section

set_option maxRecDepth 2048
set_option maxHeartbeats 1800000

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

abbrev Bank := Fin 64
abbrev BC := Unit × Option Bool
abbrev BL := SourceClausePreservingBroadcast.Label
abbrev CopyLabel := BitMachineRawSequence.Label
  (BitMachineRawSequence.Label (BitMachineRawSequence.Label BL BL) BL) BL
abbrev CopyControl := ((BC × BC) × BC) × BC
abbrev ActiveLabel := BitMachineRawSequence.Label CopyLabel GaussPivotSearchController.Label
abbrev ActiveControl := CopyControl × GaussPivotSearchController.Control

def copyInit : CopyControl := (((((),none),((),none)),((),none)),((),none))
def searchInit := GaussPivotPrepSearchHigh64.searchControl
def activeInit : ActiveControl := (copyInit,searchInit)
def copyStart : CopyLabel := BitMachineRawSequence.leftLabel
  (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel .scan))
def activeStart : ActiveLabel := BitMachineRawSequence.leftLabel copyStart

def activeProgram := BitMachineRawSequence.program
  GaussPivotPrepSave64.copyProgram GaussPivotSearchHigh64.program
  GaussPivotPrepSearchHigh64.searchLabel copyInit searchInit

abbrev Control := GaussPreparedGuard64.Control × ActiveControl × BC

inductive Label where
  | base (l : GaussPreparedGuard64.Label)
  | active (l : ActiveLabel)
  | terminal (l : BL)
  | afterGuard | doneActive | doneTerminal
  deriving DecidableEq, Fintype

def baseInit : GaussPreparedGuard64.Control :=
  (GaussPreparedGuard64.prepInit,GaussPreparedGuard64.guardInit)
def eBase (v : GaussPreparedGuard64.Control) : Control := (v,activeInit,((),none))
def eActive (v : ActiveControl) : Control := (baseInit,v,((),none))
def eTerminal (v : BC) : Control := (baseInit,activeInit,v)

def program : Label → TM2.Stmt (fun _ : Bank => Bool) Label Control
  | .base l => BitMachineInline.stmt Label.base eBase Prod.fst
      (some .afterGuard) (GaussPreparedGuard64.program l)
  | .active l => BitMachineInline.stmt Label.active eActive (fun v => v.2.1)
      (some .doneActive) (activeProgram l)
  | .terminal l => BitMachineInline.stmt Label.terminal eTerminal (fun v => v.2.2)
      (some .doneTerminal)
      (SourceClausePreservingBroadcast.program (31 : Bank) 63 [62] l)
  | .afterGuard => .branch
      (fun v => match v.1.2 with
        | .choose (some true) => true
        | _ => false)
      (.load (fun _ => eActive activeInit) (.goto (fun _ => .active activeStart)))
      (.load (fun _ => eTerminal ((),none)) (.goto (fun _ => .terminal .scan)))
  | .doneActive => .halt
  | .doneTerminal => .halt

abbrev Config := TM2.Cfg (fun _ : Bank => Bool) Label Control
def run (t : Nat) (c : Config) := ((advance program)^[t]) c

def initial {m k : Nat} (s : GaussControlTrace.State m k) : Config :=
  ⟨some (.base (BitMachineRawSequence.leftLabel (.copy .scan))),
    eBase baseInit,(GaussPivotPrepHigh64.start s).stk⟩

theorem run_add {c c' : Config} {t : Nat} (h : run t c = c') (u : Nat) :
    run (t+u) c = run u c' := by
  rw [Nat.add_comm,run,Function.iterate_add_apply]
  exact congrArg (run u) h

theorem guard_phase {m k : Nat} (s : GaussControlTrace.State m k) :
    ∃ t ≤ GaussPreparedGuard64.clock s,
      run t (initial s) =
        ⟨some .afterGuard,
          eBase (GaussPreparedGuard64.prepInit,.choose (some (decide (s.r < m)))),
          GaussPivotPrepHigh64.prepared s⟩ := by
  obtain ⟨t,ht,he⟩ := GaussPreparedGuard64.physical_prepared_guard s
  obtain ⟨u,hu,hr⟩ := BitMachineInline.outputs
    Label.base eBase Prod.fst (by intro v; rfl) (some .afterGuard)
    GaussPreparedGuard64.program program (by intro l; rfl)
    (GaussPreparedGuard64.initial s) t
    (by rw [he])
  change run u _ = BitMachineInline.cfg Label.base eBase (some .afterGuard)
    (((advance GaussPreparedGuard64.program)^[t])
      (GaussPreparedGuard64.initial s)) at hr
  rw [he] at hr
  refine ⟨u,hu.trans ht,?_⟩
  simpa only [initial,baseInit,GaussPreparedGuard64.initial,BitMachineInline.cfg] using hr

theorem branch_terminal {m k : Nat} (s : GaussControlTrace.State m k)
    (hr : ¬ s.r < m) :
    run 1 ⟨some .afterGuard,
      eBase (GaussPreparedGuard64.prepInit,.choose (some (decide (s.r < m)))),
      GaussPivotPrepHigh64.prepared s⟩ =
      ⟨some (.terminal .scan),eTerminal ((),none),GaussPivotPrepHigh64.prepared s⟩ := by
  simp [run,program,advance,TM2.step,TM2.stepAux,eBase,hr]

theorem branch_active {m k : Nat} (s : GaussControlTrace.State m k)
    (hr : s.r < m) :
    run 1 ⟨some .afterGuard,
      eBase (GaussPreparedGuard64.prepInit,.choose (some (decide (s.r < m)))),
      GaussPivotPrepHigh64.prepared s⟩ =
      ⟨some (.active activeStart),eActive activeInit,GaussPivotPrepHigh64.prepared s⟩ := by
  simp [run,program,advance,TM2.step,TM2.stepAux,eBase,hr]

def terminalResult {m k : Nat} (s : GaussControlTrace.State m k) : Bank → List Bool :=
  SourceClausePreservingBroadcast.result 31 63 [62]
    (GaussControlTrace.statePacket s) (GaussPivotPrepHigh64.prepared s)

/-- Exhausted rows take a real finite-control branch and copy the unchanged
state packet to output62. Every payload bit is charged, even on repeated calls. -/
theorem terminal_run {m k : Nat} (s : GaussControlTrace.State m k)
    (hr : ¬ s.r < m) :
    ∃ t ≤ GaussPreparedGuard64.clock s + 1 +
        (2*(GaussControlTrace.statePacket s).length+3),
      run t (initial s) =
        ⟨some .doneTerminal,eTerminal ((),none),terminalResult s⟩ ∧
      (terminalResult s) 62 = GaussControlTrace.statePacket s := by
  obtain ⟨a,ha,hguard⟩ := guard_phase s
  have hb := branch_terminal s hr
  have hsource : GaussPivotPrepHigh64.prepared s 31 =
      GaussControlTrace.statePacket s := GaussPivotPrepHigh64.prepared_original s
  have hscratch : GaussPivotPrepHigh64.prepared s 63 = [] :=
    GaussPivotPrepHigh64.prepared_high s 63 (by decide)
  have hcopy := SourceClausePreservingBroadcast.run_halt
    (31 : Bank) 63 [62] (by decide) (by decide) (by decide) (by decide)
    (GaussControlTrace.statePacket s) (GaussPivotPrepHigh64.prepared s)
    hsource hscratch
  obtain ⟨b,hbtime,he⟩ := BitMachineInline.outputs
    Label.terminal eTerminal (fun v => v.2.2) (by intro v; rfl)
    (some .doneTerminal)
    (SourceClausePreservingBroadcast.program (31 : Bank) 63 [62])
    program (by intro l; rfl)
    (⟨some .scan,((),none),GaussPivotPrepHigh64.prepared s⟩)
    (2*(GaussControlTrace.statePacket s).length+3)
    (by rw [hcopy])
  change run b _ = BitMachineInline.cfg Label.terminal eTerminal
    (some .doneTerminal) _ at he
  rw [hcopy] at he
  have hterm : run b
      ⟨some (.terminal .scan),eTerminal ((),none),GaussPivotPrepHigh64.prepared s⟩ =
      ⟨some .doneTerminal,eTerminal ((),none),terminalResult s⟩ := by
    simpa only [BitMachineInline.cfg,terminalResult] using he
  refine ⟨a+1+b,by omega,?_,?_⟩
  · rw [show a+1+b = a+(1+b) by omega,run_add hguard (1+b),run_add hb b]
    exact hterm
  · rw [terminalResult,SourceClausePreservingBroadcast.target_written
      31 63 [62] (by decide) (by decide) (by decide) _ _ 62 (by simp)]
    simp [GaussPivotPrepHigh64.prepared_high s 62 (by decide)]

def activeClock {m k : Nat} (s : GaussControlTrace.State m k) : Nat :=
  2*s.r+2*s.c+2*(GaussControlTrace.statePacket s).length+2*m+15 +
    GaussSearchRuntime.polynomialClock (GaussControlTrace.statePacket s).length + 2

theorem active_from_prepared {m k : Nat} (s : GaussControlTrace.State m k)
    (hc : s.c < k) :
    ∃ t ≤ activeClock s, ∃ vf, ∃ Sf : Fin 32 → List Bool,
      ((advance activeProgram)^[t])
        (⟨some activeStart,activeInit,GaussPivotPrepHigh64.prepared s⟩ :
          TM2.Cfg (fun _ : Bank => Bool) _ _) =
        ⟨none,(copyInit,.choose vf),GaussPivotSearchHigh64.searched s Sf⟩ := by
  obtain ⟨a,ha,hcopy⟩ := GaussPivotPrepSave64.copy_run s
  obtain ⟨b,hb,vf,Sf,hsearch,_⟩ := GaussPhysicalSearchClock.physical_search_clock s hc
  obtain ⟨t,ht,he⟩ := BitMachineRawSequence.runs
    GaussPivotPrepSave64.copyProgram GaussPivotSearchHigh64.program
    copyStart GaussPivotPrepSearchHigh64.searchLabel
    copyInit copyInit searchInit (.choose vf)
    (GaussPivotPrepHigh64.prepared s) (GaussPivotPrepSave64.saved s)
    (GaussPivotSearchHigh64.searched s Sf) a b
    (by simpa only [copyStart,copyInit] using hcopy)
    (by simpa only [GaussPivotPrepSearchHigh64.searchLabel,searchInit,
      GaussPivotPrepSearchHigh64.searchControl] using hsearch)
  exact ⟨t,by dsimp [activeClock]; omega,vf,Sf,
    by simpa only [activeProgram,activeStart,activeInit] using he⟩

/-- The active branch runs the actual backup copies and pivot search after
the actual preserving row guard. No pivot result or searched state is assumed. -/
theorem active_run {m k : Nat} (s : GaussControlTrace.State m k)
    (hr : s.r < m) (hc : s.c < k) :
    ∃ t ≤ GaussPreparedGuard64.clock s + 1 + activeClock s,
      ∃ vf, ∃ Sf : Fin 32 → List Bool,
        run t (initial s) =
          ⟨some .doneActive,eActive (copyInit,.choose vf),
            GaussPivotSearchHigh64.searched s Sf⟩ := by
  obtain ⟨a,ha,hguard⟩ := guard_phase s
  have hb := branch_active s hr
  obtain ⟨c,hc',vf,Sf,hsearch⟩ := active_from_prepared s hc
  obtain ⟨d,hd,he⟩ := BitMachineInline.outputs
    Label.active eActive (fun v => v.2.1) (by intro v; rfl)
    (some .doneActive) activeProgram program (by intro l; rfl)
    (⟨some activeStart,activeInit,GaussPivotPrepHigh64.prepared s⟩)
    c (by rw [hsearch])
  change run d _ = BitMachineInline.cfg Label.active eActive
    (some .doneActive) _ at he
  rw [hsearch] at he
  have hactive : run d
      ⟨some (.active activeStart),eActive activeInit,GaussPivotPrepHigh64.prepared s⟩ =
      ⟨some .doneActive,eActive (copyInit,.choose vf),
        GaussPivotSearchHigh64.searched s Sf⟩ := by
    simpa only [BitMachineInline.cfg] using he
  refine ⟨a+1+d,by omega,vf,Sf,?_⟩
  rw [show a+1+d=a+(1+d) by omega,run_add hguard (1+d),run_add hb d]
  exact hactive

#print axioms terminal_run
#print axioms active_from_prepared
#print axioms active_run

end
end CurrentAdditive.GaussGuardedFront64
