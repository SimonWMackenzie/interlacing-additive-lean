import Paper2.CodeFullCleanMeaning
import Paper2.CodeFullCleanBound
import Mathlib.Tactic

/-! One fixed controller repeatedly executes the physical clean step. Only
the saved finite success flag decides whether to re-enter; the next code,
output, public parameters, and tape already occupy their physical banks. -/

namespace Paper2.CodeFullRepeat

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open GeneratorCode GeneratorSerialization GeneratorPositive GeneratorStateSize

noncomputable section

abbrev Stack := CodeFullCleanStep.Stack
abbrev Control := CodeFullCleanStep.Control
abbrev Label := CodeFullCleanStep.Label ⊕ Unit
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def canonical : CodeFullCleanStep.Config :=
  CodeFullCleanStep.start ⟨[],[]⟩ [] 0 0

def entryLabel : CodeFullCleanStep.Label := canonical.l.get (by rfl)
def entryControl : Control := canonical.var

theorem entry_fixed (s : State) (tape : List Bool) (B R : Nat) :
    (CodeFullCleanStep.start s tape B R).l = some entryLabel ∧
    (CodeFullCleanStep.start s tape B R).var = entryControl := by
  constructor <;> rfl

def success (v : Control) : Bool :=
  CodeDrawResultHandler.savedStatus v.1.1.1 == some true

noncomputable def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l =>
      BitMachineInline.stmt Sum.inl id id (some (.inr ()))
        (CodeFullCleanStep.program l)
  | .inr () =>
      branch success
        (load (fun _ => entryControl) (goto (fun _ => .inl entryLabel)))
        halt

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

def sourceCfg (c : CodeFullCleanStep.Config) : Config :=
  BitMachineInline.cfg Sum.inl id (some (.inr ())) c

def routeCfg (v : Control) (S : Stack → List Bool) : Config :=
  ⟨some (.inr ()),v,S⟩

def start (s : State) (tape : List Bool) (B R : Nat) : Config :=
  sourceCfg (CodeFullCleanStep.start s tape B R)

private theorem id_read : Function.LeftInverse (id : Control → Control) id := by
  intro v; rfl

private theorem source_program (l : CodeFullCleanStep.Label) :
    program (.inl l) = BitMachineInline.stmt Sum.inl id id
      (some (.inr ())) (CodeFullCleanStep.program l) := rfl

theorem source_to_route (c d : CodeFullCleanStep.Config) (t : Nat)
    (hr : CodeFullCleanStep.run t c = d) (hd : d.l = none) :
    ∃ u ≤ t, run u (sourceCfg c) = routeCfg d.var d.stk := by
  have hh : (((advance CodeFullCleanStep.program)^[t]) c).l = none := by
    change (CodeFullCleanStep.run t c).l = none
    rw [hr]; exact hd
  obtain ⟨u,hu,hur⟩ := BitMachineInline.outputs Sum.inl id id
    id_read (some (.inr ())) CodeFullCleanStep.program program
    source_program c t hh
  refine ⟨u,hu,?_⟩
  change run u (sourceCfg c) =
    BitMachineInline.cfg Sum.inl id (some (.inr ()))
      (CodeFullCleanStep.run t c) at hur
  rw [hr] at hur
  simpa [routeCfg,BitMachineInline.cfg,hd] using hur

theorem route_success (v : Control) (S : Stack → List Bool)
    (hs : success v = true) :
    run 1 (routeCfg v S) =
      ⟨some (.inl entryLabel),entryControl,S⟩ := by
  simp [run,routeCfg,program,BitMachineEncoding.advance,
    TM2.step,TM2.stepAux,hs]

theorem route_stop (v : Control) (S : Stack → List Bool)
    (hs : success v = false) :
    run 1 (routeCfg v S) = ⟨none,v,S⟩ := by
  simp [run,routeCfg,program,BitMachineEncoding.advance,
    TM2.step,TM2.stepAux,hs]

theorem route_to_start (v : Control) (S : Stack → List Bool)
    (s : State) (tape : List Bool) (B R : Nat)
    (hs : success v = true)
    (hbank : S = (CodeFullCleanStep.start s tape B R).stk) :
    run 1 (routeCfg v S) = start s tape B R := by
  rw [route_success v S hs]
  obtain ⟨hl,hv⟩ := entry_fixed s tape B R
  simp [start,sourceCfg,BitMachineInline.cfg,hl,hv,hbank]

theorem reenter_from_reached (s next : State) (tape residual : List Bool)
    (B R : Nat) (d : CodeAdminBranchJoin.Config) (t : Nat)
    (hr : CodeAdminBranchJoin.run t
      (CodeAdminBranchJoin.start s tape B R) = d)
    (hd : d.l = none)
    (hs : success ((d.var,none) : Control) = true)
    (hbank : (CodeInterpreterReset.final d.var d.stk).stk =
      (CodeAdminBranchJoin.start next residual B R).stk) :
    ∃ u ≤ t + CodeInterpreterReset.clock d.stk + 1,
      run u (start s tape B R) = start next residual B R := by
  obtain ⟨a,ha,har⟩ := CodeFullCleanStep.raw_clean_from_reached
    s tape B R d t hr hd
  let clean := CodeFullCleanStep.resetCfg
    (CodeInterpreterReset.final d.var d.stk)
  have hc : clean.l = none := rfl
  obtain ⟨b,hb,hbr⟩ := source_to_route
    (CodeFullCleanStep.start s tape B R) clean a har hc
  have hs' : success clean.var = true := hs
  have hbank' : clean.stk =
      (CodeFullCleanStep.start next residual B R).stk := hbank
  have hroute := route_to_start clean.var clean.stk
    next residual B R hs' hbank'
  refine ⟨b+1,by omega,?_⟩
  have hadd : run (b+1) (start s tape B R) =
      run 1 (run b (start s tape B R)) := by
    change ((advance program)^[b+1]) (start s tape B R) =
      ((advance program)^[1])
        (((advance program)^[b]) (start s tape B R))
    rw [Nat.add_comm b 1,Function.iterate_add_apply]
  rw [hadd]
  change run b (sourceCfg (CodeFullCleanStep.start s tape B R)) =
    routeCfg clean.var clean.stk at hbr
  change run 1 (run b (sourceCfg (CodeFullCleanStep.start s tape B R))) = _
  rw [hbr]
  exact hroute

theorem stop_from_reached (s : State) (tape : List Bool)
    (B R : Nat) (d : CodeAdminBranchJoin.Config) (t : Nat)
    (hr : CodeAdminBranchJoin.run t
      (CodeAdminBranchJoin.start s tape B R) = d)
    (hd : d.l = none)
    (hs : success ((d.var,none) : Control) = false) :
    ∃ u ≤ t + CodeInterpreterReset.clock d.stk + 1,
      run u (start s tape B R) =
        ⟨none,(d.var,none),CodeInterpreterReset.resetBank d.stk⟩ := by
  obtain ⟨a,ha,har⟩ := CodeFullCleanStep.raw_clean_from_reached
    s tape B R d t hr hd
  let clean := CodeFullCleanStep.resetCfg
    (CodeInterpreterReset.final d.var d.stk)
  obtain ⟨b,hb,hbr⟩ := source_to_route
    (CodeFullCleanStep.start s tape B R) clean a har rfl
  have hstop := route_stop clean.var clean.stk hs
  refine ⟨b+1,by omega,?_⟩
  have hadd : run (b+1) (start s tape B R) =
      run 1 (run b (start s tape B R)) := by
    change ((advance program)^[b+1]) (start s tape B R) =
      ((advance program)^[1])
        (((advance program)^[b]) (start s tape B R))
    rw [Nat.add_comm b 1,Function.iterate_add_apply]
  rw [hadd]
  change run 1 (run b (sourceCfg (CodeFullCleanStep.start s tape B R))) = _
  rw [hbr]
  exact hstop

theorem ticket_reenters (root : Code) (s : State)
    (hp : PositiveState s) (ht : Trace root s)
    (D : Nat) (hD : 0 < D) (cs : List Code)
    (outputWord : List Bool)
    (hstate : GeneratorCode.normalize s =
      ⟨.ticket D :: cs,outputWord.reverse⟩)
    (B R N : Nat) (hB : Nat.clog 2 D ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (q : Fin D) (hq : CappedSampler.runWideBits D B R hB tape.1 = some q) :
    ∃ u,
      run u (start s (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R) =
        start (GeneratorCode.advance
          ⟨.ticket D::cs,outputWord.reverse⟩ q.val)
          (RecursiveSamplingTape.writeTape B R N tape.2).val B R := by
  obtain ⟨t,F,ht0,hr⟩ := CodeAdminBranchJoin.ticket_success_from_raw
    root s hp ht D hD cs outputWord hstate B R N hB tape q hq
  let raw := CodeAdminDraw.drawResult D B R N hB tape .ticket
    (CodeAdminNormalization.todoWord cs) (List.replicate D true)
    [] [] outputWord F
  let handled := CodeDrawResultHandler.framed raw.var raw.stk
    (CodeDrawOutput.cfg none none []
      (((RecursiveLabelCodecScratch.finCodec D).encode q).reverse ++ outputWord))
  let joined := CodeAdminResultJoin.resultCfg handled
  let endpoint : CodeAdminBranchJoin.Config :=
    ⟨none,CodeAdminBranchJoin.joinLift joined.var,joined.stk⟩
  have hsraw := (CodeDrawResultHandler.result_status D B R N hB tape .ticket
    (CodeAdminNormalization.todoWord cs) (List.replicate D true)
    [] [] outputWord F).1
  have hs : success ((endpoint.var,none) : Control) = true := by
    change (CodeDrawResultHandler.savedStatus raw.var == some true) = true
    rw [hsraw,hq]
    rfl
  have hbank := CodeFullCleanMeaning.ticket_ready_bank D B R N hD hB
    tape cs outputWord.reverse F q
  have hbank' : (CodeInterpreterReset.final endpoint.var endpoint.stk).stk =
      (CodeAdminBranchJoin.start
        (GeneratorCode.advance ⟨.ticket D::cs,outputWord.reverse⟩ q.val)
        (RecursiveSamplingTape.writeTape B R N tape.2).val B R).stk := by
    simpa [raw,handled,joined,endpoint] using hbank
  obtain ⟨u,hu,hru⟩ := reenter_from_reached s
    (GeneratorCode.advance ⟨.ticket D::cs,outputWord.reverse⟩ q.val)
    (RecursiveSamplingTape.writeTape B R (N+1) tape).val
    (RecursiveSamplingTape.writeTape B R N tape.2).val
    B R endpoint t hr rfl hs hbank'
  exact ⟨u,hru⟩

theorem bit_reenters (root : Code) (s : State)
    (hp : PositiveState s) (ht : Trace root s)
    (cs : List Code) (outputWord : List Bool)
    (hstate : GeneratorCode.normalize s =
      ⟨.bit :: cs,outputWord.reverse⟩)
    (B R N : Nat) (hB : Nat.clog 2 2 ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (q : Fin 2) (hq : CappedSampler.runWideBits 2 B R hB tape.1 = some q) :
    ∃ u,
      run u (start s (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R) =
        start (GeneratorCode.advance
          ⟨.bit::cs,outputWord.reverse⟩ q.val)
          (RecursiveSamplingTape.writeTape B R N tape.2).val B R := by
  obtain ⟨t,F,ht0,hr⟩ := CodeAdminBranchJoin.bit_success_from_raw
    root s hp ht cs outputWord hstate B R N hB tape q hq
  let raw := CodeAdminDraw.drawResult 2 B R N hB tape .bit
    (CodeAdminNormalization.todoWord cs) [] [] [] outputWord F
  let handled := CodeDrawResultHandler.framed raw.var raw.stk
    (CodeDrawOutput.cfg none none [] (decide (q.val=1)::outputWord))
  let joined := CodeAdminResultJoin.resultCfg handled
  let endpoint : CodeAdminBranchJoin.Config :=
    ⟨none,CodeAdminBranchJoin.joinLift joined.var,joined.stk⟩
  have hsraw := (CodeDrawResultHandler.result_status 2 B R N hB tape .bit
    (CodeAdminNormalization.todoWord cs) [] [] [] outputWord F).1
  have hs : success ((endpoint.var,none) : Control) = true := by
    change (CodeDrawResultHandler.savedStatus raw.var == some true) = true
    rw [hsraw,hq]
    rfl
  have hbank := CodeFullCleanMeaning.bit_ready_bank B R N hB
    tape cs outputWord.reverse F q
  have hbank' : (CodeInterpreterReset.final endpoint.var endpoint.stk).stk =
      (CodeAdminBranchJoin.start
        (GeneratorCode.advance ⟨.bit::cs,outputWord.reverse⟩ q.val)
        (RecursiveSamplingTape.writeTape B R N tape.2).val B R).stk := by
    simpa [raw,handled,joined,endpoint] using hbank
  obtain ⟨u,hu,hru⟩ := reenter_from_reached s
    (GeneratorCode.advance ⟨.bit::cs,outputWord.reverse⟩ q.val)
    (RecursiveSamplingTape.writeTape B R (N+1) tape).val
    (RecursiveSamplingTape.writeTape B R N tape.2).val
    B R endpoint t hr rfl hs hbank'
  exact ⟨u,hru⟩

theorem branch_reenters (root : Code) (s : State)
    (hp : PositiveState s) (ht : Trace root s)
    (D a b : Nat) (hD : 0 < D) (f g h : Code)
    (cs : List Code) (outputWord : List Bool)
    (hstate : GeneratorCode.normalize s =
      ⟨.branch3 D a b f g h :: cs,outputWord.reverse⟩)
    (B R N : Nat) (hB : Nat.clog 2 D ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (q : Fin D) (hq : CappedSampler.runWideBits D B R hB tape.1 = some q) :
    ∃ u,
      run u (start s (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R) =
        start (GeneratorCode.advance
          ⟨.branch3 D a b f g h::cs,outputWord.reverse⟩ q.val)
          (RecursiveSamplingTape.writeTape B R N tape.2).val B R := by
  obtain ⟨t,F,ht0,hr⟩ := CodeAdminBranchJoin.branch_selected_from_raw
    root s hp ht D a b hD f g h cs outputWord hstate B R N hB tape q hq
  let tail := BranchSelection.inputWord f g h
    (CodeAdminNormalization.todoWord cs)
  let base := CodeHeaderDraw.resultCfg D B R N hB tape .branch3 tail
    (List.replicate D true) (List.replicate a true)
    (List.replicate b true) outputWord F
  let raw := CodeAdminDraw.drawResult D B R N hB tape .branch3 tail
    (List.replicate D true) (List.replicate a true)
    (List.replicate b true) outputWord F
  let joined : CodeAdminResultJoin.Config :=
    CodeAdminResultJoin.resultCfg ⟨none,(raw.var,none),raw.stk⟩
  let selected := CodeBranchAdapter.final base.var base.stk
    (List.replicate D true) outputWord q.val a b f g h
    (CodeAdminNormalization.todoWord cs)
  let endpoint := CodeAdminBranchJoin.branchCfg joined.var selected
  have hsraw := (CodeDrawResultHandler.result_status D B R N hB tape .branch3
    tail (List.replicate D true) (List.replicate a true)
    (List.replicate b true) outputWord F).1
  have hs : success ((endpoint.var,none) : Control) = true := by
    change (CodeDrawResultHandler.savedStatus raw.var == some true) = true
    rw [hsraw,hq]
    rfl
  have hbank := CodeFullCleanMeaning.branch_ready_bank D a b B R N hD hB
    tape f g h cs outputWord.reverse F q
  have hbank' : (CodeInterpreterReset.final endpoint.var endpoint.stk).stk =
      (CodeAdminBranchJoin.start
        (GeneratorCode.advance
          ⟨.branch3 D a b f g h::cs,outputWord.reverse⟩ q.val)
        (RecursiveSamplingTape.writeTape B R N tape.2).val B R).stk := by
    simpa [tail,base,raw,joined,selected,endpoint] using hbank
  obtain ⟨u,hu,hru⟩ := reenter_from_reached s
    (GeneratorCode.advance
      ⟨.branch3 D a b f g h::cs,outputWord.reverse⟩ q.val)
    (RecursiveSamplingTape.writeTape B R (N+1) tape).val
    (RecursiveSamplingTape.writeTape B R N tape.2).val
    B R endpoint t hr rfl hs hbank'
  exact ⟨u,hru⟩

theorem done_stops (root : Code) (s : State)
    (hp : PositiveState s) (ht : Trace root s)
    (h : (GeneratorCode.normalize s).todo = [])
    (tape : List Bool) (B R : Nat) :
    ∃ u,
      let d := CodeAdminDraw.doneCfg
        (GeneratorCode.normalize s).output.reverse tape B R
      let j : CodeAdminResultJoin.Config :=
        CodeAdminResultJoin.resultCfg ⟨none,(d.var,none),d.stk⟩
      let endpoint : CodeAdminBranchJoin.Config :=
        ⟨none,CodeAdminBranchJoin.joinLift j.var,j.stk⟩
      run u (start s tape B R) =
        ⟨none,(endpoint.var,none),CodeInterpreterReset.resetBank endpoint.stk⟩ := by
  obtain ⟨t,ht0,hr⟩ := CodeAdminBranchJoin.done_from_raw
    root s hp ht h tape B R
  let d := CodeAdminDraw.doneCfg
    (GeneratorCode.normalize s).output.reverse tape B R
  let j : CodeAdminResultJoin.Config :=
    CodeAdminResultJoin.resultCfg ⟨none,(d.var,none),d.stk⟩
  let endpoint : CodeAdminBranchJoin.Config :=
    ⟨none,CodeAdminBranchJoin.joinLift j.var,j.stk⟩
  have hs : success ((endpoint.var,none) : Control) = false := by
    simp [success,endpoint,j,d,CodeAdminBranchJoin.joinLift,
      CodeAdminResultJoin.resultCfg,BitMachineInline.cfg,
      CodeDrawResultHandler.savedStatus,CodeAdminDraw.doneCfg,
      CodeAdminDraw.drawControl,CodeHeaderDraw.drawInitialControl,
      LoadedTicketMachine.statusStartControl]
  obtain ⟨u,hu,hru⟩ := stop_from_reached s tape B R endpoint t hr rfl hs
  exact ⟨u,hru⟩

theorem failure_stops (root : Code) (s : State)
    (hp : PositiveState s) (ht : Trace root s)
    (c : Code) (cs : List Code) (outputWord : List Bool)
    (hstate : GeneratorCode.normalize s = ⟨c::cs,outputWord.reverse⟩)
    (hc : DrawHead c) (B R N : Nat)
    (hB : Nat.clog 2 (request (GeneratorCode.normalize s)) ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (hq : CappedSampler.runWideBits
      (request (GeneratorCode.normalize s)) B R hB tape.1 = none) :
    ∃ u F,
      let d := CodeAdminDraw.drawResult
        (request (GeneratorCode.normalize s)) B R N hB tape
        (CodeHeaderMachine.headerKind c)
        (CodeHeaderMachine.headerTail c (CodeAdminNormalization.todoWord cs))
        (CodeHeaderMachine.headerN c) (CodeHeaderMachine.headerA c)
        (CodeHeaderMachine.headerB c) outputWord F
      let j : CodeAdminResultJoin.Config :=
        CodeAdminResultJoin.resultCfg ⟨none,(d.var,none),d.stk⟩
      let endpoint : CodeAdminBranchJoin.Config :=
        ⟨none,CodeAdminBranchJoin.joinLift j.var,j.stk⟩
      run u (start s (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R) =
        ⟨none,(endpoint.var,none),CodeInterpreterReset.resetBank endpoint.stk⟩ := by
  obtain ⟨t,F,ht0,hr⟩ := CodeAdminBranchJoin.failure_from_raw
    root s hp ht c cs outputWord hstate hc B R N hB tape hq
  let d := CodeAdminDraw.drawResult
    (request (GeneratorCode.normalize s)) B R N hB tape
    (CodeHeaderMachine.headerKind c)
    (CodeHeaderMachine.headerTail c (CodeAdminNormalization.todoWord cs))
    (CodeHeaderMachine.headerN c) (CodeHeaderMachine.headerA c)
    (CodeHeaderMachine.headerB c) outputWord F
  let j : CodeAdminResultJoin.Config :=
    CodeAdminResultJoin.resultCfg ⟨none,(d.var,none),d.stk⟩
  let endpoint : CodeAdminBranchJoin.Config :=
    ⟨none,CodeAdminBranchJoin.joinLift j.var,j.stk⟩
  have hsraw := (CodeDrawResultHandler.result_status
    (request (GeneratorCode.normalize s)) B R N hB tape
    (CodeHeaderMachine.headerKind c)
    (CodeHeaderMachine.headerTail c (CodeAdminNormalization.todoWord cs))
    (CodeHeaderMachine.headerN c) (CodeHeaderMachine.headerA c)
    (CodeHeaderMachine.headerB c) outputWord F).1
  have hs : success ((endpoint.var,none) : Control) = false := by
    change (CodeDrawResultHandler.savedStatus d.var == some true) = false
    rw [hsraw,hq]
    rfl
  obtain ⟨u,hu,hru⟩ := stop_from_reached s
    (RecursiveSamplingTape.writeTape B R (N+1) tape).val
    B R endpoint t hr rfl hs
  exact ⟨u,F,hru⟩

#print axioms source_to_route
#print axioms route_to_start
#print axioms reenter_from_reached
#print axioms stop_from_reached
#print axioms ticket_reenters
#print axioms bit_reenters
#print axioms branch_reenters
#print axioms done_stops
#print axioms failure_stops

end
end Paper2.CodeFullRepeat
