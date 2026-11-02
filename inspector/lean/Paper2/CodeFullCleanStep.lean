import Paper2.CodeAdminBranchJoin
import Paper2.CodeInterpreterReset
import Mathlib.Tactic

/-! A fixed TM2 program from an encoded first-order state through one
physical draw, output/branch action, and exact bank reset. -/

namespace Paper2.CodeFullCleanStep

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open GeneratorCode GeneratorSerialization GeneratorPositive GeneratorStateSize

noncomputable section

abbrev Stack := CodeAdminBranchJoin.Stack
abbrev Control := CodeInterpreterReset.Control CodeAdminBranchJoin.Control
abbrev Label := CodeAdminBranchJoin.Label ⊕ CodeInterpreterReset.Label
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

instance : Fintype Stack := inferInstance

noncomputable def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l =>
      BitMachineInline.stmt Sum.inl (fun v => (v,none)) Prod.fst
        (some (.inr (.inl 0))) (CodeAdminBranchJoin.program l)
  | .inr l =>
      BitMachineInline.stmt Sum.inr id id none
        (CodeInterpreterReset.program (Flag := CodeAdminBranchJoin.Control) l)

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

def sourceCfg (c : CodeAdminBranchJoin.Config) : Config :=
  BitMachineInline.cfg Sum.inl (fun v => (v,none))
    (some (.inr (.inl 0))) c

def resetCfg (c : CodeInterpreterReset.Config CodeAdminBranchJoin.Control) :
    Config := BitMachineInline.cfg Sum.inr id none c

def start (s : State) (tape : List Bool) (B R : Nat) : Config :=
  sourceCfg (CodeAdminBranchJoin.start s tape B R)

private theorem source_read :
    Function.LeftInverse (Prod.fst : Control → CodeAdminBranchJoin.Control)
      (fun v : CodeAdminBranchJoin.Control => (v,(none : Option Bool))) := by
  intro v; rfl

private theorem reset_read : Function.LeftInverse (id : Control → Control) id := by
  intro v; rfl

private theorem source_program (l : CodeAdminBranchJoin.Label) :
    program (.inl l) =
      BitMachineInline.stmt Sum.inl (fun v => (v,none)) Prod.fst
        (some (.inr (.inl 0))) (CodeAdminBranchJoin.program l) := rfl

private theorem reset_program (l : CodeInterpreterReset.Label) :
    program (.inr l) =
      BitMachineInline.stmt Sum.inr id id none
        (CodeInterpreterReset.program (Flag := CodeAdminBranchJoin.Control) l) := rfl

theorem source_to_reset (c d : CodeAdminBranchJoin.Config) (t : Nat)
    (hr : CodeAdminBranchJoin.run t c = d) (hd : d.l = none) :
    ∃ u ≤ t, run u (sourceCfg c) =
      resetCfg (CodeInterpreterReset.initial d.var d.stk) := by
  have hh : (((advance CodeAdminBranchJoin.program)^[t]) c).l = none := by
    change (CodeAdminBranchJoin.run t c).l = none
    rw [hr]; exact hd
  obtain ⟨u,hu,hur⟩ := BitMachineInline.outputs Sum.inl
    (fun v => (v,none)) Prod.fst source_read
    (some (.inr (.inl 0))) CodeAdminBranchJoin.program program
    source_program c t hh
  refine ⟨u,hu,?_⟩
  change run u (sourceCfg c) =
    BitMachineInline.cfg Sum.inl (fun v => (v,none))
      (some (.inr (.inl 0))) (CodeAdminBranchJoin.run t c) at hur
  rw [hr] at hur
  simpa [resetCfg,CodeInterpreterReset.initial,BitMachineInline.cfg,hd] using hur

theorem reset_to_end (c d : CodeInterpreterReset.Config CodeAdminBranchJoin.Control)
    (t : Nat)
    (hr : ((advance (CodeInterpreterReset.program
      (Flag := CodeAdminBranchJoin.Control)))^[t]) c = d)
    (hd : d.l = none) :
    ∃ u ≤ t, run u (resetCfg c) = resetCfg d := by
  have hh : (((advance (CodeInterpreterReset.program
      (Flag := CodeAdminBranchJoin.Control)))^[t]) c).l = none := by
    rw [hr]; exact hd
  obtain ⟨u,hu,hur⟩ := BitMachineInline.outputs
    Sum.inr id id reset_read none
    (CodeInterpreterReset.program (Flag := CodeAdminBranchJoin.Control))
    program reset_program c t hh
  refine ⟨u,hu,?_⟩
  change run u (resetCfg c) =
    resetCfg (((advance (CodeInterpreterReset.program
      (Flag := CodeAdminBranchJoin.Control)))^[t]) c) at hur
  rw [hr] at hur
  exact hur

theorem to_clean (c d : CodeAdminBranchJoin.Config) (t : Nat)
    (hr : CodeAdminBranchJoin.run t c = d) (hd : d.l = none) :
    ∃ u ≤ t+CodeInterpreterReset.clock d.stk,
      run u (sourceCfg c) =
        resetCfg (CodeInterpreterReset.final d.var d.stk) := by
  obtain ⟨a,ha,har⟩ := source_to_reset c d t hr hd
  have hreset := CodeInterpreterReset.reset_run d.var d.stk
  obtain ⟨b,hb,hbr⟩ := reset_to_end
    (CodeInterpreterReset.initial d.var d.stk)
    (CodeInterpreterReset.final d.var d.stk)
    (CodeInterpreterReset.clock d.stk) hreset rfl
  refine ⟨b+a,by omega,?_⟩
  have hadd : run (b+a) (sourceCfg c) =
      run b (run a (sourceCfg c)) := by
    simp [run,Function.iterate_add_apply]
  rw [hadd,har,hbr]

theorem raw_clean_from_reached (s : State) (tape : List Bool) (B R : Nat)
    (d : CodeAdminBranchJoin.Config) (t : Nat)
    (hr : CodeAdminBranchJoin.run t
      (CodeAdminBranchJoin.start s tape B R) = d)
    (hd : d.l = none) :
    ∃ u ≤ t+CodeInterpreterReset.clock d.stk,
      run u (start s tape B R) =
        resetCfg (CodeInterpreterReset.final d.var d.stk) := by
  simpa [start] using to_clean
    (CodeAdminBranchJoin.start s tape B R) d t hr hd

theorem ticket_success_from_raw (root : Code) (s : State)
    (hp : PositiveState s) (ht : Trace root s)
    (D : Nat) (hD : 0 < D) (cs : List Code)
    (outputWord : List Bool)
    (hstate : GeneratorCode.normalize s =
      ⟨.ticket D :: cs,outputWord.reverse⟩)
    (B R N : Nat) (hB : Nat.clog 2 D ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (q : Fin D) (hq : CappedSampler.runWideBits D B R hB tape.1 = some q) :
    ∃ t F,
      let raw := CodeAdminDraw.drawResult D B R N hB tape .ticket
        (CodeAdminNormalization.todoWord cs) (List.replicate D true)
        [] [] outputWord F
      let handled := CodeDrawResultHandler.framed raw.var raw.stk
        (CodeDrawOutput.cfg none none []
          (((RecursiveLabelCodecScratch.finCodec D).encode q).reverse ++ outputWord))
      let joined := CodeAdminResultJoin.resultCfg handled
      let endpoint : CodeAdminBranchJoin.Config :=
        ⟨none,CodeAdminBranchJoin.joinLift joined.var,joined.stk⟩
      t ≤ 13*(codeSize root+3)^2 + 3 +
        CodeAdminDraw.drawClock D B R + (D+2) +
        CodeInterpreterReset.clock endpoint.stk ∧
      run t (start s (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R) =
        resetCfg (CodeInterpreterReset.final endpoint.var endpoint.stk) := by
  let input := (RecursiveSamplingTape.writeTape B R (N+1) tape).val
  obtain ⟨ta,F,hta,ha⟩ := CodeAdminBranchJoin.ticket_success_from_raw
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
  obtain ⟨tb,htb,hbr⟩ := to_clean
    (CodeAdminBranchJoin.start s input B R) endpoint ta ha rfl
  refine ⟨tb,F,?_,by simpa [input,raw,handled,joined,endpoint] using hbr⟩
  change tb ≤ 13*(codeSize root+3)^2 + 3 +
    CodeAdminDraw.drawClock D B R + (D+2) +
    CodeInterpreterReset.clock endpoint.stk
  omega

theorem done_from_raw (root : Code) (s : State)
    (hp : PositiveState s) (ht : Trace root s)
    (h : (GeneratorCode.normalize s).todo = [])
    (tape : List Bool) (B R : Nat) :
    ∃ t,
      let d := CodeAdminDraw.doneCfg
        (GeneratorCode.normalize s).output.reverse tape B R
      let j : CodeAdminResultJoin.Config :=
        CodeAdminResultJoin.resultCfg ⟨none,(d.var,none),d.stk⟩
      let endpoint : CodeAdminBranchJoin.Config :=
        ⟨none,CodeAdminBranchJoin.joinLift j.var,j.stk⟩
      t ≤ 13*(codeSize root+3)^2+3+
        CodeInterpreterReset.clock endpoint.stk ∧
      run t (start s tape B R) =
        resetCfg (CodeInterpreterReset.final endpoint.var endpoint.stk) := by
  obtain ⟨ta,hta,ha⟩ := CodeAdminBranchJoin.done_from_raw
    root s hp ht h tape B R
  let d := CodeAdminDraw.doneCfg
    (GeneratorCode.normalize s).output.reverse tape B R
  let j : CodeAdminResultJoin.Config :=
    CodeAdminResultJoin.resultCfg ⟨none,(d.var,none),d.stk⟩
  let endpoint : CodeAdminBranchJoin.Config :=
    ⟨none,CodeAdminBranchJoin.joinLift j.var,j.stk⟩
  obtain ⟨tb,htb,hbr⟩ := raw_clean_from_reached
    s tape B R endpoint ta ha rfl
  refine ⟨tb,?_,by simpa [d,j,endpoint] using hbr⟩
  change tb ≤ 13*(codeSize root+3)^2+3+
    CodeInterpreterReset.clock endpoint.stk
  omega

theorem failure_from_raw (root : Code) (s : State)
    (hp : PositiveState s) (ht : Trace root s)
    (c : Code) (cs : List Code) (outputWord : List Bool)
    (hstate : GeneratorCode.normalize s = ⟨c::cs,outputWord.reverse⟩)
    (hc : DrawHead c)
    (B R N : Nat)
    (hB : Nat.clog 2 (request (GeneratorCode.normalize s)) ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (hq : CappedSampler.runWideBits
      (request (GeneratorCode.normalize s)) B R hB tape.1 = none) :
    ∃ t F,
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
      t ≤ 13*(codeSize root+3)^2+3+
        CodeAdminDraw.drawClock (request (GeneratorCode.normalize s)) B R+
        CodeInterpreterReset.clock endpoint.stk ∧
      run t (start s (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R) =
        resetCfg (CodeInterpreterReset.final endpoint.var endpoint.stk) := by
  let input := (RecursiveSamplingTape.writeTape B R (N+1) tape).val
  obtain ⟨ta,F,hta,ha⟩ := CodeAdminBranchJoin.failure_from_raw
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
  obtain ⟨tb,htb,hbr⟩ := raw_clean_from_reached
    s input B R endpoint ta ha rfl
  refine ⟨tb,F,?_,by simpa [input,d,j,endpoint] using hbr⟩
  change tb ≤ 13*(codeSize root+3)^2+3+
    CodeAdminDraw.drawClock (request (GeneratorCode.normalize s)) B R+
    CodeInterpreterReset.clock endpoint.stk
  omega

theorem bit_success_from_raw (root : Code) (s : State)
    (hp : PositiveState s) (ht : Trace root s)
    (cs : List Code) (outputWord : List Bool)
    (hstate : GeneratorCode.normalize s = ⟨.bit :: cs,outputWord.reverse⟩)
    (B R N : Nat) (hB : Nat.clog 2 2 ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (q : Fin 2) (hq : CappedSampler.runWideBits 2 B R hB tape.1 = some q) :
    ∃ t F,
      let raw := CodeAdminDraw.drawResult 2 B R N hB tape .bit
        (CodeAdminNormalization.todoWord cs) [] [] [] outputWord F
      let handled := CodeDrawResultHandler.framed raw.var raw.stk
        (CodeDrawOutput.cfg none none [] (decide (q.val=1)::outputWord))
      let joined := CodeAdminResultJoin.resultCfg handled
      let endpoint : CodeAdminBranchJoin.Config :=
        ⟨none,CodeAdminBranchJoin.joinLift joined.var,joined.stk⟩
      t ≤ 13*(codeSize root+3)^2 + 2 +
        CodeAdminDraw.drawClock 2 B R + 4 +
        CodeInterpreterReset.clock endpoint.stk ∧
      run t (start s (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R) =
        resetCfg (CodeInterpreterReset.final endpoint.var endpoint.stk) := by
  let input := (RecursiveSamplingTape.writeTape B R (N+1) tape).val
  obtain ⟨ta,F,hta,ha⟩ := CodeAdminBranchJoin.bit_success_from_raw
    root s hp ht cs outputWord hstate B R N hB tape q hq
  let raw := CodeAdminDraw.drawResult 2 B R N hB tape .bit
    (CodeAdminNormalization.todoWord cs) [] [] [] outputWord F
  let handled := CodeDrawResultHandler.framed raw.var raw.stk
    (CodeDrawOutput.cfg none none [] (decide (q.val=1)::outputWord))
  let joined := CodeAdminResultJoin.resultCfg handled
  let endpoint : CodeAdminBranchJoin.Config :=
    ⟨none,CodeAdminBranchJoin.joinLift joined.var,joined.stk⟩
  obtain ⟨tb,htb,hbr⟩ := raw_clean_from_reached
    s input B R endpoint ta ha rfl
  refine ⟨tb,F,?_,by simpa [input,raw,handled,joined,endpoint] using hbr⟩
  change tb ≤ 13*(codeSize root+3)^2 + 2 +
    CodeAdminDraw.drawClock 2 B R + 4 +
    CodeInterpreterReset.clock endpoint.stk
  omega

theorem branch_success_from_raw (root : Code) (s : State)
    (hp : PositiveState s) (ht : Trace root s)
    (D a b : Nat) (hD : 0 < D) (f g h : Code)
    (cs : List Code) (outputWord : List Bool)
    (hstate : GeneratorCode.normalize s =
      ⟨.branch3 D a b f g h :: cs,outputWord.reverse⟩)
    (B R N : Nat) (hB : Nat.clog 2 D ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (q : Fin D) (hq : CappedSampler.runWideBits D B R hB tape.1 = some q) :
    ∃ t F,
      let base := CodeHeaderDraw.resultCfg D B R N hB tape .branch3
        (BranchSelection.inputWord f g h (CodeAdminNormalization.todoWord cs))
        (List.replicate D true) (List.replicate a true)
        (List.replicate b true) outputWord F
      let raw := CodeAdminDraw.drawResult D B R N hB tape .branch3
        (BranchSelection.inputWord f g h (CodeAdminNormalization.todoWord cs))
        (List.replicate D true) (List.replicate a true)
        (List.replicate b true) outputWord F
      let joined : CodeAdminResultJoin.Config :=
        CodeAdminResultJoin.resultCfg ⟨none,(raw.var,none),raw.stk⟩
      let selected := CodeBranchAdapter.final base.var base.stk
        (List.replicate D true) outputWord q.val a b f g h
        (CodeAdminNormalization.todoWord cs)
      let endpoint := CodeAdminBranchJoin.branchCfg joined.var selected
      t ≤ 13*(codeSize root+3)^2 + 3 +
        CodeAdminDraw.drawClock D B R +
        70*(q.val+a+b+
          (BranchSelection.inputWord f g h (CodeAdminNormalization.todoWord cs)).length+1) +
        CodeInterpreterReset.clock endpoint.stk ∧
      run t (start s (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R) =
        resetCfg (CodeInterpreterReset.final endpoint.var endpoint.stk) := by
  let input := (RecursiveSamplingTape.writeTape B R (N+1) tape).val
  obtain ⟨ta,F,hta,ha⟩ := CodeAdminBranchJoin.branch_selected_from_raw
    root s hp ht D a b hD f g h cs outputWord hstate B R N hB tape q hq
  let base := CodeHeaderDraw.resultCfg D B R N hB tape .branch3
    (BranchSelection.inputWord f g h (CodeAdminNormalization.todoWord cs))
    (List.replicate D true) (List.replicate a true)
    (List.replicate b true) outputWord F
  let raw := CodeAdminDraw.drawResult D B R N hB tape .branch3
    (BranchSelection.inputWord f g h (CodeAdminNormalization.todoWord cs))
    (List.replicate D true) (List.replicate a true)
    (List.replicate b true) outputWord F
  let joined : CodeAdminResultJoin.Config :=
    CodeAdminResultJoin.resultCfg ⟨none,(raw.var,none),raw.stk⟩
  let selected := CodeBranchAdapter.final base.var base.stk
    (List.replicate D true) outputWord q.val a b f g h
    (CodeAdminNormalization.todoWord cs)
  let endpoint := CodeAdminBranchJoin.branchCfg joined.var selected
  obtain ⟨tb,htb,hbr⟩ := raw_clean_from_reached
    s input B R endpoint ta ha rfl
  refine ⟨tb,F,?_,by simpa [input,base,raw,joined,selected,endpoint] using hbr⟩
  change tb ≤ 13*(codeSize root+3)^2 + 3 +
    CodeAdminDraw.drawClock D B R +
    70*(q.val+a+b+
      (BranchSelection.inputWord f g h (CodeAdminNormalization.todoWord cs)).length+1) +
    CodeInterpreterReset.clock endpoint.stk
  omega

#print axioms to_clean
#print axioms done_from_raw
#print axioms failure_from_raw
#print axioms ticket_success_from_raw
#print axioms bit_success_from_raw
#print axioms branch_success_from_raw

end
end Paper2.CodeFullCleanStep
