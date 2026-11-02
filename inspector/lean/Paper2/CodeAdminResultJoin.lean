import Paper2.CodeDrawResultHandler
import Mathlib.Tactic

/-! One fixed program table for encoded administration, one loaded draw,
and status-preserving ticket/bit result handling. -/

namespace Paper2.CodeAdminResultJoin

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open GeneratorCode GeneratorSerialization GeneratorPositive GeneratorStateSize

noncomputable section

abbrev Stack := CodeAdminDraw.Stack
abbrev Control := CodeDrawResultHandler.Control
abbrev Label := CodeAdminDraw.Label ⊕ CodeDrawResultHandler.Label
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

noncomputable def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l =>
      BitMachineInline.stmt Sum.inl (fun v => (v,none)) Prod.fst
        (some (.inr (.inl .dispatch))) (CodeAdminDraw.program l)
  | .inr l =>
      BitMachineInline.stmt Sum.inr id id none
        (CodeDrawResultHandler.program l)

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

def sourceCfg (c : CodeAdminDraw.Config) : Config :=
  BitMachineInline.cfg Sum.inl (fun v => (v,none))
    (some (.inr (.inl .dispatch))) c

def resultCfg (c : CodeDrawResultHandler.Config) : Config :=
  BitMachineInline.cfg Sum.inr id none c

def start (s : State) (tape : List Bool) (B R : Nat) : Config :=
  sourceCfg (CodeAdminDraw.start s tape B R)

private theorem admin_read :
    Function.LeftInverse (Prod.fst : Control → CodeAdminDraw.Control)
      (fun v : CodeAdminDraw.Control => (v,(none : Option Bool))) := by
  intro v; rfl

private theorem handler_read : Function.LeftInverse (id : Control → Control) id := by
  intro v; rfl

private theorem admin_program (l : CodeAdminDraw.Label) :
    program (.inl l) =
      BitMachineInline.stmt Sum.inl (fun v => (v,none)) Prod.fst
        (some (.inr (.inl .dispatch))) (CodeAdminDraw.program l) := rfl

private theorem handler_program (l : CodeDrawResultHandler.Label) :
    program (.inr l) =
      BitMachineInline.stmt Sum.inr id id none
        (CodeDrawResultHandler.program l) := rfl

theorem source_to_handler (c d : CodeAdminDraw.Config) (t : Nat)
    (hr : CodeAdminDraw.run t c = d) (hd : d.l = none) :
    ∃ u ≤ t, run u (sourceCfg c) =
      resultCfg (CodeDrawResultHandler.start d) := by
  have hh : (((advance CodeAdminDraw.program)^[t]) c).l = none := by
    change (CodeAdminDraw.run t c).l = none
    rw [hr]
    exact hd
  obtain ⟨u,hu,hur⟩ := BitMachineInline.outputs Sum.inl
    (fun v => (v,none)) Prod.fst admin_read
    (some (.inr (.inl .dispatch))) CodeAdminDraw.program program
    admin_program c t hh
  refine ⟨u,hu,?_⟩
  change run u (sourceCfg c) =
    BitMachineInline.cfg Sum.inl (fun v => (v,none))
      (some (.inr (.inl .dispatch))) (CodeAdminDraw.run t c) at hur
  rw [hr] at hur
  simpa [sourceCfg,resultCfg,CodeDrawResultHandler.start,
    BitMachineInline.cfg,hd] using hur

theorem handler_to_end (c d : CodeDrawResultHandler.Config) (t : Nat)
    (hr : CodeDrawResultHandler.run t c = d) (hd : d.l = none) :
    ∃ u ≤ t, run u (resultCfg c) = resultCfg d := by
  have hh : (((advance CodeDrawResultHandler.program)^[t]) c).l = none := by
    change (CodeDrawResultHandler.run t c).l = none
    rw [hr]
    exact hd
  obtain ⟨u,hu,hur⟩ := BitMachineInline.outputs Sum.inr id id
    handler_read none CodeDrawResultHandler.program program
    handler_program c t hh
  refine ⟨u,hu,?_⟩
  change run u (resultCfg c) = resultCfg (CodeDrawResultHandler.run t c) at hur
  rw [hr] at hur
  exact hur

theorem source_then_handler (c d : CodeAdminDraw.Config)
    (e : CodeDrawResultHandler.Config) (t u : Nat)
    (ha : CodeAdminDraw.run t c = d) (hd : d.l = none)
    (hb : CodeDrawResultHandler.run u (CodeDrawResultHandler.start d) = e)
    (he : e.l = none) :
    ∃ v ≤ t+u, run v (sourceCfg c) = resultCfg e := by
  obtain ⟨ta,hta,hra⟩ := source_to_handler c d t ha hd
  obtain ⟨tb,htb,hrb⟩ := handler_to_end
    (CodeDrawResultHandler.start d) e u hb he
  refine ⟨tb+ta,by omega,?_⟩
  have hadd : run (tb+ta) (sourceCfg c) =
      run tb (run ta (sourceCfg c)) := by
    simp [run,Function.iterate_add_apply]
  rw [hadd,hra,hrb]

theorem compose_raw (s : State) (tape : List Bool) (B R : Nat)
    (d : CodeAdminDraw.Config) (e : CodeDrawResultHandler.Config)
    (ta tb : Nat)
    (ha : CodeAdminDraw.run ta (CodeAdminDraw.start s tape B R) = d)
    (hd : d.l = none)
    (hb : CodeDrawResultHandler.run tb (CodeDrawResultHandler.start d) = e)
    (he : e.l = none) :
    ∃ v ≤ ta+tb, run v (start s tape B R) = resultCfg e := by
  simpa [start] using source_then_handler
    (CodeAdminDraw.start s tape B R) d e ta tb ha hd hb he

theorem done_from_raw (root : Code) (s : State)
    (hp : PositiveState s) (ht : Trace root s)
    (h : (GeneratorCode.normalize s).todo = [])
    (tape : List Bool) (B R : Nat) :
    ∃ t ≤ 13*(codeSize root+3)^2+2,
      run t (start s tape B R) =
        resultCfg ⟨none,
          ((CodeAdminDraw.doneCfg (GeneratorCode.normalize s).output.reverse
            tape B R).var,none),
          (CodeAdminDraw.doneCfg (GeneratorCode.normalize s).output.reverse
            tape B R).stk⟩ := by
  let d := CodeAdminDraw.doneCfg (GeneratorCode.normalize s).output.reverse tape B R
  let e : CodeDrawResultHandler.Config := ⟨none,(d.var,none),d.stk⟩
  obtain ⟨ta,hta,ha⟩ := CodeAdminDraw.done_from_start root s hp ht h tape B R
  have hf : CodeDrawResultHandler.savedStatus d.var ≠ some true := by
    simp [d,CodeDrawResultHandler.savedStatus,CodeAdminDraw.doneCfg,
      CodeAdminDraw.drawControl,CodeHeaderDraw.drawInitialControl,
      LoadedTicketMachine.statusStartControl]
  have hb : CodeDrawResultHandler.run 1 (CodeDrawResultHandler.start d) = e := by
    exact CodeDrawResultHandler.dispatch_failure d.var d.stk hf
  obtain ⟨t,ht',hr⟩ := compose_raw s tape B R d e ta 1 ha rfl hb rfl
  exact ⟨t,by omega,hr⟩

theorem ticket_success_from_raw (root : Code) (s : State)
    (hp : PositiveState s) (ht : Trace root s)
    (n : Nat) (hn : 0 < n) (cs : List Code)
    (outputWord : List Bool)
    (hstate : GeneratorCode.normalize s =
      ⟨.ticket n :: cs,outputWord.reverse⟩)
    (B R N : Nat) (hB : Nat.clog 2 n ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (q : Fin n) (hq : CappedSampler.runWideBits n B R hB tape.1 = some q) :
    ∃ t F, t ≤ 13*(codeSize root+3)^2 + 1 +
        CodeAdminDraw.drawClock n B R + (n+2) ∧
      run t (start s (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R) =
        resultCfg (CodeDrawResultHandler.framed
          (CodeAdminDraw.drawResult n B R N hB tape .ticket
            (CodeAdminNormalization.todoWord cs) (List.replicate n true)
            [] [] outputWord F).var
          (CodeAdminDraw.drawResult n B R N hB tape .ticket
            (CodeAdminNormalization.todoWord cs) (List.replicate n true)
            [] [] outputWord F).stk
          (CodeDrawOutput.cfg none none []
            (((RecursiveLabelCodecScratch.finCodec n).encode q).reverse ++ outputWord))) := by
  let input := (RecursiveSamplingTape.writeTape B R (N+1) tape).val
  obtain ⟨ta,F,hta,ha⟩ := CodeAdminDraw.ticket_from_start
    root s hp ht n hn cs outputWord hstate B R N hB tape
  let d := CodeAdminDraw.drawResult n B R N hB tape .ticket
    (CodeAdminNormalization.todoWord cs) (List.replicate n true)
    [] [] outputWord F
  obtain ⟨tb,htb,hb⟩ := CodeDrawResultHandler.actual_ticket_success
    n B R N hB tape (CodeAdminNormalization.todoWord cs)
    (List.replicate n true) [] [] outputWord F q hq
  let e := CodeDrawResultHandler.framed d.var d.stk
    (CodeDrawOutput.cfg none none []
      (((RecursiveLabelCodecScratch.finCodec n).encode q).reverse ++ outputWord))
  have he : e.l = none := rfl
  obtain ⟨t,ht',hr⟩ := compose_raw s input B R d e ta tb ha rfl hb he
  refine ⟨t,F,?_,by simpa [input,d,e] using hr⟩
  simp only [CodeAdminDraw.drawClock] at ⊢
  omega

theorem bit_success_from_raw (root : Code) (s : State)
    (hp : PositiveState s) (ht : Trace root s)
    (cs : List Code) (outputWord : List Bool)
    (hstate : GeneratorCode.normalize s = ⟨.bit :: cs,outputWord.reverse⟩)
    (B R N : Nat) (hB : Nat.clog 2 2 ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (q : Fin 2) (hq : CappedSampler.runWideBits 2 B R hB tape.1 = some q) :
    ∃ t F, t ≤ 13*(codeSize root+3)^2 + 1 +
        CodeAdminDraw.drawClock 2 B R + 4 ∧
      run t (start s (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R) =
        resultCfg (CodeDrawResultHandler.framed
          (CodeAdminDraw.drawResult 2 B R N hB tape .bit
            (CodeAdminNormalization.todoWord cs) [] [] [] outputWord F).var
          (CodeAdminDraw.drawResult 2 B R N hB tape .bit
            (CodeAdminNormalization.todoWord cs) [] [] [] outputWord F).stk
          (CodeDrawOutput.cfg none none [] (decide (q.val=1)::outputWord))) := by
  let input := (RecursiveSamplingTape.writeTape B R (N+1) tape).val
  obtain ⟨ta,F,hta,ha⟩ := CodeAdminDraw.bit_from_start
    root s hp ht cs outputWord hstate B R N hB tape
  let d := CodeAdminDraw.drawResult 2 B R N hB tape .bit
    (CodeAdminNormalization.todoWord cs) [] [] [] outputWord F
  obtain ⟨tb,htb,hb⟩ := CodeDrawResultHandler.actual_bit_success
    B R N hB tape (CodeAdminNormalization.todoWord cs) outputWord F q hq
  let e := CodeDrawResultHandler.framed d.var d.stk
    (CodeDrawOutput.cfg none none [] (decide (q.val=1)::outputWord))
  have he : e.l = none := rfl
  obtain ⟨t,ht',hr⟩ := compose_raw s input B R d e ta tb ha rfl hb he
  refine ⟨t,F,?_,by simpa [input,d,e] using hr⟩
  simp only [CodeAdminDraw.drawClock] at ⊢
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
    ∃ t F, t ≤ 13*(codeSize root+3)^2 + 2 +
        CodeAdminDraw.drawClock (request (GeneratorCode.normalize s)) B R ∧
      let d := CodeAdminDraw.drawResult
        (request (GeneratorCode.normalize s)) B R N hB tape
        (CodeHeaderMachine.headerKind c)
        (CodeHeaderMachine.headerTail c (CodeAdminNormalization.todoWord cs))
        (CodeHeaderMachine.headerN c) (CodeHeaderMachine.headerA c)
        (CodeHeaderMachine.headerB c) outputWord F
      run t (start s (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R) =
        resultCfg ⟨none,(d.var,none),d.stk⟩ := by
  let input := (RecursiveSamplingTape.writeTape B R (N+1) tape).val
  obtain ⟨ta,F,hta,ha⟩ := CodeAdminDraw.draw_head_from_start
    root s hp ht c cs outputWord hstate hc B R N hB tape
  let d := CodeAdminDraw.drawResult
    (request (GeneratorCode.normalize s)) B R N hB tape
    (CodeHeaderMachine.headerKind c)
    (CodeHeaderMachine.headerTail c (CodeAdminNormalization.todoWord cs))
    (CodeHeaderMachine.headerN c) (CodeHeaderMachine.headerA c)
    (CodeHeaderMachine.headerB c) outputWord F
  let e : CodeDrawResultHandler.Config := ⟨none,(d.var,none),d.stk⟩
  have hb : CodeDrawResultHandler.run 1 (CodeDrawResultHandler.start d) = e := by
    exact CodeDrawResultHandler.actual_failure
      (request (GeneratorCode.normalize s)) B R N hB tape
      (CodeHeaderMachine.headerKind c)
      (CodeHeaderMachine.headerTail c (CodeAdminNormalization.todoWord cs))
      (CodeHeaderMachine.headerN c) (CodeHeaderMachine.headerA c)
      (CodeHeaderMachine.headerB c) outputWord F hq
  obtain ⟨t,ht',hr⟩ := compose_raw s input B R d e ta 1 ha rfl hb rfl
  exact ⟨t,F,by omega,by simpa [input,d,e] using hr⟩

theorem branch_dispatch (saved : CodeAdminDraw.Control)
    (S : Stack → List Bool)
    (hs : CodeDrawResultHandler.savedStatus saved = some true)
    (hk : CodeDrawResultHandler.savedKind saved = some .branch3) :
    CodeDrawResultHandler.run 1
      (CodeDrawResultHandler.start ⟨none,saved,S⟩) =
        (⟨none,(saved,none),S⟩ : CodeDrawResultHandler.Config) := by
  have hnt : ((some CodeHeaderMachine.Kind.branch3) ==
      (some CodeHeaderMachine.Kind.ticket)) = false := by decide
  have hnb : ((some CodeHeaderMachine.Kind.branch3) ==
      (some CodeHeaderMachine.Kind.bit)) = false := by decide
  simp [CodeDrawResultHandler.run, CodeDrawResultHandler.start,
    CodeDrawResultHandler.program, BitMachineEncoding.advance,
    TM2.step,TM2.stepAux,hs,hk,hnt,hnb]

theorem branch_success_from_raw (root : Code) (s : State)
    (hp : PositiveState s) (ht : Trace root s)
    (n a b : Nat) (hn : 0 < n) (first second third : Code)
    (cs : List Code) (outputWord : List Bool)
    (hstate : GeneratorCode.normalize s =
      ⟨.branch3 n a b first second third :: cs,outputWord.reverse⟩)
    (B R N : Nat) (hB : Nat.clog 2 n ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (q : Fin n) (hq : CappedSampler.runWideBits n B R hB tape.1 = some q) :
    ∃ t F, t ≤ 13*(codeSize root+3)^2 + 2 +
        CodeAdminDraw.drawClock n B R ∧
      let d := CodeAdminDraw.drawResult n B R N hB tape .branch3
        (encodeCode first ++ encodeCode second ++ encodeCode third ++
          CodeAdminNormalization.todoWord cs)
        (List.replicate n true) (List.replicate a true)
        (List.replicate b true) outputWord F
      run t (start s (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R) =
        resultCfg ⟨none,(d.var,none),d.stk⟩ := by
  let input := (RecursiveSamplingTape.writeTape B R (N+1) tape).val
  obtain ⟨ta,F,hta,ha⟩ := CodeAdminDraw.branch_from_start root s hp ht
    n a b hn first second third cs outputWord hstate B R N hB tape
  let d := CodeAdminDraw.drawResult n B R N hB tape .branch3
    (encodeCode first ++ encodeCode second ++ encodeCode third ++
      CodeAdminNormalization.todoWord cs)
    (List.replicate n true) (List.replicate a true)
    (List.replicate b true) outputWord F
  let e : CodeDrawResultHandler.Config := ⟨none,(d.var,none),d.stk⟩
  have hs : CodeDrawResultHandler.savedStatus d.var = some true := by
    simpa [d,hq] using
      (CodeDrawResultHandler.result_status n B R N hB tape .branch3
        (encodeCode first ++ encodeCode second ++ encodeCode third ++
          CodeAdminNormalization.todoWord cs)
        (List.replicate n true) (List.replicate a true)
        (List.replicate b true) outputWord F).1
  have hk : CodeDrawResultHandler.savedKind d.var = some .branch3 :=
    (CodeDrawResultHandler.result_status n B R N hB tape .branch3
      (encodeCode first ++ encodeCode second ++ encodeCode third ++
        CodeAdminNormalization.todoWord cs)
      (List.replicate n true) (List.replicate a true)
      (List.replicate b true) outputWord F).2
  have hb : CodeDrawResultHandler.run 1 (CodeDrawResultHandler.start d) = e :=
    branch_dispatch d.var d.stk hs hk
  obtain ⟨t,ht',hr⟩ := compose_raw s input B R d e ta 1 ha rfl hb rfl
  refine ⟨t,F,?_,by simpa [input,d,e] using hr⟩
  simp only [CodeAdminDraw.drawClock] at ⊢
  omega

#print axioms source_to_handler
#print axioms source_then_handler
#print axioms done_from_raw
#print axioms ticket_success_from_raw
#print axioms bit_success_from_raw
#print axioms failure_from_raw
#print axioms branch_success_from_raw

end
end Paper2.CodeAdminResultJoin
