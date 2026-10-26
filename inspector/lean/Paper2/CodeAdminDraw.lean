import Paper2.CodeAdminReady
import Paper2.CodeHeaderDraw
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding
import Mathlib.Tactic

/-! One fixed controller joining physical administrative normalization to a
physical capped draw. The route step copies only finite control; all data
remain in their actual stacks. -/

namespace Paper2.CodeAdminDraw

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open GeneratorCode GeneratorSerialization GeneratorPositive GeneratorStateSize

noncomputable section

abbrev Stack := CodeHeaderDraw.Stack
abbrev Control := CodeHeaderDraw.Control × CodeAdminMachine.Control
abbrev Label := CodeAdminMachine.Label ⊕ (Unit ⊕ CodeHeaderDraw.Label)
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def adminSlot : CodeAdminMachine.Stack ↪ Stack where
  toFun := Sum.inr
  inj' := Sum.inr_injective

def adminControl : CodeAdminMachine.Control := ((none,none),none)
def drawControl : CodeHeaderDraw.Control :=
  (CodeHeaderDraw.drawInitialControl,(none,none))

def foreign (tape : List Bool) (B R : Nat) : Stack → List Bool :=
  Sum.elim (DrawParameterLoader.initialBank tape 0 B R) (fun _ => [])

def adminLift (v : CodeAdminMachine.Control) : Control := (drawControl,v)
def adminRead (v : Control) : CodeAdminMachine.Control := v.2
def drawLift (v : CodeHeaderDraw.Control) : Control := (v,adminControl)
def drawRead (v : Control) : CodeHeaderDraw.Control := v.1

noncomputable def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l =>
      BitMachineStackEmbedding.stmt adminSlot Sum.inl adminLift adminRead
        (some (.inr (.inl ()))) (CodeAdminMachine.program l)
  | .inr (.inl ()) =>
      branch (fun v => v.2.1.2.isSome)
        (load (fun v => ((CodeHeaderDraw.drawInitialControl,v.2.1),adminControl))
          (goto (fun _ => .inr (.inr (.inr (.inr .route))))))
        halt
  | .inr (.inr l) =>
      BitMachineInline.stmt (fun x => .inr (.inr x)) drawLift drawRead
        none (CodeHeaderDraw.program l)

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

noncomputable def start (s : State) (tape : List Bool) (B R : Nat) : Config :=
  BitMachineStackEmbedding.cfg adminSlot (foreign tape B R) Sum.inl
    adminLift (some (.inr (.inl ()))) (CodeAdminNormalization.stateCfg s)

noncomputable def adminStop (s : State) (tape : List Bool) (B R : Nat) : Config :=
  BitMachineStackEmbedding.cfg adminSlot (foreign tape B R) Sum.inl
    adminLift (some (.inr (.inl ()))) (CodeAdminReady.stopped s)

def doneBank (outputWord tape : List Bool) (B R : Nat) : Stack → List Bool :=
  Sum.elim (DrawParameterLoader.initialBank tape 0 B R)
    (CodeScanner.bank (CodeHeaderMachine.contents [] [] [] [] [] [] []) outputWord)

def doneCfg (outputWord tape : List Bool) (B R : Nat) : Config :=
  ⟨none,(drawControl,adminControl),doneBank outputWord tape B R⟩

def drawResult (D B R N : Nat) (hB : Nat.clog 2 D ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (kind : CodeHeaderMachine.Kind)
    (tail n a b outputWord : List Bool)
    (F : DrawParameterLoader.LogCopyStack → List Bool) : Config :=
  BitMachineInline.cfg (fun l => .inr (.inr l)) drawLift none
    (CodeHeaderDraw.resultCfg D B R N hB tape kind tail n a b outputWord F)

theorem admin_lift_read : Function.LeftInverse adminRead adminLift := by intro v; rfl
theorem draw_lift_read : Function.LeftInverse drawRead drawLift := by intro v; rfl

private theorem admin_program (l : CodeAdminMachine.Label) :
    program (.inl l) =
      BitMachineStackEmbedding.stmt adminSlot Sum.inl adminLift adminRead
        (some (.inr (.inl ()))) (CodeAdminMachine.program l) := rfl

private theorem draw_program (l : CodeHeaderDraw.Label) :
    program (.inr (.inr l)) =
      BitMachineInline.stmt (fun x => .inr (.inr x)) drawLift drawRead none
        (CodeHeaderDraw.program l) := rfl

theorem admin_run (root : Code) (s : State) (hp : PositiveState s)
    (ht : Trace root s) (tape : List Bool) (B R : Nat) :
    ∃ t ≤ 13*(codeSize root+3)^2,
      run t (start s tape B R) =
        adminStop (GeneratorCode.normalize s) tape B R := by
  obtain ⟨u,hu,hr⟩ := CodeAdminReady.physical_ready_trace root s hp ht
  have hh : (((advance CodeAdminMachine.program)^[u])
      (CodeAdminNormalization.stateCfg s)).l = none := by
    rw [hr]; exact CodeAdminReady.stopped_halted _
  obtain ⟨t,ht',htr⟩ := BitMachineStackEmbedding.outputs adminSlot
    (foreign tape B R) Sum.inl adminLift adminRead admin_lift_read
    (some (.inr (.inl ()))) CodeAdminMachine.program program admin_program
    (CodeAdminNormalization.stateCfg s) u hh
  refine ⟨t,by omega,?_⟩
  simpa only [run,start,adminStop,hr] using htr

private theorem bank_right (S : CodeAdminMachine.Stack → List Bool)
    (tape : List Bool) (B R : Nat) :
    BitMachineStackEmbedding.bank adminSlot (foreign tape B R) S =
      Sum.elim (DrawParameterLoader.initialBank tape 0 B R) S := by
  funext j
  cases j with
  | inl j =>
      rw [BitMachineStackEmbedding.bank_outside]
      · rfl
      · intro h; obtain ⟨k,h⟩ := h; cases h
  | inr j => exact BitMachineStackEmbedding.bank_at adminSlot _ S j

theorem route_done (s : State) (tape : List Bool) (B R : Nat)
    (h : s.todo = []) :
    run 1 (adminStop s tape B R) = doneCfg s.output.reverse tape B R := by
  simp only [run, Function.iterate_one, adminStop, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    CodeAdminReady.stopped, h, CodeAdminMachine.cfg, adminLift, drawControl,
    program, BitMachineEncoding.advance, TM2.step, TM2.stepAux,
    Option.getD_some, Option.isSome_none, cond_false]
  congr 1
  exact bank_right _ tape B R

theorem route_draw (c : Code) (cs : List Code) (outputWord tape : List Bool)
    (B R : Nat) (kind : CodeHeaderMachine.Kind)
    (hk : CodeHeaderMachine.headerKind c = kind)
    (hw : CodeHeaderMachine.headerWord c = []) :
    run 1 (adminStop ⟨c::cs,outputWord.reverse⟩ tape B R) =
      BitMachineInline.cfg (fun l => .inr (.inr l)) drawLift none
        (CodeHeaderDraw.stagingCfg .route none kind tape B R
          (CodeHeaderMachine.headerTail c (CodeAdminNormalization.todoWord cs))
          (CodeHeaderMachine.headerN c) (CodeHeaderMachine.headerA c)
          (CodeHeaderMachine.headerB c) [] outputWord 0) := by
  simp only [run, Function.iterate_one, adminStop, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    CodeAdminReady.stopped, CodeAdminMachine.cfg, adminLift, drawLift,
    program, BitMachineEncoding.advance, TM2.step, TM2.stepAux,
    hk, hw]
  have hsome : (some kind).isSome = true := rfl
  simp only [hsome, cond_true]
  rw [bank_right]
  simp [CodeHeaderDraw.stagingCfg, CodeHeaderDraw.stagingBank,
    CodeScanner.bank, List.reverse_reverse, Option.getD_some]

theorem draw_run (c : CodeHeaderDraw.Config) (t : Nat)
    (hh : (CodeHeaderDraw.run t c).l = none) :
    ∃ u ≤ t,
      run u (BitMachineInline.cfg (fun l => .inr (.inr l)) drawLift none c) =
        BitMachineInline.cfg (fun l => .inr (.inr l)) drawLift none
          (CodeHeaderDraw.run t c) := by
  obtain ⟨u,hu,hur⟩ := BitMachineInline.outputs
    (fun l => .inr (.inr l)) drawLift drawRead draw_lift_read none
    CodeHeaderDraw.program program draw_program c t hh
  refine ⟨u,hu,?_⟩
  simpa only [run, CodeHeaderDraw.run] using hur

theorem route_then_draw (a : Config) (entry terminal : CodeHeaderDraw.Config)
    (q : Nat)
    (hroute : run 1 a =
      BitMachineInline.cfg (fun l => .inr (.inr l)) drawLift none entry)
    (hdraw : CodeHeaderDraw.run q entry = terminal)
    (hhalt : terminal.l = none) :
    ∃ t ≤ q+1, run t a =
      BitMachineInline.cfg (fun l => .inr (.inr l)) drawLift none terminal := by
  have hh : (CodeHeaderDraw.run q entry).l = none := by rw [hdraw]; exact hhalt
  obtain ⟨u,hu,hur⟩ := draw_run entry q hh
  refine ⟨u+1,by omega,?_⟩
  have hadd : run (u+1) a = run u (run 1 a) := by
    simp [run, Function.iterate_add_apply]
  rw [hadd, hroute, hur, hdraw]

theorem ticket_from_start (root : Code) (s : State)
    (hp : PositiveState s) (ht : Trace root s)
    (n : Nat) (hn : 0 < n) (cs : List Code)
    (outputWord : List Bool)
    (hstate : GeneratorCode.normalize s =
      ⟨.ticket n :: cs,outputWord.reverse⟩)
    (B R N : Nat) (hB : Nat.clog 2 n ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1)) :
    ∃ t : Nat, ∃ F : DrawParameterLoader.LogCopyStack → List Bool,
      t ≤ 13*(codeSize root+3)^2 + 1 +
        ((2*n+4) + LoadedTicketMachine.loaderBound n B R +
          LoadedTicketMachine.ticketBound n B R + 1) ∧
      run t (start s (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R) =
        drawResult n B R N hB tape .ticket
          (CodeAdminNormalization.todoWord cs) (List.replicate n true)
          [] [] outputWord F := by
  let input := (RecursiveSamplingTape.writeTape B R (N+1) tape).val
  obtain ⟨ta,hta,hra⟩ := admin_run root s hp ht input B R
  obtain ⟨td,F,htd,hrd⟩ := CodeHeaderDraw.prepared_ticket
    n B R N hn hB tape (CodeAdminNormalization.todoWord cs) [] [] outputWord
  have hroute : run 1 (adminStop (GeneratorCode.normalize s) input B R) =
      BitMachineInline.cfg (fun l => .inr (.inr l)) drawLift none
        (CodeHeaderDraw.stagingCfg .route none .ticket input B R
          (CodeAdminNormalization.todoWord cs) (List.replicate n true)
          [] [] [] outputWord 0) := by
    rw [hstate]
    simpa [CodeHeaderMachine.headerTail, CodeHeaderMachine.headerN,
      CodeHeaderMachine.headerA, CodeHeaderMachine.headerB,
      CodeHeaderMachine.headerKind, CodeHeaderMachine.headerWord]
      using route_draw (.ticket n) cs outputWord input B R .ticket rfl rfl
  have hhalt : (CodeHeaderDraw.resultCfg n B R N hB tape .ticket
      (CodeAdminNormalization.todoWord cs) (List.replicate n true)
      [] [] outputWord F).l = none := rfl
  obtain ⟨tb,htb,hrb⟩ := route_then_draw
    (adminStop (GeneratorCode.normalize s) input B R)
    (CodeHeaderDraw.stagingCfg .route none .ticket input B R
      (CodeAdminNormalization.todoWord cs) (List.replicate n true)
      [] [] [] outputWord 0)
    (CodeHeaderDraw.resultCfg n B R N hB tape .ticket
      (CodeAdminNormalization.todoWord cs) (List.replicate n true)
      [] [] outputWord F) td hroute hrd hhalt
  refine ⟨tb+ta,F,by omega,?_⟩
  have hadd : run (tb+ta) (start s input B R) =
      run tb (run ta (start s input B R)) := by
    simp [run, Function.iterate_add_apply]
  rw [hadd, hra, hrb]
  rfl

theorem done_from_start (root : Code) (s : State)
    (hp : PositiveState s) (ht : Trace root s)
    (h : (GeneratorCode.normalize s).todo = [])
    (tape : List Bool) (B R : Nat) :
    ∃ t ≤ 13*(codeSize root+3)^2+1,
      run t (start s tape B R) =
        doneCfg (GeneratorCode.normalize s).output.reverse tape B R := by
  obtain ⟨ta,hta,hra⟩ := admin_run root s hp ht tape B R
  refine ⟨1+ta,by omega,?_⟩
  have hadd : run (1+ta) (start s tape B R) =
      run 1 (run ta (start s tape B R)) := by
    simp [run, Function.iterate_add_apply]
  rw [hadd,hra,route_done _ _ _ _ h]

theorem bit_from_start (root : Code) (s : State)
    (hp : PositiveState s) (ht : Trace root s)
    (cs : List Code) (outputWord : List Bool)
    (hstate : GeneratorCode.normalize s = ⟨.bit :: cs,outputWord.reverse⟩)
    (B R N : Nat) (hB : Nat.clog 2 2 ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1)) :
    ∃ t : Nat, ∃ F : DrawParameterLoader.LogCopyStack → List Bool,
      t ≤ 13*(codeSize root+3)^2 + 1 +
        (4 + LoadedTicketMachine.loaderBound 2 B R +
          LoadedTicketMachine.ticketBound 2 B R + 1) ∧
      run t (start s (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R) =
        drawResult 2 B R N hB tape .bit
          (CodeAdminNormalization.todoWord cs) [] [] [] outputWord F := by
  let input := (RecursiveSamplingTape.writeTape B R (N+1) tape).val
  obtain ⟨ta,hta,hra⟩ := admin_run root s hp ht input B R
  obtain ⟨td,F,htd,hrd⟩ := CodeHeaderDraw.prepared_bit
    B R N hB tape (CodeAdminNormalization.todoWord cs) outputWord
  have hroute : run 1 (adminStop (GeneratorCode.normalize s) input B R) =
      BitMachineInline.cfg (fun l => .inr (.inr l)) drawLift none
        (CodeHeaderDraw.stagingCfg .route none .bit input B R
          (CodeAdminNormalization.todoWord cs) [] [] [] [] outputWord 0) := by
    rw [hstate]
    simpa [CodeHeaderMachine.headerTail, CodeHeaderMachine.headerN,
      CodeHeaderMachine.headerA, CodeHeaderMachine.headerB,
      CodeHeaderMachine.headerKind, CodeHeaderMachine.headerWord]
      using route_draw .bit cs outputWord input B R .bit rfl rfl
  have hhalt : (CodeHeaderDraw.resultCfg 2 B R N hB tape .bit
      (CodeAdminNormalization.todoWord cs) [] [] [] outputWord F).l = none := rfl
  obtain ⟨tb,htb,hrb⟩ := route_then_draw
    (adminStop (GeneratorCode.normalize s) input B R)
    (CodeHeaderDraw.stagingCfg .route none .bit input B R
      (CodeAdminNormalization.todoWord cs) [] [] [] [] outputWord 0)
    (CodeHeaderDraw.resultCfg 2 B R N hB tape .bit
      (CodeAdminNormalization.todoWord cs) [] [] [] outputWord F)
    td hroute hrd hhalt
  refine ⟨tb+ta,F,by omega,?_⟩
  have hadd : run (tb+ta) (start s input B R) =
      run tb (run ta (start s input B R)) := by
    simp [run, Function.iterate_add_apply]
  rw [hadd,hra,hrb]
  rfl

theorem branch_from_start (root : Code) (s : State)
    (hp : PositiveState s) (ht : Trace root s)
    (n a b : Nat) (hn : 0 < n) (first second third : Code)
    (cs : List Code) (outputWord : List Bool)
    (hstate : GeneratorCode.normalize s =
      ⟨.branch3 n a b first second third :: cs,outputWord.reverse⟩)
    (B R N : Nat) (hB : Nat.clog 2 n ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1)) :
    ∃ t : Nat, ∃ F : DrawParameterLoader.LogCopyStack → List Bool,
      t ≤ 13*(codeSize root+3)^2 + 1 +
        ((2*n+4) + LoadedTicketMachine.loaderBound n B R +
          LoadedTicketMachine.ticketBound n B R + 1) ∧
      run t (start s (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R) =
        drawResult n B R N hB tape .branch3
          (encodeCode first ++ encodeCode second ++ encodeCode third ++
            CodeAdminNormalization.todoWord cs)
          (List.replicate n true) (List.replicate a true)
          (List.replicate b true) outputWord F := by
  let input := (RecursiveSamplingTape.writeTape B R (N+1) tape).val
  let tail := encodeCode first ++ encodeCode second ++ encodeCode third ++
    CodeAdminNormalization.todoWord cs
  obtain ⟨ta,hta,hra⟩ := admin_run root s hp ht input B R
  obtain ⟨td,F,htd,hrd⟩ := CodeHeaderDraw.prepared_branch
    n B R N hn hB tape tail (List.replicate a true)
      (List.replicate b true) outputWord
  have hroute : run 1 (adminStop (GeneratorCode.normalize s) input B R) =
      BitMachineInline.cfg (fun l => .inr (.inr l)) drawLift none
        (CodeHeaderDraw.stagingCfg .route none .branch3 input B R
          tail (List.replicate n true) (List.replicate a true)
          (List.replicate b true) [] outputWord 0) := by
    rw [hstate]
    simpa [tail, CodeHeaderMachine.headerTail, CodeHeaderMachine.headerN,
      CodeHeaderMachine.headerA, CodeHeaderMachine.headerB,
      CodeHeaderMachine.headerKind, CodeHeaderMachine.headerWord,
      List.append_assoc]
      using route_draw (.branch3 n a b first second third) cs
        outputWord input B R .branch3 rfl rfl
  have hhalt : (CodeHeaderDraw.resultCfg n B R N hB tape .branch3
      tail (List.replicate n true) (List.replicate a true)
      (List.replicate b true) outputWord F).l = none := rfl
  obtain ⟨tb,htb,hrb⟩ := route_then_draw
    (adminStop (GeneratorCode.normalize s) input B R)
    (CodeHeaderDraw.stagingCfg .route none .branch3 input B R
      tail (List.replicate n true) (List.replicate a true)
      (List.replicate b true) [] outputWord 0)
    (CodeHeaderDraw.resultCfg n B R N hB tape .branch3
      tail (List.replicate n true) (List.replicate a true)
      (List.replicate b true) outputWord F)
    td hroute hrd hhalt
  refine ⟨tb+ta,F,by omega,?_⟩
  have hadd : run (tb+ta) (start s input B R) =
      run tb (run ta (start s input B R)) := by
    simp [run, Function.iterate_add_apply]
  rw [hadd,hra,hrb]
  rfl

def drawClock (D B R : Nat) : Nat :=
  (2*D+4) + LoadedTicketMachine.loaderBound D B R +
    LoadedTicketMachine.ticketBound D B R + 1

/-- Unified positive-head endpoint. The normalized constructor is a proof
index, never a machine input; the physical dispatcher reads its saved tag. -/
theorem draw_head_from_start (root : Code) (s : State)
    (hp : PositiveState s) (ht : Trace root s)
    (c : Code) (cs : List Code) (outputWord : List Bool)
    (hstate : GeneratorCode.normalize s = ⟨c::cs,outputWord.reverse⟩)
    (hc : DrawHead c)
    (B R N : Nat)
    (hB : Nat.clog 2 (request (GeneratorCode.normalize s)) ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1)) :
    ∃ t : Nat, ∃ F : DrawParameterLoader.LogCopyStack → List Bool,
      t ≤ 13*(codeSize root+3)^2 + 1 +
        drawClock (request (GeneratorCode.normalize s)) B R ∧
      run t (start s (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R) =
        drawResult (request (GeneratorCode.normalize s)) B R N hB tape
          (CodeHeaderMachine.headerKind c)
          (CodeHeaderMachine.headerTail c (CodeAdminNormalization.todoWord cs))
          (CodeHeaderMachine.headerN c) (CodeHeaderMachine.headerA c)
          (CodeHeaderMachine.headerB c) outputWord F := by
  cases c with
  | emit bits => simp [DrawHead] at hc
  | append left right => simp [DrawHead] at hc
  | ticket n =>
      cases n with
      | zero => simp [DrawHead] at hc
      | succ k =>
          have hB' : Nat.clog 2 (k+1) ≤ B := by
            simpa [hstate, request] using hB
          obtain ⟨t,F,ht',hr⟩ := ticket_from_start root s hp ht
            (k+1) (by omega) cs outputWord hstate B R N hB' tape
          refine ⟨t,F,?_,?_⟩
          · simpa [drawClock, hstate, request] using ht'
          · simpa [hstate, request, CodeHeaderMachine.headerKind,
              CodeHeaderMachine.headerTail, CodeHeaderMachine.headerN,
              CodeHeaderMachine.headerA, CodeHeaderMachine.headerB] using hr
  | bit =>
      have hB' : Nat.clog 2 2 ≤ B := by
        simpa [hstate, request] using hB
      obtain ⟨t,F,ht',hr⟩ := bit_from_start root s hp ht
        cs outputWord hstate B R N hB' tape
      refine ⟨t,F,?_,?_⟩
      · have hd : request (GeneratorCode.normalize s) = 2 := by
          simp [hstate, request]
        simp only [hd, drawClock]
        omega
      · simpa [hstate, request, CodeHeaderMachine.headerKind,
          CodeHeaderMachine.headerTail, CodeHeaderMachine.headerN,
          CodeHeaderMachine.headerA, CodeHeaderMachine.headerB] using hr
  | branch3 n a b first second third =>
      cases n with
      | zero => simp [DrawHead] at hc
      | succ k =>
          have hB' : Nat.clog 2 (k+1) ≤ B := by
            simpa [hstate, request] using hB
          obtain ⟨t,F,ht',hr⟩ := branch_from_start root s hp ht
            (k+1) a b (by omega) first second third cs outputWord
            hstate B R N hB' tape
          refine ⟨t,F,?_,?_⟩
          · simpa [drawClock, hstate, request] using ht'
          · simpa [hstate, request, CodeHeaderMachine.headerKind,
              CodeHeaderMachine.headerTail, CodeHeaderMachine.headerN,
              CodeHeaderMachine.headerA, CodeHeaderMachine.headerB,
              List.append_assoc] using hr

/-- One actual finite-control run either stops on normalized empty todo, or
performs precisely one positive draw from its physically extracted header. -/
theorem done_or_draw_from_start (root : Code) (s : State)
    (hp : PositiveState s) (ht : Trace root s)
    (B R N : Nat)
    (hB : Nat.clog 2 (request (GeneratorCode.normalize s)) ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1)) :
    ∃ t ≤ 13*(codeSize root+3)^2 + 1 +
        drawClock (request (GeneratorCode.normalize s)) B R,
      ((GeneratorCode.normalize s).todo = [] ∧
        run t (start s (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R) =
          doneCfg (GeneratorCode.normalize s).output.reverse
            (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R) ∨
      (∃ c cs F,
        (GeneratorCode.normalize s).todo = c :: cs ∧ DrawHead c ∧
        run t (start s (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R) =
          drawResult (request (GeneratorCode.normalize s)) B R N hB tape
            (CodeHeaderMachine.headerKind c)
            (CodeHeaderMachine.headerTail c (CodeAdminNormalization.todoWord cs))
            (CodeHeaderMachine.headerN c) (CodeHeaderMachine.headerA c)
            (CodeHeaderMachine.headerB c)
            (GeneratorCode.normalize s).output.reverse F) := by
  let z := GeneratorCode.normalize s
  by_cases hnil : z.todo = []
  · obtain ⟨t,ht',hr⟩ := done_from_start root s hp ht hnil
      (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R
    exact ⟨t,by omega,Or.inl ⟨hnil,hr⟩⟩
  · have hz := GeneratorPositive.normalize_positive s hp
    have hready := GeneratorCode.normalize_ready s
    obtain ⟨c,cs,hcs,hc⟩ := ready_positive_draw z hz hready hnil
    have hstate : z = ⟨c::cs,z.output.reverse.reverse⟩ := by
      cases hs : z with
      | mk todo out =>
          have htod : todo = c :: cs := by simpa [hs] using hcs
          cases htod
          simp
    obtain ⟨t,F,ht',hr⟩ := draw_head_from_start root s hp ht
      c cs z.output.reverse (by simpa [z] using hstate) hc
      B R N hB tape
    exact ⟨t,ht',Or.inr ⟨c,cs,F,hcs,hc,by simpa using hr⟩⟩

theorem bounded_done_or_draw_from_start {M : Nat} (root : Code)
    (s : BoundedState M)
    (hp : PositiveState s.val) (ht : Trace root s.val)
    (B R N : Nat) (hMB : Nat.clog 2 M ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1)) :
    ∃ t ≤ 13*(codeSize root+3)^2 + 1 +
        drawClock (den s) B R,
      ((GeneratorCode.normalize s.val).todo = [] ∧
        run t (start s.val (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R) =
          doneCfg (GeneratorCode.normalize s.val).output.reverse
            (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R) ∨
      (∃ c cs F,
        (GeneratorCode.normalize s.val).todo = c :: cs ∧ DrawHead c ∧
        run t (start s.val (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R) =
          drawResult (den s) B R N
            (den_width hMB s) tape
            (CodeHeaderMachine.headerKind c)
            (CodeHeaderMachine.headerTail c (CodeAdminNormalization.todoWord cs))
            (CodeHeaderMachine.headerN c) (CodeHeaderMachine.headerA c)
            (CodeHeaderMachine.headerB c)
            (GeneratorCode.normalize s.val).output.reverse F) := by
  simpa only [den] using
    done_or_draw_from_start root s.val hp ht B R N
      (den_width hMB s) tape

#print axioms admin_run
#print axioms route_done
#print axioms route_draw
#print axioms ticket_from_start
#print axioms bit_from_start
#print axioms branch_from_start
#print axioms done_from_start
#print axioms draw_head_from_start
#print axioms done_or_draw_from_start
#print axioms bounded_done_or_draw_from_start

end
end Paper2.CodeAdminDraw
