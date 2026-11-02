import Paper2.CodeAdminResultJoin
import Paper2.CodeBranchAdapter
import Mathlib.Tactic

/-! A fixed finite-control arm routing an actual successful branch result to
the frozen charged child selector. -/

namespace Paper2.CodeAdminBranchJoin

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open GeneratorCode GeneratorSerialization GeneratorPositive GeneratorStateSize

noncomputable section

abbrev Stack := CodeAdminResultJoin.Stack
abbrev Control := CodeAdminResultJoin.Control × CodeBranchAdapter.Control
abbrev Label := CodeAdminResultJoin.Label ⊕
  (Unit ⊕ (CodeAdminResultJoin.Control × CodeBranchAdapter.Label))
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def selectorStart : BranchSelection.Control :=
  ((.first,none),ChildSelect.idle .first)

def branchControl (base : CodeBranchAdapter.BaseControl) :
    CodeBranchAdapter.Control := (selectorStart,(base,none))

def joinLift (v : CodeAdminResultJoin.Control) : Control :=
  (v,branchControl (CodeHeaderDraw.drawInitialControl,(none,none)))

def joinRead (v : Control) : CodeAdminResultJoin.Control := v.1

def branchLift (saved : CodeAdminResultJoin.Control)
    (v : CodeBranchAdapter.Control) : Control := (saved,v)

def branchRead (v : Control) : CodeBranchAdapter.Control := v.2

noncomputable def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l =>
      BitMachineInline.stmt Sum.inl joinLift joinRead
        (some (.inr (.inl ()))) (CodeAdminResultJoin.program l)
  | .inr (.inl ()) =>
      branch (fun v =>
        CodeDrawResultHandler.savedStatus v.1.1 == some true &&
        CodeDrawResultHandler.savedKind v.1.1 == some .branch3)
        (load (fun v => (v.1,branchControl v.1.1.1))
          (goto (fun v => .inr (.inr (v.1,.inr .route)))))
        halt
  | .inr (.inr (saved,l)) =>
      BitMachineInline.stmt (fun x => .inr (.inr (saved,x)))
        (branchLift saved) branchRead none (CodeBranchAdapter.program l)

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

def joinCfg (c : CodeAdminResultJoin.Config) : Config :=
  BitMachineInline.cfg Sum.inl joinLift (some (.inr (.inl ()))) c

def branchCfg (saved : CodeAdminResultJoin.Control)
    (c : CodeBranchAdapter.Config) : Config :=
  BitMachineInline.cfg (fun x => .inr (.inr (saved,x)))
    (branchLift saved) none c

def start (s : State) (tape : List Bool) (B R : Nat) : Config :=
  joinCfg (CodeAdminResultJoin.start s tape B R)

private theorem join_read : Function.LeftInverse joinRead joinLift := by
  intro v; rfl

private theorem branch_read (saved : CodeAdminResultJoin.Control) :
    Function.LeftInverse branchRead (branchLift saved) := by
  intro v; rfl

private theorem join_program (l : CodeAdminResultJoin.Label) :
    program (.inl l) = BitMachineInline.stmt Sum.inl joinLift joinRead
      (some (.inr (.inl ()))) (CodeAdminResultJoin.program l) := rfl

private theorem branch_program (saved : CodeAdminResultJoin.Control)
    (l : CodeBranchAdapter.Label) :
    program (.inr (.inr (saved,l))) =
      BitMachineInline.stmt (fun x => .inr (.inr (saved,x)))
        (branchLift saved) branchRead none (CodeBranchAdapter.program l) := rfl

theorem join_to_route (c d : CodeAdminResultJoin.Config) (t : Nat)
    (hr : CodeAdminResultJoin.run t c = d) (hd : d.l = none) :
    ∃ u ≤ t, run u (joinCfg c) =
      ⟨some (.inr (.inl ())),joinLift d.var,d.stk⟩ := by
  have hh : (((advance CodeAdminResultJoin.program)^[t]) c).l = none := by
    change (CodeAdminResultJoin.run t c).l = none
    rw [hr]; exact hd
  obtain ⟨u,hu,hur⟩ := BitMachineInline.outputs Sum.inl
    joinLift joinRead join_read (some (.inr (.inl ())))
    CodeAdminResultJoin.program program join_program c t hh
  refine ⟨u,hu,?_⟩
  change run u (joinCfg c) =
    BitMachineInline.cfg Sum.inl joinLift (some (.inr (.inl ())))
      (CodeAdminResultJoin.run t c) at hur
  rw [hr] at hur
  simpa [BitMachineInline.cfg,hd] using hur

theorem branch_to_end (saved : CodeAdminResultJoin.Control)
    (c d : CodeBranchAdapter.Config) (t : Nat)
    (hr : CodeBranchAdapter.run t c = d) (hd : d.l = none) :
    ∃ u ≤ t, run u (branchCfg saved c) = branchCfg saved d := by
  have hh : (((advance CodeBranchAdapter.program)^[t]) c).l = none := by
    change (CodeBranchAdapter.run t c).l = none
    rw [hr]; exact hd
  obtain ⟨u,hu,hur⟩ := BitMachineInline.outputs
    (fun x => .inr (.inr (saved,x))) (branchLift saved) branchRead
    (branch_read saved) none CodeBranchAdapter.program program
    (branch_program saved) c t hh
  refine ⟨u,hu,?_⟩
  change run u (branchCfg saved c) =
    branchCfg saved (CodeBranchAdapter.run t c) at hur
  rw [hr] at hur
  exact hur

theorem route_branch (saved : CodeAdminResultJoin.Control)
    (S : Stack → List Bool)
    (hs : CodeDrawResultHandler.savedStatus saved.1 = some true)
    (hk : CodeDrawResultHandler.savedKind saved.1 = some .branch3) :
    run 1 ⟨some (.inr (.inl ())),joinLift saved,S⟩ =
      branchCfg saved
        ⟨some (.inr .route),branchControl saved.1.1,S⟩ := by
  simp [run,program,BitMachineEncoding.advance,TM2.step,TM2.stepAux,
    joinLift,branchCfg,branchControl,branchLift,BitMachineInline.cfg,hs,hk]

theorem route_nonbranch (saved : CodeAdminResultJoin.Control)
    (S : Stack → List Bool)
    (hno : ¬ (CodeDrawResultHandler.savedStatus saved.1 = some true ∧
      CodeDrawResultHandler.savedKind saved.1 = some .branch3)) :
    run 1 ⟨some (.inr (.inl ())),joinLift saved,S⟩ =
      ⟨none,joinLift saved,S⟩ := by
  have hf : (CodeDrawResultHandler.savedStatus saved.1 == some true &&
      CodeDrawResultHandler.savedKind saved.1 == some .branch3) = false := by
    simp [beq_iff_eq]
    tauto
  simp [run,program,BitMachineEncoding.advance,TM2.step,TM2.stepAux,
    joinLift,hf]

theorem nonbranch_from_raw (s : State) (tape : List Bool) (B R : Nat)
    (j : CodeAdminResultJoin.Config) (ta : Nat)
    (ha : CodeAdminResultJoin.run ta
      (CodeAdminResultJoin.start s tape B R) = j)
    (hj : j.l = none)
    (hno : ¬ (CodeDrawResultHandler.savedStatus j.var.1 = some true ∧
      CodeDrawResultHandler.savedKind j.var.1 = some .branch3)) :
    ∃ t ≤ ta+1,
      run t (start s tape B R) = ⟨none,joinLift j.var,j.stk⟩ := by
  obtain ⟨u,hu,hur⟩ := join_to_route
    (CodeAdminResultJoin.start s tape B R) j ta ha hj
  refine ⟨1+u,by omega,?_⟩
  have hadd : run (1+u) (start s tape B R) =
      run 1 (run u (joinCfg (CodeAdminResultJoin.start s tape B R))) := by
    simp [start,run,Function.iterate_add_apply]
  rw [hadd,hur,route_nonbranch j.var j.stk hno]

theorem done_from_raw (root : Code) (s : State)
    (hp : PositiveState s) (ht : Trace root s)
    (h : (GeneratorCode.normalize s).todo = [])
    (tape : List Bool) (B R : Nat) :
    ∃ t ≤ 13*(codeSize root+3)^2+3,
      let d := CodeAdminDraw.doneCfg
        (GeneratorCode.normalize s).output.reverse tape B R
      let j : CodeAdminResultJoin.Config :=
        CodeAdminResultJoin.resultCfg ⟨none,(d.var,none),d.stk⟩
      run t (start s tape B R) = ⟨none,joinLift j.var,j.stk⟩ := by
  obtain ⟨ta,hta,ha⟩ := CodeAdminResultJoin.done_from_raw
    root s hp ht h tape B R
  let d := CodeAdminDraw.doneCfg
    (GeneratorCode.normalize s).output.reverse tape B R
  let j : CodeAdminResultJoin.Config :=
    CodeAdminResultJoin.resultCfg ⟨none,(d.var,none),d.stk⟩
  have hno : ¬ (CodeDrawResultHandler.savedStatus j.var.1 = some true ∧
      CodeDrawResultHandler.savedKind j.var.1 = some .branch3) := by
    simp [j,d,CodeAdminResultJoin.resultCfg,BitMachineInline.cfg,
      CodeDrawResultHandler.savedStatus,CodeAdminDraw.doneCfg,
      CodeAdminDraw.drawControl,CodeHeaderDraw.drawInitialControl,
      LoadedTicketMachine.statusStartControl]
  obtain ⟨t,ht',hr⟩ := nonbranch_from_raw s tape B R j ta ha rfl hno
  exact ⟨t,by omega,by simpa [d,j] using hr⟩

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
    ∃ t F, t ≤ 13*(codeSize root+3)^2 + 3 +
        CodeAdminDraw.drawClock (request (GeneratorCode.normalize s)) B R ∧
      let d := CodeAdminDraw.drawResult
        (request (GeneratorCode.normalize s)) B R N hB tape
        (CodeHeaderMachine.headerKind c)
        (CodeHeaderMachine.headerTail c (CodeAdminNormalization.todoWord cs))
        (CodeHeaderMachine.headerN c) (CodeHeaderMachine.headerA c)
        (CodeHeaderMachine.headerB c) outputWord F
      let j : CodeAdminResultJoin.Config :=
        CodeAdminResultJoin.resultCfg ⟨none,(d.var,none),d.stk⟩
      run t (start s (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R) =
        ⟨none,joinLift j.var,j.stk⟩ := by
  let input := (RecursiveSamplingTape.writeTape B R (N+1) tape).val
  obtain ⟨ta,F,hta,ha⟩ := CodeAdminResultJoin.failure_from_raw
    root s hp ht c cs outputWord hstate hc B R N hB tape hq
  let d := CodeAdminDraw.drawResult
    (request (GeneratorCode.normalize s)) B R N hB tape
    (CodeHeaderMachine.headerKind c)
    (CodeHeaderMachine.headerTail c (CodeAdminNormalization.todoWord cs))
    (CodeHeaderMachine.headerN c) (CodeHeaderMachine.headerA c)
    (CodeHeaderMachine.headerB c) outputWord F
  let j : CodeAdminResultJoin.Config :=
    CodeAdminResultJoin.resultCfg ⟨none,(d.var,none),d.stk⟩
  have hno : ¬ (CodeDrawResultHandler.savedStatus j.var.1 = some true ∧
      CodeDrawResultHandler.savedKind j.var.1 = some .branch3) := by
    have hf : CodeDrawResultHandler.savedStatus d.var = some false := by
      simpa [d,hq] using
        (CodeDrawResultHandler.result_status
          (request (GeneratorCode.normalize s)) B R N hB tape
          (CodeHeaderMachine.headerKind c)
          (CodeHeaderMachine.headerTail c (CodeAdminNormalization.todoWord cs))
          (CodeHeaderMachine.headerN c) (CodeHeaderMachine.headerA c)
          (CodeHeaderMachine.headerB c) outputWord F).1
    simp [j,CodeAdminResultJoin.resultCfg,BitMachineInline.cfg,hf]
  obtain ⟨t,ht',hr⟩ := nonbranch_from_raw s input B R j ta ha rfl hno
  exact ⟨t,F,by omega,by simpa [input,d,j] using hr⟩

theorem ticket_success_from_raw (root : Code) (s : State)
    (hp : PositiveState s) (ht : Trace root s)
    (D : Nat) (hD : 0 < D) (cs : List Code)
    (outputWord : List Bool)
    (hstate : GeneratorCode.normalize s =
      ⟨.ticket D :: cs,outputWord.reverse⟩)
    (B R N : Nat) (hB : Nat.clog 2 D ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (q : Fin D) (hq : CappedSampler.runWideBits D B R hB tape.1 = some q) :
    ∃ t F, t ≤ 13*(codeSize root+3)^2 + 2 +
        CodeAdminDraw.drawClock D B R + (D+2) ∧
      let d := CodeAdminDraw.drawResult D B R N hB tape .ticket
        (CodeAdminNormalization.todoWord cs) (List.replicate D true)
        [] [] outputWord F
      let e := CodeDrawResultHandler.framed d.var d.stk
        (CodeDrawOutput.cfg none none []
          (((RecursiveLabelCodecScratch.finCodec D).encode q).reverse ++ outputWord))
      let j := CodeAdminResultJoin.resultCfg e
      run t (start s (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R) =
        ⟨none,joinLift j.var,j.stk⟩ := by
  let input := (RecursiveSamplingTape.writeTape B R (N+1) tape).val
  obtain ⟨ta,F,hta,ha⟩ := CodeAdminResultJoin.ticket_success_from_raw
    root s hp ht D hD cs outputWord hstate B R N hB tape q hq
  let d := CodeAdminDraw.drawResult D B R N hB tape .ticket
    (CodeAdminNormalization.todoWord cs) (List.replicate D true)
    [] [] outputWord F
  let e := CodeDrawResultHandler.framed d.var d.stk
    (CodeDrawOutput.cfg none none []
      (((RecursiveLabelCodecScratch.finCodec D).encode q).reverse ++ outputWord))
  let j := CodeAdminResultJoin.resultCfg e
  have hno : ¬ (CodeDrawResultHandler.savedStatus j.var.1 = some true ∧
      CodeDrawResultHandler.savedKind j.var.1 = some .branch3) := by
    have hk : CodeDrawResultHandler.savedKind d.var = some .ticket :=
      (CodeDrawResultHandler.result_status D B R N hB tape .ticket
        (CodeAdminNormalization.todoWord cs) (List.replicate D true)
        [] [] outputWord F).2
    simp [j,e,CodeAdminResultJoin.resultCfg,BitMachineInline.cfg,
      CodeDrawResultHandler.framed,BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg,hk]
  obtain ⟨t,ht',hr⟩ := nonbranch_from_raw s input B R j ta ha rfl hno
  exact ⟨t,F,by omega,by simpa [input,d,e,j] using hr⟩

theorem bit_success_from_raw (root : Code) (s : State)
    (hp : PositiveState s) (ht : Trace root s)
    (cs : List Code) (outputWord : List Bool)
    (hstate : GeneratorCode.normalize s = ⟨.bit :: cs,outputWord.reverse⟩)
    (B R N : Nat) (hB : Nat.clog 2 2 ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (q : Fin 2) (hq : CappedSampler.runWideBits 2 B R hB tape.1 = some q) :
    ∃ t F, t ≤ 13*(codeSize root+3)^2 + 2 +
        CodeAdminDraw.drawClock 2 B R + 4 ∧
      let d := CodeAdminDraw.drawResult 2 B R N hB tape .bit
        (CodeAdminNormalization.todoWord cs) [] [] [] outputWord F
      let e := CodeDrawResultHandler.framed d.var d.stk
        (CodeDrawOutput.cfg none none [] (decide (q.val=1)::outputWord))
      let j := CodeAdminResultJoin.resultCfg e
      run t (start s (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R) =
        ⟨none,joinLift j.var,j.stk⟩ := by
  let input := (RecursiveSamplingTape.writeTape B R (N+1) tape).val
  obtain ⟨ta,F,hta,ha⟩ := CodeAdminResultJoin.bit_success_from_raw
    root s hp ht cs outputWord hstate B R N hB tape q hq
  let d := CodeAdminDraw.drawResult 2 B R N hB tape .bit
    (CodeAdminNormalization.todoWord cs) [] [] [] outputWord F
  let e := CodeDrawResultHandler.framed d.var d.stk
    (CodeDrawOutput.cfg none none [] (decide (q.val=1)::outputWord))
  let j := CodeAdminResultJoin.resultCfg e
  have hno : ¬ (CodeDrawResultHandler.savedStatus j.var.1 = some true ∧
      CodeDrawResultHandler.savedKind j.var.1 = some .branch3) := by
    have hk : CodeDrawResultHandler.savedKind d.var = some .bit :=
      (CodeDrawResultHandler.result_status 2 B R N hB tape .bit
        (CodeAdminNormalization.todoWord cs) [] [] [] outputWord F).2
    simp [j,e,CodeAdminResultJoin.resultCfg,BitMachineInline.cfg,
      CodeDrawResultHandler.framed,BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg,hk]
  obtain ⟨t,ht',hr⟩ := nonbranch_from_raw s input B R j ta ha rfl hno
  exact ⟨t,F,by omega,by simpa [input,d,e,j] using hr⟩

theorem join_then_branch (c d : CodeAdminResultJoin.Config)
    (entry final : CodeBranchAdapter.Config) (ta tb : Nat)
    (ha : CodeAdminResultJoin.run ta c = d) (hd : d.l = none)
    (hs : CodeDrawResultHandler.savedStatus d.var.1 = some true)
    (hk : CodeDrawResultHandler.savedKind d.var.1 = some .branch3)
    (hentry : entry =
      ⟨some (.inr .route),branchControl d.var.1.1,d.stk⟩)
    (hb : CodeBranchAdapter.run tb entry = final)
    (hf : final.l = none) :
    ∃ t ≤ ta+1+tb, run t (joinCfg c) = branchCfg d.var final := by
  obtain ⟨u,hu,hur⟩ := join_to_route c d ta ha hd
  obtain ⟨v,hv,hvr⟩ := branch_to_end d.var entry final tb hb hf
  refine ⟨v+1+u,by omega,?_⟩
  have hadd : run (v+1+u) (joinCfg c) =
      run v (run 1 (run u (joinCfg c))) := by
    simp [run,Function.iterate_add_apply]
  rw [hadd,hur,route_branch d.var d.stk hs hk,← hentry,hvr]

theorem branch_selected_from_raw (root : Code) (s : State)
    (hp : PositiveState s) (ht : Trace root s)
    (D a b : Nat) (hD : 0 < D) (f g h : Code)
    (cs : List Code) (outputWord : List Bool)
    (hstate : GeneratorCode.normalize s =
      ⟨.branch3 D a b f g h :: cs,outputWord.reverse⟩)
    (B R N : Nat) (hB : Nat.clog 2 D ≤ B)
    (tape : CappedSampler.Adaptive.Tape B R (N+1))
    (q : Fin D) (hq : CappedSampler.runWideBits D B R hB tape.1 = some q) :
    ∃ t F,
      t ≤ 13*(codeSize root+3)^2 + 3 +
        CodeAdminDraw.drawClock D B R +
        70*(q.val+a+b+
          (BranchSelection.inputWord f g h (CodeAdminNormalization.todoWord cs)).length+1) ∧
      let base := CodeHeaderDraw.resultCfg D B R N hB tape .branch3
        (BranchSelection.inputWord f g h (CodeAdminNormalization.todoWord cs))
        (List.replicate D true) (List.replicate a true)
        (List.replicate b true) outputWord F
      let d := CodeAdminDraw.drawResult D B R N hB tape .branch3
        (BranchSelection.inputWord f g h (CodeAdminNormalization.todoWord cs))
        (List.replicate D true) (List.replicate a true)
        (List.replicate b true) outputWord F
      let j : CodeAdminResultJoin.Config :=
        CodeAdminResultJoin.resultCfg ⟨none,(d.var,none),d.stk⟩
      run t (start s (RecursiveSamplingTape.writeTape B R (N+1) tape).val B R) =
        branchCfg j.var (CodeBranchAdapter.final base.var base.stk
          (List.replicate D true) outputWord q.val a b f g h
          (CodeAdminNormalization.todoWord cs)) := by
  let input := (RecursiveSamplingTape.writeTape B R (N+1) tape).val
  let rest := CodeAdminNormalization.todoWord cs
  let tail := BranchSelection.inputWord f g h rest
  obtain ⟨ta,F,hta,ha⟩ := CodeAdminResultJoin.branch_success_from_raw
    root s hp ht D a b hD f g h cs outputWord hstate B R N hB tape q hq
  let base := CodeHeaderDraw.resultCfg D B R N hB tape .branch3 tail
    (List.replicate D true) (List.replicate a true)
    (List.replicate b true) outputWord F
  let d := CodeAdminDraw.drawResult D B R N hB tape .branch3 tail
    (List.replicate D true) (List.replicate a true)
    (List.replicate b true) outputWord F
  let j : CodeAdminResultJoin.Config :=
    CodeAdminResultJoin.resultCfg ⟨none,(d.var,none),d.stk⟩
  have hjoin : CodeAdminResultJoin.run ta
      (CodeAdminResultJoin.start s input B R) = j := by
    simpa [tail,rest,BranchSelection.inputWord,List.append_assoc,j,d,input] using ha
  obtain ⟨tb,htb,hb⟩ := CodeBranchAdapter.branch_from_result
    D B R N hB tape q hq a b f g h rest outputWord F
  let entry : CodeBranchAdapter.Config :=
    ⟨some (.inr .route),branchControl j.var.1.1,j.stk⟩
  let final := CodeBranchAdapter.final base.var base.stk
    (List.replicate D true) outputWord q.val a b f g h rest
  have hentry : entry =
      ⟨some (.inr .route),branchControl j.var.1.1,j.stk⟩ := rfl
  have hbranch : CodeBranchAdapter.run tb entry = final := by
    simpa [entry,final,base,j,d,CodeAdminResultJoin.resultCfg,
      CodeAdminDraw.drawResult,CodeAdminBranchJoin.branchControl,
      selectorStart,tail,rest] using hb
  have hs : CodeDrawResultHandler.savedStatus j.var.1 = some true := by
    simpa [j,d,hq] using
      (CodeDrawResultHandler.result_status D B R N hB tape .branch3 tail
        (List.replicate D true) (List.replicate a true)
        (List.replicate b true) outputWord F).1
  have hk : CodeDrawResultHandler.savedKind j.var.1 = some .branch3 := by
    simpa [j,d] using
      (CodeDrawResultHandler.result_status D B R N hB tape .branch3 tail
        (List.replicate D true) (List.replicate a true)
        (List.replicate b true) outputWord F).2
  obtain ⟨t,ht',hr⟩ := join_then_branch
    (CodeAdminResultJoin.start s input B R) j entry final ta tb
    hjoin rfl hs hk hentry hbranch rfl
  refine ⟨t,F,?_,by simpa [input,rest,tail,base,d,j,final] using hr⟩
  have htb' : tb ≤ 70 *
      (q.val+a+b+
        (BranchSelection.inputWord f g h (CodeAdminNormalization.todoWord cs)).length+1) := by
    simpa [rest] using htb
  omega

#print axioms join_to_route
#print axioms join_then_branch
#print axioms branch_selected_from_raw
#print axioms done_from_raw
#print axioms failure_from_raw
#print axioms ticket_success_from_raw
#print axioms bit_success_from_raw

end
end Paper2.CodeAdminBranchJoin
