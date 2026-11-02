import EthInapproximability.CurrentPaper.CutoffProbe

/-!
# A physical bounded-clock probe

Source: frozen v8 `05-iteration.tex`, the bounded prefix clock. This finite
program calls the flagged simulator, branches on its actual returned halt
bit, reverses the remaining output twice into the decoder bank, and runs
the charged budget test. The caller supplies the displayed physical input
and cap banks; their preparation belongs to the outer prefix controller.
-/

namespace EthInapproximability.CurrentPaper.CutoffProbeMachine

noncomputable section
set_option linter.unusedSimpArgs false

open Turing TM2.Stmt
open BitMachineEncoding BitMachineComposition BitMachineSubroutine BitMachineSubroutineRenaming

variable (M : BitMachine.Machine)

noncomputable abbrev sim := FlaggedBoundedBitMachine.machine M
abbrev Stack := Fin (sim M).stackCount ⊕ CutoffBudgetTest.Stack
abbrev Label := Fin (sim M).labelCount ⊕ (CutoffBudgetTest.Label ⊕ Fin 3)
abbrev Control := Fin (sim M).controlCount × CutoffBudgetTest.Control
abbrev Config := TM2.Cfg (fun _ : Stack M => Bool) (Label M) (Control M)

def testInitial : CutoffBudgetTest.Control := ((none, none), (none, false))

def labelSwap : (CutoffBudgetTest.Label ⊕ (Fin (sim M).labelCount ⊕ Fin 3)) ≃ Label M where
  toFun := Sum.elim (fun l => .inr (.inl l)) (Sum.elim Sum.inl (fun l => .inr (.inr l)))
  invFun := Sum.elim (fun l => .inr (.inl l)) (Sum.elim Sum.inl (fun l => .inr (.inr l)))
  left_inv := by intro l; rcases l with l | (l | l) <;> rfl
  right_inv := by intro l; rcases l with l | (l | l) <;> rfl

def program : Label M → TM2.Stmt (fun _ : Stack M => Bool) (Label M) (Control M)
  | .inl l => liftStmt (some (.inr 0)) ((sim M).program l)
  | .inr (.inl l) => renameStmt (Equiv.sumComm _ _) (labelSwap M) (Equiv.prodComm _ _)
      (liftStmt none (CutoffBudgetTest.program l))
  | .inr (.inr i) => if i = 0 then
      pop (.inl (sim M).output) (fun v b => (v.1, ((b, none), (none, false))))
        (branch (fun v => v.2.1.1.getD false)
          (goto (fun _ => .inr (.inr 1)))
          (push (.inr (.inr 2)) (fun _ => false) halt))
    else if i = 1 then
      pop (.inl (sim M).output) (fun v b => (v.1, ((b, none), (none, false))))
        (branch (fun v => v.2.1.1.isSome)
          (push (.inr (.inl 1)) (fun v => v.2.1.1.getD false)
            (goto (fun _ => .inr (.inr 1))))
          (goto (fun _ => .inr (.inr 2))))
    else
      pop (.inr (.inl 1)) (fun v b => (v.1, ((b, none), (none, false))))
        (branch (fun v => v.2.1.1.isSome)
          (push (.inr (.inl 0)) (fun v => v.2.1.1.getD false)
            (goto (fun _ => .inr (.inr 2))))
          (load (fun v => (v.1, testInitial)) (goto (fun _ => .inr (.inl (.inl 0))))))

def bank (input saved binary cap work out : List Bool) : CutoffBudgetTest.Stack → List Bool :=
  Sum.elim ![input, saved, binary] ![cap, work, out]

def cfg (l : Option (Label M)) (v : Control M)
    (S : Fin (sim M).stackCount → List Bool)
    (input saved binary cap work out : List Bool) : Config M :=
  ⟨l, v, Sum.elim S (bank input saved binary cap work out)⟩

def run (t : ℕ) (c : Config M) := ((advance (program M))^[t]) c

theorem run_one (c : Config M) : run M 1 c = advance (program M) c := by simp [run]
theorem run_add (t u : ℕ) (c : Config M) : run M (t+u) c = run M u (run M t c) := by
  simpa only [run, Nat.add_comm] using Function.iterate_add_apply (advance (program M)) u t c

def withOutput (S : Fin (sim M).stackCount → List Bool) (bits : List Bool) :=
  Function.update S (sim M).output bits

theorem withOutput_apply (S : Fin (sim M).stackCount → List Bool) (bits : List Bool) :
    withOutput M S bits (sim M).output = bits := by simp [withOutput]

theorem withOutput_same (S : Fin (sim M).stackCount → List Bool) :
    withOutput M S (S (sim M).output) = S := Function.update_eq_self _ _

theorem withOutput_update (S : Fin (sim M).stackCount → List Bool) (a b : List Bool) :
    withOutput M (withOutput M S a) b = withOutput M S b := by simp [withOutput]

theorem cfg_ext (l : Option (Label M)) (v : Control M)
    (S T : Fin (sim M).stackCount → List Bool) (a b c d e f : List Bool) (h : S = T) :
    cfg M l v S a b c d e f = cfg M l v T a b c d e f := by rw [h]

theorem reverse_step (v : Fin (sim M).controlCount) (S : Fin (sim M).stackCount → List Bool)
    (x : Bool) (xs saved cap : List Bool) (w : CutoffBudgetTest.Control) :
    advance (program M)
      (cfg M (some (.inr (.inr 1))) (v,w) (withOutput M S (x::xs)) [] saved [] cap [] []) =
    cfg M (some (.inr (.inr 1))) (v,((some x,none),(none,false)))
      (withOutput M S xs) [] (x::saved) [] cap [] [] := by
  simp only [advance, TM2.step, program, cfg, TM2.stepAux, bank, withOutput,
    Fin.reduceEq, ite_false, ite_true,
    Sum.elim_inl, Function.update_self, List.head?_cons, List.tail_cons,
    Option.isSome_some, cond_true, Option.getD_some, Sum.elim_inr]
  congr 1
  funext j
  cases j with
  | inl j => by_cases h : j = (sim M).output <;> simp [h, Function.update]
  | inr j => cases j with
    | inl j => fin_cases j <;> simp [Function.update]
    | inr j => fin_cases j <;> simp [Function.update]

theorem reverse_done (v : Fin (sim M).controlCount) (S : Fin (sim M).stackCount → List Bool)
    (saved cap : List Bool) (w : CutoffBudgetTest.Control) :
    advance (program M)
      (cfg M (some (.inr (.inr 1))) (v,w) (withOutput M S []) [] saved [] cap [] []) =
    cfg M (some (.inr (.inr 2))) (v,testInitial) (withOutput M S []) [] saved [] cap [] [] := by
  simp only [advance, TM2.step, program, cfg, TM2.stepAux, bank, withOutput,
    Fin.reduceEq, ite_false, ite_true,
    Sum.elim_inl, Function.update_self, List.head?_nil, List.tail_nil,
    Option.isSome_none, cond_false, Option.getD_some]
  congr 1
  funext j
  cases j with
  | inl j => by_cases h : j = (sim M).output <;> simp [h, Function.update]
  | inr j => rfl

theorem reverse_run (v : Fin (sim M).controlCount) (S : Fin (sim M).stackCount → List Bool)
    (xs saved cap : List Bool) (w : CutoffBudgetTest.Control) :
    run M (xs.length+1)
      (cfg M (some (.inr (.inr 1))) (v,w) (withOutput M S xs) [] saved [] cap [] []) =
    cfg M (some (.inr (.inr 2))) (v,testInitial)
      (withOutput M S []) [] (xs.reverse++saved) [] cap [] [] := by
  induction xs generalizing saved w with
  | nil => simpa only [List.length_nil, zero_add, List.reverse_nil, List.nil_append,
      run_one] using reverse_done M v S saved cap w
  | cons x xs ih =>
      rw [show (x::xs).length+1 = 1+(xs.length+1) by simp; omega, run_add, run_one,
        reverse_step, ih]
      simp [List.reverse_cons, List.append_assoc]

theorem restore_step (v : Fin (sim M).controlCount) (S : Fin (sim M).stackCount → List Bool)
    (x : Bool) (xs input cap : List Bool) (w : CutoffBudgetTest.Control) :
    advance (program M)
      (cfg M (some (.inr (.inr 2))) (v,w) S input (x::xs) [] cap [] []) =
    cfg M (some (.inr (.inr 2))) (v,((some x,none),(none,false))) S (x::input) xs [] cap [] [] := by
  simp only [advance, TM2.step, program, cfg, TM2.stepAux, bank,
    Sum.elim_inr, Sum.elim_inl, Fin.reduceEq, ite_false, ite_true,
    Matrix.cons_val_one, Matrix.cons_val_zero, List.head?_cons, List.tail_cons,
    Option.isSome_some, cond_true, Option.getD_some]
  congr 1
  funext j
  cases j with
  | inl j => simp [Function.update]
  | inr j => cases j with
    | inl j => fin_cases j <;> simp [Function.update]
    | inr j => fin_cases j <;> simp [Function.update]

theorem restore_done (v : Fin (sim M).controlCount) (S : Fin (sim M).stackCount → List Bool)
    (input cap : List Bool) (w : CutoffBudgetTest.Control) :
    advance (program M)
      (cfg M (some (.inr (.inr 2))) (v,w) S input [] [] cap [] []) =
    cfg M (some (.inr (.inl (.inl 0)))) (v,testInitial) S input [] [] cap [] [] := by
  simp only [advance, TM2.step, program, cfg, TM2.stepAux, bank,
    Sum.elim_inr, Sum.elim_inl, Fin.reduceEq, ite_false, ite_true,
    Matrix.cons_val_one, Matrix.cons_val_zero, List.head?_nil, List.tail_nil,
    Option.isSome_none, cond_false, Option.getD_some]
  congr 1
  funext j
  cases j with
  | inl j => simp [Function.update]
  | inr j => cases j with
    | inl j => fin_cases j <;> simp [Function.update]
    | inr j => fin_cases j <;> simp [Function.update]

theorem restore_run (v : Fin (sim M).controlCount) (S : Fin (sim M).stackCount → List Bool)
    (xs input cap : List Bool) (w : CutoffBudgetTest.Control) :
    run M (xs.length+1)
      (cfg M (some (.inr (.inr 2))) (v,w) S input xs [] cap [] []) =
    cfg M (some (.inr (.inl (.inl 0)))) (v,testInitial) S (xs.reverse++input) [] [] cap [] [] := by
  induction xs generalizing input w with
  | nil => simpa only [List.length_nil, zero_add, List.reverse_nil, List.nil_append,
      run_one] using restore_done M v S input cap w
  | cons x xs ih =>
      rw [show (x::xs).length+1 = 1+(xs.length+1) by simp; omega, run_add, run_one,
        restore_step, ih]
      simp [List.reverse_cons, List.append_assoc]

theorem test_phase (v : Fin (sim M).controlCount) (S : Fin (sim M).stackCount → List Bool)
    (input cap : List Bool) :
    ∃ t c, t ≤ input.length+2+(cap.length+1)*(4*input.length+5) ∧
      run M t (cfg M (some (.inr (.inl (.inl 0)))) (v,testInitial) S input [] [] cap [] []) = c ∧
      c.l = none ∧ c.stk (.inr (.inr 2)) =
        decide (CutoffBitMachine.decodedNat input ≤ cap.length) ::
          List.replicate (min (CutoffBitMachine.decodedNat input) cap.length) true := by
  obtain ⟨t,c,ht,hc,hh,ho⟩ := CutoffBudgetTest.test_run input cap []
  obtain ⟨u,hu,he⟩ := lift_outputs_renamed (Equiv.sumComm _ _) (labelSwap M)
    (Equiv.prodComm _ _) CutoffBudgetTest.program (program M) none (fun _ => rfl)
    v S (CutoffBudgetTest.start input cap []) t (by
      change (CutoffBudgetTest.run t _).l = none; rw [hc,hh])
  change run M u _ = renameCfg _ _ _ (liftCfg none v S (CutoffBudgetTest.run t _)) at he
  rw [hc] at he
  have hstart : renameCfg (Equiv.sumComm _ _) (labelSwap M) (Equiv.prodComm _ _)
      (liftCfg (none : Option (Fin (sim M).labelCount ⊕ Fin 3)) v S
        (CutoffBudgetTest.start input cap [])) =
      cfg M (some (.inr (.inl (.inl 0)))) (v,testInitial) S input [] [] cap [] [] := by
    unfold renameCfg liftCfg CutoffBudgetTest.start CutoffOutputDecoder.cfg cfg bank
    congr 1
    funext j
    cases j with
    | inl j => rfl
    | inr j => cases j with
      | inl j => fin_cases j <;> rfl
      | inr j => fin_cases j <;> rfl
  rw [hstart] at he
  refine ⟨u,_,hu.trans ht,he,?_,?_⟩
  · simp [renameCfg,liftCfg,hh]
  · simpa only [renameCfg,liftCfg,Equiv.sumComm_symm,Equiv.sumComm_apply,
      Sum.elim_inl,List.append_nil] using ho

theorem gate_step (v : Fin (sim M).controlCount) (S : Fin (sim M).stackCount → List Bool)
    (halted : Bool) (payload cap : List Bool) :
    advance (program M)
      (cfg M (some (.inr (.inr 0))) (v,testInitial)
        (withOutput M S (halted::payload)) [] [] [] cap [] []) =
      cfg M (if halted then some (.inr (.inr 1)) else none)
        (v,((some halted,none),(none,false))) (withOutput M S payload)
        [] [] [] cap [] (if halted then [] else [false]) := by
  cases halted <;>
    simp only [advance,TM2.step,program,cfg,TM2.stepAux,bank,withOutput,
      Fin.reduceEq,ite_true,Sum.elim_inl,Sum.elim_inr,Function.update_self,
      List.head?_cons,List.tail_cons,Option.getD_some,cond_false,cond_true]
  all_goals
    congr 1
    funext j
    cases j with
    | inl j => by_cases h : j=(sim M).output <;> simp [h,Function.update]
    | inr j => cases j with
      | inl j => fin_cases j <;> simp [Function.update]
      | inr j => fin_cases j <;> simp [Function.update]

def answer (halted : Bool) (payload cap : List Bool) : List Bool :=
  if halted then decide (CutoffBitMachine.decodedNat payload ≤ cap.length) ::
    List.replicate (min (CutoffBitMachine.decodedNat payload) cap.length) true else [false]

theorem returned_run (v : Fin (sim M).controlCount) (S : Fin (sim M).stackCount → List Bool)
    (halted : Bool) (payload cap : List Bool) :
    ∃ t c, t ≤ 3*payload.length+5+(cap.length+1)*(4*payload.length+5) ∧
      run M t (cfg M (some (.inr (.inr 0))) (v,testInitial)
        (withOutput M S (halted::payload)) [] [] [] cap [] []) = c ∧
      c.l = none ∧ c.stk (.inr (.inr 2)) = answer halted payload cap := by
  cases halted with
  | false =>
      refine ⟨1,cfg M none (v,((some false,none),(none,false)))
        (withOutput M S payload) [] [] [] cap [] [false],by omega,?_,rfl,rfl⟩
      exact (run_one M _).trans (gate_step M v S false payload cap)
  | true =>
      obtain ⟨t,c,ht,hc,hh,ho⟩ := test_phase M v (withOutput M S []) payload cap
      refine ⟨1+(payload.length+1)+(payload.reverse.length+1)+t,c,?_,?_,hh,ho⟩
      · simp only [List.length_reverse]; omega
      · rw [run_add M (1+(payload.length+1)+(payload.reverse.length+1)) t,
          run_add M (1+(payload.length+1)) (payload.reverse.length+1),
          run_add M 1 (payload.length+1),run_one,gate_step]
        simp only [cond_true,ite_true]
        rw [reverse_run,List.append_nil,restore_run]
        simpa only [List.append_nil,List.reverse_reverse] using hc

def start (input cap : List Bool) : Config M :=
  liftCfg (some (.inr 0)) testInitial (bank [] [] [] cap [] []) ((sim M).init input)

theorem simulation_phase (input cap : List Bool) :
    ∃ (t : ℕ) (c : (sim M).Config), t ≤ 2*(input.length+1)+1 ∧
      run M t (start M input cap) =
        cfg M (some (.inr (.inr 0))) (c.var,testInitial) c.stk [] [] [] cap [] [] ∧
      c.stk (sim M).output = FlaggedBoundedBitMachine.report M input := by
  obtain ⟨hh,ho⟩ := BitMachine.outputsWithin_at_bound _
    (FlaggedBoundedBitMachine.outputs_all M input)
  obtain ⟨t,ht,hr⟩ := lift_outputs (sim M).program (program M)
    (some (.inr 0)) (fun _ => rfl) testInitial (bank [] [] [] cap [] [])
    ((sim M).init input) (2*(input.length+1)+1) hh
  refine ⟨t,(sim M).run (2*(input.length+1)+1) ((sim M).init input),ht,?_,ho⟩
  change run M t (start M input cap) = liftCfg _ _ _ ((sim M).run _ _) at hr
  simpa only [liftCfg,hh,Option.map_some,cfg] using hr

theorem probe_run (input cap : List Bool) :
    ∃ t c, t ≤ 2*(input.length+1)+1+
        (3*(FlaggedBoundedBitMachine.report M input).tail.length+5+
          (cap.length+1)*(4*(FlaggedBoundedBitMachine.report M input).tail.length+5)) ∧
      run M t (start M input cap) = c ∧ c.l = none ∧
      (c.stk (.inr (.inr 2))).head? =
        some (CutoffProbe.interpret cap.length (FlaggedBoundedBitMachine.report M input)) ∧
      (c.stk (.inr (.inr 2))).length ≤ cap.length+1 := by
  obtain ⟨t,c,ht,hc,ho⟩ := simulation_phase M input cap
  let b := (FlaggedBoundedBitMachine.report M input).headD false
  let p := (FlaggedBoundedBitMachine.report M input).tail
  have hr : FlaggedBoundedBitMachine.report M input = b::p := by
    simp only [b,p,FlaggedBoundedBitMachine.report,List.headD_cons,List.tail_cons]
  obtain ⟨u,d,hu,hd,hh,hout⟩ := returned_run M c.var c.stk b p cap
  have hs : withOutput M c.stk (b::p) = c.stk := by rw [←hr,←ho,withOutput_same]
  rw [hs] at hd
  refine ⟨t+u,d,by dsimp [p] at hu; omega,?_,hh,?_,?_⟩
  · rw [run_add,hc,hd]
  · rw [hout,hr]
    cases b <;> simp [answer,CutoffProbe.interpret]
  · rw [hout]
    cases b <;> simp [answer,List.length_replicate,Nat.min_le_right]

def polynomialConstant : ℕ := 7*(3*(sim M).pushBound+1)+13

theorem payload_length_all (input : List Bool) :
    (FlaggedBoundedBitMachine.report M input).tail.length ≤
      (3*(sim M).pushBound+1)*(input.length+1) := by
  have h := BitMachine.output_length_bound (sim M)
    (FlaggedBoundedBitMachine.outputs_all M input)
  have ht : (FlaggedBoundedBitMachine.report M input).tail.length ≤
      (FlaggedBoundedBitMachine.report M input).length := by simp
  nlinarith

/-- All loaded inputs terminate, including malformed simulator packets.
No canonical integer encoding or source termination is required. -/
theorem probe_run_polynomial (input cap : List Bool) :
    ∃ t c, t ≤ polynomialConstant M*(input.length+cap.length+1)^2 ∧
      run M t (start M input cap) = c ∧ c.l = none ∧
      (c.stk (.inr (.inr 2))).head? =
        some (CutoffProbe.interpret cap.length (FlaggedBoundedBitMachine.report M input)) ∧
      (c.stk (.inr (.inr 2))).length ≤ cap.length+1 := by
  obtain ⟨t,c,ht,hc,hh,ho,hl⟩ := probe_run M input cap
  refine ⟨t,c,ht.trans ?_,hc,hh,ho,hl⟩
  let A := input.length+cap.length+1
  let K := 3*(sim M).pushBound+1
  have hA : 1 ≤ A := by dsimp [A]; omega
  have hi : input.length+1 ≤ A := by dsimp [A]; omega
  have hc : cap.length+1 ≤ A := by dsimp [A]; omega
  have hp : (FlaggedBoundedBitMachine.report M input).tail.length ≤ K*A :=
    (payload_length_all M input).trans (Nat.mul_le_mul_left K hi)
  have hmul : (cap.length+1)*(4*(FlaggedBoundedBitMachine.report M input).tail.length+5) ≤
      A*(4*(K*A)+5) := Nat.mul_le_mul hc (by omega)
  change _ ≤ (7*K+13)*A^2
  nlinarith [Nat.mul_le_mul_left (3*K+7) (show A ≤ A^2 by nlinarith)]

/-- A probe at every index in the bounded prefix returns exactly the
paper's success predicate. Its cost includes simulation, transfers, and
decoding/comparison; the caller still prepares the displayed initial bank. -/
theorem probe_in_prefix (n k : ℕ) (hk : k ≤ n) :
    ∃ t c, t ≤ (7*(M.pushBound+2)+20)*(n+1)^2 ∧
      run M t (start M (CutoffProbe.input n k) (List.replicate n true)) = c ∧
      c.l = none ∧ (c.stk (.inr (.inr 2))).head? =
        some (SlowClock.succeeds (CutoffBitMachine.clock M) n k) ∧
      (c.stk (.inr (.inr 2))).length ≤ n+1 := by
  obtain ⟨t,c,ht,hc,hh,ho,hl⟩ := probe_run M (CutoffProbe.input n k) (List.replicate n true)
  simp only [List.length_replicate] at ht ho hl
  refine ⟨t,c,ht.trans ?_,hc,hh,?_,hl⟩
  · have hi := CutoffProbe.input_length n k
    have hp := CutoffProbe.payload_length_in_prefix M n k hk
    change (FlaggedBoundedBitMachine.report M (CutoffProbe.input n k)).tail.length ≤
      (M.pushBound+2)*(n+1) at hp
    have hm := Nat.mul_le_mul_left (n+1)
      (show 4*(FlaggedBoundedBitMachine.report M (CutoffProbe.input n k)).tail.length+5 ≤
        4*((M.pushBound+2)*(n+1))+5 by omega)
    nlinarith [Nat.mul_le_mul_left (3*(M.pushBound+2)+11)
      (show n+1 ≤ (n+1)^2 by nlinarith)]
  · change (c.stk (.inr (.inr 2))).head? = some
      (CutoffProbe.interpret n (CutoffProbe.report M n k)) at ho
    rwa [CutoffProbe.interpret_report] at ho

def machine : BitMachine.Machine :=
  ofFinite (.inl (sim M).input : Stack M) (.inr (.inr 2)) (.inl (sim M).start : Label M)
    ((sim M).initial,testInitial) (program M)

def encode (c : Config M) : (machine M).Config :=
  renameCfg (Fintype.equivFin (Stack M)) (Fintype.equivFin (Label M))
    (Fintype.equivFin (Control M)) c

theorem machine_run (t : ℕ) (c : Config M) :
    (machine M).run t (encode M c) = encode M (run M t c) :=
  ofFinite_run _ _ _ _ _ c t

def bankPushBound : ℕ := ∑ l : Label M, BitMachine.pushBound (program M l)

theorem step_stack_length (c : Config M) (j : Stack M) :
    ((advance (program M) c).stk j).length ≤ (c.stk j).length+bankPushBound M := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => simp [advance,TM2.step]
  | some l =>
      have h := BitMachine.stepAux_length (program M l) v S j
      have hb : BitMachine.pushBound (program M l) ≤ bankPushBound M :=
        Finset.single_le_sum (f := fun l => BitMachine.pushBound (program M l))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
      exact h.trans (Nat.add_le_add_left hb _)

/-- Every transient stack has a physical bit-length bound, so clearing
the probe bank in an outer loop is separately and explicitly chargeable. -/
theorem run_stack_length (t : ℕ) (c : Config M) (j : Stack M) :
    ((run M t c).stk j).length ≤ (c.stk j).length+t*bankPushBound M := by
  induction t with
  | zero => simp [run]
  | succ t ih =>
      have h := (step_stack_length M (run M t c) j).trans (Nat.add_le_add_right ih _)
      simpa [run,Function.iterate_succ_apply',Nat.succ_mul,Nat.add_assoc] using h

theorem start_stack_length (input cap : List Bool) (j : Stack M) :
    ((start M input cap).stk j).length ≤ input.length+cap.length := by
  cases j with
  | inl j =>
      simp only [start,liftCfg,Sum.elim_inl,BitMachine.Machine.init]
      split <;> simp
  | inr j => cases j with
    | inl j => fin_cases j <;> simp [start,liftCfg,bank]
    | inr j => fin_cases j <;> simp [start,liftCfg,bank]

theorem probe_run_with_bank_bound (input cap : List Bool) :
    ∃ t c, t ≤ polynomialConstant M*(input.length+cap.length+1)^2 ∧
      run M t (start M input cap) = c ∧ c.l = none ∧
      (c.stk (.inr (.inr 2))).head? =
        some (CutoffProbe.interpret cap.length (FlaggedBoundedBitMachine.report M input)) ∧
      (c.stk (.inr (.inr 2))).length ≤ cap.length+1 ∧
      ∀ j, (c.stk j).length ≤ input.length+cap.length+t*bankPushBound M := by
  obtain ⟨t,c,ht,hc,hh,ho,hl⟩ := probe_run_polynomial M input cap
  refine ⟨t,c,ht,hc,hh,ho,hl,?_⟩
  intro j
  have hs := run_stack_length M t (start M input cap) j
  rw [hc] at hs
  exact hs.trans (Nat.add_le_add_right (start_stack_length M input cap j) _)

/-- The source program receives arbitrary raw bits. Canonical integer
encodings are needed only when identifying this with the paper's index. -/
theorem probe_packed (n : ℕ) (bits : List Bool) :
    ∃ t c, t ≤ polynomialConstant M*(2*n+bits.length+2)^2 ∧
      run M t (start M (BoundedBitMachine.packed n bits) (List.replicate n true)) = c ∧
      c.l = none ∧ (c.stk (.inr (.inr 2))).head? = some
        (decide ((M.run n (M.init bits)).l = none) &&
          decide (CutoffBitMachine.decodedNat ((M.run n (M.init bits)).stk M.output) ≤ n)) ∧
      (c.stk (.inr (.inr 2))).length ≤ n+1 ∧
      ∀ j, (c.stk j).length ≤ 2*n+bits.length+1+t*bankPushBound M := by
  obtain ⟨t,c,ht,hc,hh,ho,hl,hs⟩ := probe_run_with_bank_bound M
    (BoundedBitMachine.packed n bits) (List.replicate n true)
  have he : (BoundedBitMachine.packed n bits).length+(List.replicate n true).length =
      2*n+bits.length+1 := by
    simp only [BoundedBitMachine.packed,List.length_append,List.length_replicate,List.length_cons]
    omega
  rw [he] at ht hs
  simp only [List.length_replicate] at ho hl
  rw [FlaggedBoundedBitMachine.report_packed] at ho
  exact ⟨t,c,ht,hc,hh,ho,hl,hs⟩

theorem start_eq (input cap : List Bool) :
    start M input cap = cfg M (some (.inl (sim M).start)) ((sim M).initial,testInitial)
      (fun j => if j=(sim M).input then input else []) [] [] [] cap [] [] := rfl

end
end EthInapproximability.CurrentPaper.CutoffProbeMachine
