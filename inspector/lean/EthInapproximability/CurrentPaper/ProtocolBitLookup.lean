import EthInapproximability.CurrentPaper.BitMachine
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic

/-!
# A finite bit-stack machine for certificate-table lookup

Source: current paper v8, `03-exact-hardness.tex`, the NP-membership paragraph.
This is a concrete implementation of the bit-list lookup used by the protocol
verifier. The first stack receives `true^i ++ false :: q`; the second stack is
initially empty. The machine returns the singleton `[q[i]?.getD false]`, clears
its working stack, and restores its finite control registers.

Every transition is a fixed finite TM2 statement acting on Boolean stacks.
The index is stored in unary on a stack, never in an unbounded control register.
The proved time bound concerns these literal transitions. This component does
not yet implement the complete protocol verifier or its binary header parser.
-/

namespace EthInapproximability.CurrentPaper.ProtocolBitLookup

open Turing
open Turing.TM2.Stmt

/-- Five labels suffice for the lookup and its final cleanup. -/
inductive Label where
  | count
  | skip
  | readBit
  | clear
  | finish
  deriving DecidableEq, Fintype

/-- Stack zero holds the input and then the answer; stack one holds the unary
index. The two finite registers store the answer and the last test result. -/
def program : Label → TM2.Stmt (fun _ : Fin 2 => Bool) Label (Bool × Bool)
  | .count =>
      pop 0 (fun s b => (s.1, b.getD false))
        (branch Prod.snd
          (push 1 (fun _ => true) (goto (fun _ => .count)))
          (goto (fun _ => .skip)))
  | .skip =>
      pop 1 (fun s b => (s.1, b.isSome))
        (branch Prod.snd
          (pop 0 (fun s _ => s) (goto (fun _ => .skip)))
          (goto (fun _ => .readBit)))
  | .readBit =>
      pop 0 (fun s b => (b.getD false, s.2)) (goto (fun _ => .clear))
  | .clear =>
      pop 0 (fun s b => (s.1, b.isSome))
        (branch Prod.snd (goto (fun _ => .clear)) (goto (fun _ => .finish)))
  | .finish =>
      push 0 Prod.fst (load (fun _ => (false, false)) halt)

/-- An actual finite TM2 machine, with two stacks and two Boolean registers. -/
def machine : FinTM2 where
  K := Fin 2
  k₀ := 0
  k₁ := 0
  Γ _ := Bool
  Λ := Label
  main := .count
  σ := Bool × Bool
  initialState := (false, false)
  m := program

def stackContents (input counter : List Bool) : Fin 2 → List Bool :=
  fun k => if k = 0 then input else counter

def cfg (label : Option Label) (state : Bool × Bool) (input counter : List Bool) :
    machine.Cfg :=
  ⟨label, state, stackContents input counter⟩

@[simp] theorem stacks_zero (input counter : List Bool) : stackContents input counter 0 = input := rfl

@[simp] theorem stacks_one (input counter : List Bool) : stackContents input counter 1 = counter := rfl

@[simp] theorem update_stacks_zero (input counter new : List Bool) :
    Function.update (stackContents input counter) 0 new = stackContents new counter := by
  funext k
  fin_cases k <;> simp [stackContents, Function.update]

@[simp] theorem update_stacks_one (input counter new : List Bool) :
    Function.update (stackContents input counter) 1 new = stackContents input new := by
  funext k
  fin_cases k <;> simp [stackContents, Function.update]

/-- Iterating the actual partial transition function; arrival at the halting
configuration is retained as `some` before the next transition returns `none`. -/
def run (steps : Nat) (c : machine.Cfg) : Option machine.Cfg :=
  (fun x : Option machine.Cfg => x.bind machine.step)^[steps] (some c)

@[simp] theorem run_zero (c : machine.Cfg) : run 0 c = some c := rfl

theorem run_succ_of_step {c d : machine.Cfg} (h : machine.step c = some d) (n : Nat) :
    run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, Option.bind_some, h]

theorem run_add_of_run {c d : machine.Cfg} {m : Nat} (h : run m c = some d) (n : Nat) :
    run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

theorem step_count_true (a b : Bool) (q counter : List Bool) :
    machine.step (cfg (some .count) (a, b) (true :: q) counter) =
      some (cfg (some .count) (a, true) q (true :: counter)) := by
  simp [FinTM2.step, TM2.step, TM2.stepAux, machine, program, cfg]
  congr 2
  funext k
  fin_cases k <;> rfl

theorem step_count_false (a b : Bool) (q counter : List Bool) :
    machine.step (cfg (some .count) (a, b) (false :: q) counter) =
      some (cfg (some .skip) (a, false) q counter) := by
  simp [FinTM2.step, TM2.step, TM2.stepAux, machine, program, cfg]
  congr 2
  funext k
  fin_cases k <;> rfl

theorem step_skip_nonempty (a b bit : Bool) (q counter : List Bool) :
    machine.step (cfg (some .skip) (a, b) q (bit :: counter)) =
      some (cfg (some .skip) (a, true) q.tail counter) := by
  simp [FinTM2.step, TM2.step, TM2.stepAux, machine, program, cfg]
  congr 2
  funext k
  fin_cases k <;> rfl

theorem step_skip_empty (a b : Bool) (q : List Bool) :
    machine.step (cfg (some .skip) (a, b) q []) =
      some (cfg (some .readBit) (a, false) q []) := by
  simp [FinTM2.step, TM2.step, TM2.stepAux, machine, program, cfg]
  congr 2
  funext k
  fin_cases k <;> rfl

theorem step_read (a b : Bool) (q : List Bool) :
    machine.step (cfg (some .readBit) (a, b) q []) =
      some (cfg (some .clear) (q.head?.getD false, b) q.tail []) := by
  simp [FinTM2.step, TM2.step, TM2.stepAux, machine, program, cfg]
  congr 2
  funext k
  fin_cases k <;> rfl

theorem step_clear_nonempty (a b bit : Bool) (q : List Bool) :
    machine.step (cfg (some .clear) (a, b) (bit :: q) []) =
      some (cfg (some .clear) (a, true) q []) := by
  simp [FinTM2.step, TM2.step, TM2.stepAux, machine, program, cfg]
  congr 2
  funext k
  fin_cases k <;> rfl

theorem step_clear_empty (a b : Bool) :
    machine.step (cfg (some .clear) (a, b) [] []) =
      some (cfg (some .finish) (a, false) [] []) := by
  simp [FinTM2.step, TM2.step, TM2.stepAux, machine, program, cfg]
  congr 2
  funext k
  fin_cases k <;> rfl

theorem step_finish (a b : Bool) :
    machine.step (cfg (some .finish) (a, b) [] []) =
      some (cfg none (false, false) [a] []) := by
  simp [FinTM2.step, TM2.step, TM2.stepAux, machine, program, cfg]
  congr 2
  funext k
  fin_cases k <;> rfl

theorem count_correct (i m : Nat) (a b : Bool) (q : List Bool) :
    run (i + 1) (cfg (some .count) (a, b)
      (List.replicate i true ++ false :: q) (List.replicate m true)) =
      some (cfg (some .skip) (a, false) q (List.replicate (i + m) true)) := by
  induction i generalizing m b with
  | zero =>
      simpa using run_succ_of_step (step_count_false a b q (List.replicate m true)) 0
  | succ i ih =>
      rw [List.replicate_succ, List.cons_append]
      rw [run_succ_of_step (step_count_true a b
        (List.replicate i true ++ false :: q) (List.replicate m true))]
      rw [← List.replicate_succ]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (m + 1) true

theorem tail_drop (q : List Bool) (i : Nat) : (q.drop i).tail = q.drop (i + 1) := by
  induction i generalizing q with
  | zero => cases q <;> rfl
  | succ i ih =>
      cases q with
      | nil => rfl
      | cons bit q => simpa using ih q

theorem skip_correct (i : Nat) (a b : Bool) (q : List Bool) :
    run (i + 1) (cfg (some .skip) (a, b) q (List.replicate i true)) =
      some (cfg (some .readBit) (a, false) (q.drop i) []) := by
  induction i generalizing b q with
  | zero => simpa using run_succ_of_step (step_skip_empty a b q) 0
  | succ i ih =>
      rw [List.replicate_succ]
      rw [run_succ_of_step (step_skip_nonempty a b true q (List.replicate i true))]
      simpa only [← List.tail_drop_eq_drop_tail, tail_drop] using ih true q.tail

theorem clear_correct (a b : Bool) (q : List Bool) :
    run (q.length + 2) (cfg (some .clear) (a, b) q []) =
      some (cfg none (false, false) [a] []) := by
  induction q generalizing b with
  | nil =>
      simp only [List.length_nil, Nat.zero_add]
      rw [run_succ_of_step (step_clear_empty a b) 1,
        run_succ_of_step (step_finish a false) 0]
      rfl
  | cons bit q ih =>
      rw [List.length_cons]
      rw [show q.length + 1 + 2 = (q.length + 2) + 1 by omega,
        run_succ_of_step (step_clear_nonempty a b bit q)]
      exact ih true

theorem read_correct (a b : Bool) (q : List Bool) :
    run (q.tail.length + 3) (cfg (some .readBit) (a, b) q []) =
      some (cfg none (false, false) [q.head?.getD false] []) := by
  rw [show q.tail.length + 3 = (q.tail.length + 2) + 1 by omega,
    run_succ_of_step (step_read a b q)]
  exact clear_correct (q.head?.getD false) b q.tail

def encodeInput (i : Nat) (q : List Bool) : List Bool :=
  List.replicate i true ++ false :: q

def exactTime (i : Nat) (q : List Bool) : Nat :=
  2 * i + (q.drop (i + 1)).length + 5

theorem head_drop_lookup (q : List Bool) (i : Nat) :
    (q.drop i).head?.getD false = q[i]?.getD false := by
  induction i generalizing q with
  | zero => cases q <;> simp
  | succ i ih => cases q <;> simp_all

/-- Exact execution of the finite machine, including cleanup and restoration
of its control registers. An out-of-range index returns `false`. -/
theorem run_correct (i : Nat) (q : List Bool) :
    run (exactTime i q) (cfg (some .count) (false, false) (encodeInput i q) []) =
      some (cfg none (false, false) [q[i]?.getD false] []) := by
  have hc := count_correct i 0 false false q
  simp only [Nat.add_zero, List.replicate_zero] at hc
  have hs := skip_correct i false false q
  have hr := read_correct false false (q.drop i)
  have ht : exactTime i q = (i + 1) + ((i + 1) + (q.drop i).tail.length + 3) := by
    simp only [exactTime, tail_drop]
    omega
  simp only [encodeInput]
  rw [ht, run_add_of_run hc]
  rw [show (i + 1) + (q.drop i).tail.length + 3 =
    (i + 1) + ((q.drop i).tail.length + 3) by omega, run_add_of_run hs, hr]
  rw [head_drop_lookup]

theorem exactTime_le (i : Nat) (q : List Bool) :
    exactTime i q ≤ 2 * i + q.length + 5 := by
  simp only [exactTime, List.length_drop]
  omega

theorem exactTime_le_inputLength (i : Nat) (q : List Bool) :
    exactTime i q ≤ 2 * (encodeInput i q).length + 3 := by
  have h := exactTime_le i q
  simp only [encodeInput, List.length_append, List.length_replicate, List.length_cons]
  omega

theorem initList_eq (input : List Bool) :
    initList machine input = cfg (some .count) (false, false) input [] := by
  unfold initList cfg machine
  congr 1

theorem haltList_eq (output : List Bool) :
    haltList machine output = cfg none (false, false) output [] := by
  unfold haltList cfg machine
  congr 1

/-- The native Mathlib execution certificate for the actual finite machine. -/
def outputsInExactTime (i : Nat) (q : List Bool) :
    TM2OutputsInTime machine (encodeInput i q) (some [q[i]?.getD false]) (exactTime i q) where
  steps := exactTime i q
  evals_in_steps := by
    change run (exactTime i q) (initList machine (encodeInput i q)) =
      some (haltList machine [q[i]?.getD false])
    rw [initList_eq, haltList_eq, run_correct]
    rfl
  steps_le_m := le_rfl

/-- Linear bit-stack time, measured in the length of the actual unary-index
input encoding. The finite program has no input-dependent instruction bodies. -/
def outputsInLinearTime (i : Nat) (q : List Bool) :
    TM2OutputsInTime machine (encodeInput i q) (some [q[i]?.getD false])
      (2 * (encodeInput i q).length + 3) where
  toEvalsTo := (outputsInExactTime i q).toEvalsTo
  steps_le_m := exactTime_le_inputLength i q

/-- The unary-index lookup is polynomial-time computable in Mathlib's actual
finite-machine definition, with the displayed literal input encoding. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime
      (fun p : Nat × List Bool => encodeInput p.1 p.2)
      (fun b : Bool => [b]) (fun p => p.2[p.1]?.getD false) where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 2 * Polynomial.X + Polynomial.C 3
  outputsFun p := by
    change TM2OutputsInTime machine (List.map id (encodeInput p.1 p.2))
      (some [p.2[p.1]?.getD false]) _
    simpa using outputsInLinearTime p.1 p.2

/-- Explicit numbering of the five labels, for the paper's common machine
interface. These are finite tables, not chosen encodings of unbounded data. -/
def labelCode : Label ≃ Fin 5 where
  toFun
    | .count => 0
    | .skip => 1
    | .readBit => 2
    | .clear => 3
    | .finish => 4
  invFun k := match k.val with
    | 0 => .count
    | 1 => .skip
    | 2 => .readBit
    | 3 => .clear
    | _ => .finish
  left_inv l := by cases l <;> rfl
  right_inv k := by fin_cases k <;> rfl

/-- Explicit numbering of the four settings of two Boolean registers. -/
def controlCode : (Bool × Bool) ≃ Fin 4 where
  toFun
    | (false, false) => 0
    | (false, true) => 1
    | (true, false) => 2
    | (true, true) => 3
  invFun k := match k.val with
    | 0 => (false, false)
    | 1 => (false, true)
    | 2 => (true, false)
    | _ => (true, true)
  left_inv s := by rcases s with ⟨a, b⟩; cases a <;> cases b <;> rfl
  right_inv k := by fin_cases k <;> rfl

def rename : TM2.Stmt (fun _ : Fin 2 => Bool) Label (Bool × Bool) →
    TM2.Stmt (fun _ : Fin 2 => Bool) (Fin 5) (Fin 4)
  | .push k f q => .push k (fun s => f (controlCode.symm s)) (rename q)
  | .peek k f q => .peek k (fun s b => controlCode (f (controlCode.symm s) b)) (rename q)
  | .pop k f q => .pop k (fun s b => controlCode (f (controlCode.symm s) b)) (rename q)
  | .load f q => .load (fun s => controlCode (f (controlCode.symm s))) (rename q)
  | .branch f q₁ q₂ => .branch (fun s => f (controlCode.symm s)) (rename q₁) (rename q₂)
  | .goto f => .goto (fun s => labelCode (f (controlCode.symm s)))
  | .halt => .halt

/-- The same machine in the common finite Boolean-stack interface. -/
def bitMachine : BitMachine.Machine where
  stackCount := 2
  labelCount := 5
  controlCount := 4
  input := 0
  output := 0
  start := labelCode .count
  initial := controlCode (false, false)
  program l := rename (program (labelCode.symm l))

def renameCfg (c : machine.Cfg) : bitMachine.Config :=
  ⟨c.l.map labelCode, controlCode c.var, c.stk⟩

theorem stepAux_rename (q : TM2.Stmt (fun _ : Fin 2 => Bool) Label (Bool × Bool))
    (v : Bool × Bool) (s : Fin 2 → List Bool) :
    TM2.stepAux (rename q) (controlCode v) s = renameCfg (TM2.stepAux q v s) := by
  induction q generalizing v s with
  | push k f q ih => simpa [rename, TM2.stepAux] using ih v (Function.update s k (f v :: s k))
  | peek k f q ih => simpa [rename, TM2.stepAux] using ih (f v (s k).head?) s
  | pop k f q ih =>
      simpa [rename, TM2.stepAux] using ih (f v (s k).head?) (Function.update s k (s k).tail)
  | load f q ih => simpa [rename, TM2.stepAux] using ih (f v) s
  | branch f q₁ q₂ ih₁ ih₂ =>
      cases h : f v <;> simp [rename, TM2.stepAux, h, ih₁, ih₂]
  | goto f =>
      simp only [rename, TM2.stepAux, Equiv.symm_apply_apply, renameCfg]
      rfl
  | halt => rfl

theorem step_rename (c : machine.Cfg) :
    TM2.step bitMachine.program (renameCfg c) = (machine.step c).map renameCfg := by
  cases c with
  | mk l v s =>
      cases l with
      | none => rfl
      | some l =>
          change some (TM2.stepAux (rename (program (labelCode.symm (labelCode l))))
            (controlCode v) s) = (some (TM2.stepAux (program l) v s)).map renameCfg
          simpa only [Equiv.symm_apply_apply, Option.map_some] using
            congrArg some (stepAux_rename (program l) v s)

theorem iterate_none (n : Nat) :
    (fun x : Option machine.Cfg => x.bind machine.step)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact ih

theorem absorbing_run_eq_of_run {n : Nat} {c d : machine.Cfg}
    (h : run n c = some d) : bitMachine.run n (renameCfg c) = renameCfg d := by
  induction n generalizing c with
  | zero =>
      have hc : c = d := by simpa only [run_zero, Option.some.injEq] using h
      cases hc
      rfl
  | succ n ih =>
      cases hs : machine.step c with
      | none =>
          have hh : (fun x : Option machine.Cfg => x.bind machine.step)^[n]
              (machine.step c) = some d := by
            simpa only [run, Function.iterate_succ_apply, Option.bind_some] using h
          rw [hs, iterate_none] at hh
          cases hh
      | some c' =>
          have hr : run n c' = some d := by rwa [run_succ_of_step hs] at h
          rw [BitMachine.Machine.run, Function.iterate_succ_apply]
          have hb : bitMachine.step (renameCfg c) = renameCfg c' := by
            rw [BitMachine.Machine.step, step_rename, hs]
            rfl
          rw [hb]
          exact ih hr

theorem bitMachine_init (input : List Bool) :
    bitMachine.init input = renameCfg (cfg (some .count) (false, false) input []) := by
  rfl

/-- The common runtime interface receives the same explicit machine, with
the actual transition count bounded linearly by its actual input length. -/
theorem bitMachine_outputs (i : Nat) (q : List Bool) :
    bitMachine.OutputsWithin (encodeInput i q) [q[i]?.getD false]
      (2 * (encodeInput i q).length + 3) := by
  refine ⟨exactTime i q, exactTime_le_inputLength i q, ?_, ?_⟩
  all_goals
    rw [bitMachine_init, absorbing_run_eq_of_run (run_correct i q)]
    rfl

end EthInapproximability.CurrentPaper.ProtocolBitLookup
