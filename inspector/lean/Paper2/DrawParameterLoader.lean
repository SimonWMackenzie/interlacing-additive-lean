import Paper2.CappedLoopCleanup
import EthInapproximability.CurrentPaper.ETHParameterScaleMachineLogCopy
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding
import Mathlib.Tactic

/-! Physical preparation of one capped-draw bank from unary public inputs.
The unary ceiling-logarithm is produced by the existing finite bit machine. -/

namespace Paper2.DrawParameterLoader

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper

noncomputable section

abbrev LogCopyStack := ETHParameterScaleMachineLogCopy.Stack
abbrev Stack := Fin 16 ⊕ LogCopyStack
abbrev LogInner : LogCopyStack :=
  ETHParameterScaleMachineLogCopy.logStack
    ETHParameterScaleMachineLogCopy.logMachine.output
abbrev LogOutput : Stack := .inr LogInner

inductive Label where
  | moveLog | copyB | restoreB | subtractLog | restoreLog
  | copyR | restoreR | predD | copyD | restoreD | restoreFirst | reject
  deriving DecidableEq, Fintype

abbrev Control := Option Bool

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .moveLog =>
      pop LogOutput (fun _ bit => bit)
        (branch Option.isSome
          (push (.inl 1) (fun _ => true) (goto (fun _ => .moveLog)))
          (goto (fun _ => .copyB)))
  | .copyB =>
      pop (.inl 11) (fun _ bit => bit)
        (branch Option.isSome
          (push (.inl 13) (fun _ => true)
            (push (.inl 4) (fun _ => true) (goto (fun _ => .copyB))))
          (goto (fun _ => .restoreB)))
  | .restoreB =>
      pop (.inl 13) (fun _ bit => bit)
        (branch Option.isSome
          (push (.inl 11) (fun _ => true) (goto (fun _ => .restoreB)))
          (goto (fun _ => .subtractLog)))
  | .subtractLog =>
      pop (.inl 1) (fun _ bit => bit)
        (branch Option.isSome
          (pop (.inl 4) (fun _ bit => bit)
            (branch Option.isSome
              (push (.inl 14) (fun _ => true)
                (goto (fun _ => .subtractLog)))
              (goto (fun _ => .reject))))
          (goto (fun _ => .restoreLog)))
  | .restoreLog =>
      pop (.inl 14) (fun _ bit => bit)
        (branch Option.isSome
          (push (.inl 1) (fun _ => true) (goto (fun _ => .restoreLog)))
          (goto (fun _ => .copyR)))
  | .copyR =>
      pop (.inl 12) (fun _ bit => bit)
        (branch Option.isSome
          (push (.inl 13) (fun _ => true)
            (push (.inl 5) (fun _ => true) (goto (fun _ => .copyR))))
          (goto (fun _ => .restoreR)))
  | .restoreR =>
      pop (.inl 13) (fun _ bit => bit)
        (branch Option.isSome
          (push (.inl 12) (fun _ => true) (goto (fun _ => .restoreR)))
          (goto (fun _ => .predD)))
  | .predD =>
      pop (.inl 10) (fun _ bit => bit)
        (branch Option.isSome (goto (fun _ => .copyD))
          (goto (fun _ => .reject)))
  | .copyD =>
      pop (.inl 10) (fun _ bit => bit)
        (branch Option.isSome
          (push (.inl 13) (fun _ => true)
            (push (.inl 8) (fun _ => true) (goto (fun _ => .copyD))))
          (goto (fun _ => .restoreD)))
  | .restoreD =>
      pop (.inl 13) (fun _ bit => bit)
        (branch Option.isSome
          (push (.inl 10) (fun _ => true) (goto (fun _ => .restoreD)))
          (goto (fun _ => .restoreFirst)))
  | .restoreFirst => push (.inl 10) (fun _ => true) halt
  | .reject => halt

def mainBank (tape : List Bool) (n pad r d D B R : Nat)
    (work13 work14 : List Bool) (foreign : LogCopyStack → List Bool) :
    Stack → List Bool
  | .inl i =>
      if i = 0 then tape else
      if i = 1 then List.replicate n true else
      if i = 4 then List.replicate pad true else
      if i = 5 then List.replicate r true else
      if i = 8 then List.replicate d true else
      if i = 10 then List.replicate D true else
      if i = 11 then List.replicate B true else
      if i = 12 then List.replicate R true else
      if i = 13 then work13 else
      if i = 14 then work14 else []
  | .inr k => foreign k

def cfg (l : Option Label) (control : Control)
    (S : Stack → List Bool) : TM2.Cfg (fun _ : Stack => Bool) Label Control :=
  ⟨l, control, S⟩

def run (t : Nat) (c : TM2.Cfg (fun _ : Stack => Bool) Label Control) :=
  ((advance program)^[t]) c

def logEmbed : LogCopyStack ↪ Stack where
  toFun
    | .inl _ => .inl 10
    | .inr k => .inr (.inr k)
  inj' := by
    intro x y h
    cases x with
    | inl x =>
        cases y with
        | inl y => fin_cases x; fin_cases y; rfl
        | inr y => simp at h
    | inr x =>
        cases y with
        | inl y => simp at h
        | inr y =>
            simp only [Sum.inr.injEq] at h
            exact congrArg Sum.inr h

noncomputable def logProgram :
    ETHParameterScaleMachineLogCopy.Label →
      TM2.Stmt (fun _ : Stack => Bool)
        ETHParameterScaleMachineLogCopy.Label
        ETHParameterScaleMachineLogCopy.Control :=
  fun l => BitMachineStackEmbedding.stmt logEmbed id id id none
    (ETHParameterScaleMachineLogCopy.program l)

noncomputable def logRun (t : Nat)
    (c : TM2.Cfg (fun _ : Stack => Bool)
      ETHParameterScaleMachineLogCopy.Label
      ETHParameterScaleMachineLogCopy.Control) :=
  ((advance logProgram)^[t]) c

def initialBank (tape : List Bool) (D B R : Nat) : Stack → List Bool :=
  mainBank tape 0 0 0 0 D B R [] [] (fun _ => [])

noncomputable def logStart (tape : List Bool) (D B R : Nat) :=
  BitMachineStackEmbedding.cfg logEmbed (initialBank tape D B R)
    id id none
    (ETHParameterScaleMachineLogCopy.start (List.replicate D true))

theorem logStart_tape (tape : List Bool) (D B R : Nat) :
    (logStart tape D B R).stk (.inl 0) = tape := by
  change BitMachineStackEmbedding.bank logEmbed (initialBank tape D B R)
    _ (.inl 0) = tape
  rw [BitMachineStackEmbedding.bank_outside]
  · rfl
  · rintro ⟨k, hk⟩
    cases k <;> simp [logEmbed] at hk

theorem logStart_D (tape : List Bool) (D B R : Nat) :
    (logStart tape D B R).stk (.inl 10) = List.replicate D true := by
  change BitMachineStackEmbedding.bank logEmbed (initialBank tape D B R)
    (ETHParameterScaleMachineLogCopy.start (List.replicate D true)).stk
    (logEmbed (.inl 0)) = _
  rw [BitMachineStackEmbedding.bank_at]
  change BitMachineStackEmbedding.bank
    ETHParameterScaleMachineLogCopy.copyStack (fun _ => [])
    (EthInapproximability.CurrentPaper.BitMachineCopy.cfg
      (some .scan) none (List.replicate D true) [] []).stk
    (ETHParameterScaleMachineLogCopy.copyStack (0 : Fin 3)) = _
  rw [BitMachineStackEmbedding.bank_at]
  rfl

theorem logStart_outer_other (tape : List Bool) (D B R : Nat)
    (i : Fin 16) (hi : i ≠ 10) :
    (logStart tape D B R).stk (.inl i) =
      initialBank tape D B R (.inl i) := by
  change BitMachineStackEmbedding.bank logEmbed (initialBank tape D B R)
    _ (.inl i) = _
  apply BitMachineStackEmbedding.bank_outside
  rintro ⟨k,hk⟩
  cases k with
  | inl k => fin_cases k; exact hi (Sum.inl_injective hk.symm)
  | inr k => simp [logEmbed] at hk

noncomputable def afterLogBank (tape : List Bool) (D B R : Nat)
    (c : ETHParameterScaleMachineLogCopy.logMachine.Config) :
    Stack → List Bool :=
  BitMachineStackEmbedding.bank logEmbed (initialBank tape D B R)
    (ETHParameterScaleMachineLogCopy.afterLog (List.replicate D true) c).stk

theorem afterLogBank_other (tape : List Bool) (D B R : Nat)
    (c : ETHParameterScaleMachineLogCopy.logMachine.Config)
    (i : Fin 16) (hi : i ≠ 10) :
    afterLogBank tape D B R c (.inl i) =
      initialBank tape D B R (.inl i) := by
  apply BitMachineStackEmbedding.bank_outside
  rintro ⟨k, hk⟩
  cases k with
  | inl k => fin_cases k; exact hi (Sum.inl_injective hk.symm)
  | inr k => simp [logEmbed] at hk

theorem afterLogBank_D (tape : List Bool) (D B R : Nat)
    (c : ETHParameterScaleMachineLogCopy.logMachine.Config) :
    afterLogBank tape D B R c (.inl 10) = List.replicate D true := by
  change BitMachineStackEmbedding.bank logEmbed _ _ (logEmbed (.inl 0)) = _
  rw [BitMachineStackEmbedding.bank_at]
  exact ETHParameterScaleMachineLogCopy.afterLog_source D c

theorem afterLogBank_log (tape : List Bool) (D B R : Nat)
    (c : ETHParameterScaleMachineLogCopy.logMachine.Config)
    (ho : c.stk ETHParameterScaleMachineLogCopy.logMachine.output =
      List.replicate (Nat.clog 2 D) true) :
    afterLogBank tape D B R c LogOutput =
      List.replicate (Nat.clog 2 D) true := by
  change BitMachineStackEmbedding.bank logEmbed _ _
    (logEmbed (ETHParameterScaleMachineLogCopy.logStack
      ETHParameterScaleMachineLogCopy.logMachine.output)) = _
  rw [BitMachineStackEmbedding.bank_at,
    ETHParameterScaleMachineLogCopy.afterLog_output]
  exact ho

theorem log_produces (tape : List Bool) (D B R : Nat) :
    ∃ t : Nat, ∃ c : ETHParameterScaleMachineLogCopy.logMachine.Config,
      t ≤ 2 * D + 2 +
        (EthInapproximability.CurrentPaper.UnaryBinaryEncoding.coefficient + 6) *
          (D + 1) ^ 2 ∧
      logRun t (logStart tape D B R) =
        ⟨none,
          (ETHParameterScaleMachineLogCopy.afterLog
            (List.replicate D true) c).var,
          afterLogBank tape D B R c⟩ ∧
      c.stk ETHParameterScaleMachineLogCopy.logMachine.output =
        List.replicate (Nat.clog 2 D) true := by
  obtain ⟨t,c,ht,hr,hh,ho⟩ :=
    ETHParameterScaleMachineLogCopy.copied_log_run D
  have hhalt : (((advance ETHParameterScaleMachineLogCopy.program)^[t])
      (ETHParameterScaleMachineLogCopy.start (List.replicate D true))).l = none := by
    change (((ETHParameterScaleMachineLogCopy.run t)
      (ETHParameterScaleMachineLogCopy.start (List.replicate D true))).l = none)
    rw [hr]
    simp [ETHParameterScaleMachineLogCopy.afterLog,
      BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg, hh]
  obtain ⟨u,hu,hrun⟩ := BitMachineStackEmbedding.outputs logEmbed
    (initialBank tape D B R) id id id (by intro v; rfl) none
    ETHParameterScaleMachineLogCopy.program logProgram (by intro l; rfl)
    (ETHParameterScaleMachineLogCopy.start (List.replicate D true)) t hhalt
  refine ⟨u,c,hu.trans ht,?_,ho⟩
  have hr' : (((advance ETHParameterScaleMachineLogCopy.program)^[t])
      (ETHParameterScaleMachineLogCopy.start (List.replicate D true))) =
      ETHParameterScaleMachineLogCopy.afterLog (List.replicate D true) c := hr
  rw [hr'] at hrun
  simpa [logRun, logStart, afterLogBank,
    BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg, hh, ETHParameterScaleMachineLogCopy.afterLog] using hrun

private theorem run_succ {c d : TM2.Cfg (fun _ : Stack => Bool) Label Control}
    (h : TM2.step program c = some d) (n : Nat) :
    run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : TM2.Cfg (fun _ : Stack => Bool) Label Control}
    {m : Nat} (h : run m c = d) (n : Nat) : run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

def withLog (F : LogCopyStack → List Bool) (word : List Bool) :
    LogCopyStack → List Bool := Function.update F LogInner word

private theorem moveLog_true (tape work13 work14 : List Bool)
    (n pad r d D B R : Nat) (F : LogCopyStack → List Bool)
    (tail : List Bool) (hF : F LogInner = true :: tail)
    (control : Control) :
    TM2.step program (cfg (some .moveLog) control
      (mainBank tape n pad r d D B R work13 work14 F)) =
      some (cfg (some .moveLog) (some true)
        (mainBank tape (n+1) pad r d D B R work13 work14 (withLog F tail))) := by
  simp [TM2.step, TM2.stepAux, program, cfg, mainBank, LogOutput, hF,
    withLog]
  funext k
  cases k with
  | inl i => fin_cases i <;> simp [mainBank, List.replicate_succ]
  | inr k =>
      by_cases hk : k = LogInner
      · subst k; simp [mainBank]
      · simp [mainBank, Function.update_of_ne hk]

private theorem moveLog_done (tape work13 work14 : List Bool)
    (n pad r d D B R : Nat) (F : LogCopyStack → List Bool)
    (hF : F LogInner = []) (control : Control) :
    TM2.step program (cfg (some .moveLog) control
      (mainBank tape n pad r d D B R work13 work14 F)) =
      some (cfg (some .copyB) none
        (mainBank tape n pad r d D B R work13 work14 F)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, mainBank, LogOutput, hF]

theorem run_moveLog_prefix (v : Nat) (tape work13 work14 : List Bool)
    (n pad r d D B R : Nat) (F : LogCopyStack → List Bool)
    (control : Control) :
    ∃ next : Control,
      run v (cfg (some .moveLog) control
        (mainBank tape n pad r d D B R work13 work14
          (withLog F (List.replicate v true)))) =
      cfg (some .moveLog) next
        (mainBank tape (n+v) pad r d D B R work13 work14
          (withLog F [])) := by
  induction v generalizing n control with
  | zero => exact ⟨control, by simp [run]⟩
  | succ v ih =>
      obtain ⟨next,h⟩ := ih (n+1) (some true)
      refine ⟨next, ?_⟩
      simp only [List.replicate_succ]
      rw [run_succ (moveLog_true tape work13 work14 n pad r d D B R
        (withLog F (true :: List.replicate v true))
        (List.replicate v true) (by simp [withLog]) control) v]
      simpa [withLog, Function.update_idem, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using h


private theorem copyB_true (tape work13 work14 : List Bool)
    (n pad r d D B R : Nat) (F : LogCopyStack → List Bool)
    (control : Control) :
    TM2.step program (cfg (some .copyB) control
      (mainBank tape n pad r d D (B+1) R work13 work14 F)) =
      some (cfg (some .copyB) (some true)
        (mainBank tape n (pad+1) r d D B R (true :: work13) work14 F)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, mainBank,
    List.replicate_succ]
  funext k
  cases k with
  | inl i => fin_cases i <;> simp [mainBank, List.replicate_succ]
  | inr k => rfl

private theorem copyB_done (tape work13 work14 : List Bool)
    (n pad r d D R : Nat) (F : LogCopyStack → List Bool)
    (control : Control) :
    TM2.step program (cfg (some .copyB) control
      (mainBank tape n pad r d D 0 R work13 work14 F)) =
      some (cfg (some .restoreB) none
        (mainBank tape n pad r d D 0 R work13 work14 F)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, mainBank]

private theorem restoreB_true (tape work13 work14 : List Bool)
    (n pad r d D B R : Nat) (F : LogCopyStack → List Bool)
    (control : Control) :
    TM2.step program (cfg (some .restoreB) control
      (mainBank tape n pad r d D B R (true :: work13) work14 F)) =
      some (cfg (some .restoreB) (some true)
        (mainBank tape n pad r d D (B+1) R work13 work14 F)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, mainBank]
  funext k
  cases k with
  | inl i => fin_cases i <;> simp [mainBank, List.replicate_succ]
  | inr k => rfl

private theorem restoreB_done (tape work14 : List Bool)
    (n pad r d D B R : Nat) (F : LogCopyStack → List Bool)
    (control : Control) :
    TM2.step program (cfg (some .restoreB) control
      (mainBank tape n pad r d D B R [] work14 F)) =
      some (cfg (some .subtractLog) none
        (mainBank tape n pad r d D B R [] work14 F)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, mainBank]

private theorem true_comm (v : Nat) (tail : List Bool) :
    List.replicate v true ++ true :: tail =
      true :: (List.replicate v true ++ tail) := by
  induction v with
  | zero => rfl
  | succ v ih => simp [List.replicate_succ, ih]

theorem run_copyB_prefix (v : Nat) (tape work13 work14 : List Bool)
    (n pad r d D R : Nat) (F : LogCopyStack → List Bool)
    (control : Control) :
    ∃ next : Control,
      run v (cfg (some .copyB) control
        (mainBank tape n pad r d D v R work13 work14 F)) =
      cfg (some .copyB) next
        (mainBank tape n (pad+v) r d D 0 R
          (List.replicate v true ++ work13) work14 F) := by
  induction v generalizing pad work13 control with
  | zero => exact ⟨control, by simp [run]⟩
  | succ v ih =>
      obtain ⟨next,h⟩ := ih (true :: work13) (pad+1) (some true)
      refine ⟨next, ?_⟩
      rw [run_succ (copyB_true tape work13 work14 n pad r d D v R F control) v]
      simpa [List.replicate_succ, true_comm, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using h

theorem run_restoreB_prefix (v : Nat) (tape work13 work14 : List Bool)
    (n pad r d D B R : Nat) (F : LogCopyStack → List Bool)
    (control : Control) :
    ∃ next : Control,
      run v (cfg (some .restoreB) control
        (mainBank tape n pad r d D B R
          (List.replicate v true ++ work13) work14 F)) =
      cfg (some .restoreB) next
        (mainBank tape n pad r d D (B+v) R work13 work14 F) := by
  induction v generalizing B control with
  | zero => exact ⟨control, by simp [run]⟩
  | succ v ih =>
      obtain ⟨next,h⟩ := ih (B+1) (some true)
      refine ⟨next, ?_⟩
      simp only [List.replicate_succ, List.cons_append]
      rw [run_succ (restoreB_true tape
        (List.replicate v true ++ work13) work14 n pad r d D B R F control) v]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

private theorem subtractLog_true (tape work13 work14 : List Bool)
    (n pad r d D B R : Nat) (F : LogCopyStack → List Bool)
    (control : Control) :
    TM2.step program (cfg (some .subtractLog) control
      (mainBank tape (n+1) (pad+1) r d D B R work13 work14 F)) =
      some (cfg (some .subtractLog) (some true)
        (mainBank tape n pad r d D B R work13 (true :: work14) F)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, mainBank,
    List.replicate_succ]
  funext k
  cases k with
  | inl i => fin_cases i <;> simp [mainBank]
  | inr k => rfl

private theorem subtractLog_done (tape work13 work14 : List Bool)
    (pad r d D B R : Nat) (F : LogCopyStack → List Bool)
    (control : Control) :
    TM2.step program (cfg (some .subtractLog) control
      (mainBank tape 0 pad r d D B R work13 work14 F)) =
      some (cfg (some .restoreLog) none
        (mainBank tape 0 pad r d D B R work13 work14 F)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, mainBank]

theorem run_subtractLog_prefix (v : Nat) (tape work13 work14 : List Bool)
    (pad r d D B R : Nat) (F : LogCopyStack → List Bool)
    (control : Control) :
    ∃ next : Control,
      run v (cfg (some .subtractLog) control
        (mainBank tape v (v+pad) r d D B R work13 work14 F)) =
      cfg (some .subtractLog) next
        (mainBank tape 0 pad r d D B R work13
          (List.replicate v true ++ work14) F) := by
  induction v generalizing work14 control with
  | zero => exact ⟨control, by simp [run]⟩
  | succ v ih =>
      obtain ⟨next,h⟩ := ih (true :: work14) (some true)
      refine ⟨next, ?_⟩
      rw [show v + 1 + pad = (v + pad) + 1 by omega,
        run_succ (subtractLog_true tape work13 work14 v (v+pad)
          r d D B R F control) v]
      simpa [List.replicate_succ, true_comm] using h

private theorem restoreLog_true (tape work13 work14 : List Bool)
    (n pad r d D B R : Nat) (F : LogCopyStack → List Bool)
    (control : Control) :
    TM2.step program (cfg (some .restoreLog) control
      (mainBank tape n pad r d D B R work13 (true :: work14) F)) =
      some (cfg (some .restoreLog) (some true)
        (mainBank tape (n+1) pad r d D B R work13 work14 F)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, mainBank]
  funext k
  cases k with
  | inl i => fin_cases i <;> simp [mainBank, List.replicate_succ]
  | inr k => rfl

private theorem restoreLog_done (tape work13 : List Bool)
    (n pad r d D B R : Nat) (F : LogCopyStack → List Bool)
    (control : Control) :
    TM2.step program (cfg (some .restoreLog) control
      (mainBank tape n pad r d D B R work13 [] F)) =
      some (cfg (some .copyR) none
        (mainBank tape n pad r d D B R work13 [] F)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, mainBank]

theorem run_restoreLog_prefix (v : Nat) (tape work13 work14 : List Bool)
    (n pad r d D B R : Nat) (F : LogCopyStack → List Bool)
    (control : Control) :
    ∃ next : Control,
      run v (cfg (some .restoreLog) control
        (mainBank tape n pad r d D B R work13
          (List.replicate v true ++ work14) F)) =
      cfg (some .restoreLog) next
        (mainBank tape (n+v) pad r d D B R work13 work14 F) := by
  induction v generalizing n control with
  | zero => exact ⟨control, by simp [run]⟩
  | succ v ih =>
      obtain ⟨next,h⟩ := ih (n+1) (some true)
      refine ⟨next, ?_⟩
      simp only [List.replicate_succ, List.cons_append]
      rw [run_succ (restoreLog_true tape work13
        (List.replicate v true ++ work14) n pad r d D B R F control) v]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h


private theorem copyR_true (tape work13 work14 : List Bool)
    (n pad r d D B R : Nat) (F : LogCopyStack → List Bool)
    (control : Control) :
    TM2.step program (cfg (some .copyR) control
      (mainBank tape n pad r d D B (R+1) work13 work14 F)) =
      some (cfg (some .copyR) (some true)
        (mainBank tape n pad (r+1) d D B R (true :: work13) work14 F)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, mainBank,
    List.replicate_succ]
  funext k
  cases k with
  | inl i => fin_cases i <;> simp [mainBank, List.replicate_succ]
  | inr k => rfl

private theorem copyR_done (tape work13 work14 : List Bool)
    (n pad r d D B : Nat) (F : LogCopyStack → List Bool)
    (control : Control) :
    TM2.step program (cfg (some .copyR) control
      (mainBank tape n pad r d D B 0 work13 work14 F)) =
      some (cfg (some .restoreR) none
        (mainBank tape n pad r d D B 0 work13 work14 F)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, mainBank]

private theorem restoreR_true (tape work13 work14 : List Bool)
    (n pad r d D B R : Nat) (F : LogCopyStack → List Bool)
    (control : Control) :
    TM2.step program (cfg (some .restoreR) control
      (mainBank tape n pad r d D B R (true :: work13) work14 F)) =
      some (cfg (some .restoreR) (some true)
        (mainBank tape n pad r d D B (R+1) work13 work14 F)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, mainBank]
  funext k
  cases k with
  | inl i => fin_cases i <;> simp [mainBank, List.replicate_succ]
  | inr k => rfl

private theorem restoreR_done (tape work14 : List Bool)
    (n pad r d D B R : Nat) (F : LogCopyStack → List Bool)
    (control : Control) :
    TM2.step program (cfg (some .restoreR) control
      (mainBank tape n pad r d D B R [] work14 F)) =
      some (cfg (some .predD) none
        (mainBank tape n pad r d D B R [] work14 F)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, mainBank]

theorem run_copyR_prefix (v : Nat) (tape work13 work14 : List Bool)
    (n pad r d D B : Nat) (F : LogCopyStack → List Bool)
    (control : Control) :
    ∃ next : Control,
      run v (cfg (some .copyR) control
        (mainBank tape n pad r d D B v work13 work14 F)) =
      cfg (some .copyR) next
        (mainBank tape n pad (r+v) d D B 0
          (List.replicate v true ++ work13) work14 F) := by
  induction v generalizing r work13 control with
  | zero => exact ⟨control, by simp [run]⟩
  | succ v ih =>
      obtain ⟨next,h⟩ := ih (true :: work13) (r+1) (some true)
      refine ⟨next, ?_⟩
      rw [run_succ (copyR_true tape work13 work14 n pad r d D B v F control) v]
      simpa [List.replicate_succ, true_comm, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using h

theorem run_restoreR_prefix (v : Nat) (tape work13 work14 : List Bool)
    (n pad r d D B R : Nat) (F : LogCopyStack → List Bool)
    (control : Control) :
    ∃ next : Control,
      run v (cfg (some .restoreR) control
        (mainBank tape n pad r d D B R
          (List.replicate v true ++ work13) work14 F)) =
      cfg (some .restoreR) next
        (mainBank tape n pad r d D B (R+v) work13 work14 F) := by
  induction v generalizing R control with
  | zero => exact ⟨control, by simp [run]⟩
  | succ v ih =>
      obtain ⟨next,h⟩ := ih (R+1) (some true)
      refine ⟨next, ?_⟩
      simp only [List.replicate_succ, List.cons_append]
      rw [run_succ (restoreR_true tape
        (List.replicate v true ++ work13) work14 n pad r d D B R F control) v]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

private theorem predD_true (tape work13 work14 : List Bool)
    (n pad r d D B R : Nat) (F : LogCopyStack → List Bool)
    (control : Control) :
    TM2.step program (cfg (some .predD) control
      (mainBank tape n pad r d (D+1) B R work13 work14 F)) =
      some (cfg (some .copyD) (some true)
        (mainBank tape n pad r d D B R work13 work14 F)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, mainBank,
    List.replicate_succ]
  funext k
  cases k with
  | inl i => fin_cases i <;> simp [mainBank]
  | inr k => rfl

private theorem copyD_true (tape work13 work14 : List Bool)
    (n pad r d D B R : Nat) (F : LogCopyStack → List Bool)
    (control : Control) :
    TM2.step program (cfg (some .copyD) control
      (mainBank tape n pad r d (D+1) B R work13 work14 F)) =
      some (cfg (some .copyD) (some true)
        (mainBank tape n pad r (d+1) D B R (true :: work13) work14 F)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, mainBank,
    List.replicate_succ]
  funext k
  cases k with
  | inl i => fin_cases i <;> simp [mainBank, List.replicate_succ]
  | inr k => rfl

private theorem copyD_done (tape work13 work14 : List Bool)
    (n pad r d B R : Nat) (F : LogCopyStack → List Bool)
    (control : Control) :
    TM2.step program (cfg (some .copyD) control
      (mainBank tape n pad r d 0 B R work13 work14 F)) =
      some (cfg (some .restoreD) none
        (mainBank tape n pad r d 0 B R work13 work14 F)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, mainBank]

private theorem restoreD_true (tape work13 work14 : List Bool)
    (n pad r d D B R : Nat) (F : LogCopyStack → List Bool)
    (control : Control) :
    TM2.step program (cfg (some .restoreD) control
      (mainBank tape n pad r d D B R (true :: work13) work14 F)) =
      some (cfg (some .restoreD) (some true)
        (mainBank tape n pad r d (D+1) B R work13 work14 F)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, mainBank]
  funext k
  cases k with
  | inl i => fin_cases i <;> simp [mainBank, List.replicate_succ]
  | inr k => rfl

private theorem restoreD_done (tape work14 : List Bool)
    (n pad r d D B R : Nat) (F : LogCopyStack → List Bool)
    (control : Control) :
    TM2.step program (cfg (some .restoreD) control
      (mainBank tape n pad r d D B R [] work14 F)) =
      some (cfg (some .restoreFirst) none
        (mainBank tape n pad r d D B R [] work14 F)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, mainBank]

private theorem restoreFirst_step (tape work14 : List Bool)
    (n pad r d D B R : Nat) (F : LogCopyStack → List Bool)
    (control : Control) :
    TM2.step program (cfg (some .restoreFirst) control
      (mainBank tape n pad r d D B R [] work14 F)) =
      some (cfg none control
        (mainBank tape n pad r d (D+1) B R [] work14 F)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, mainBank]
  funext k
  cases k with
  | inl i => fin_cases i <;> simp [mainBank, List.replicate_succ]
  | inr k => rfl

theorem run_copyD_prefix (v : Nat) (tape work13 work14 : List Bool)
    (n pad r d B R : Nat) (F : LogCopyStack → List Bool)
    (control : Control) :
    ∃ next : Control,
      run v (cfg (some .copyD) control
        (mainBank tape n pad r d v B R work13 work14 F)) =
      cfg (some .copyD) next
        (mainBank tape n pad r (d+v) 0 B R
          (List.replicate v true ++ work13) work14 F) := by
  induction v generalizing d work13 control with
  | zero => exact ⟨control, by simp [run]⟩
  | succ v ih =>
      obtain ⟨next,h⟩ := ih (true :: work13) (d+1) (some true)
      refine ⟨next, ?_⟩
      rw [run_succ (copyD_true tape work13 work14 n pad r d v B R F control) v]
      simpa [List.replicate_succ, true_comm, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using h

theorem run_restoreD_prefix (v : Nat) (tape work13 work14 : List Bool)
    (n pad r d D B R : Nat) (F : LogCopyStack → List Bool)
    (control : Control) :
    ∃ next : Control,
      run v (cfg (some .restoreD) control
        (mainBank tape n pad r d D B R
          (List.replicate v true ++ work13) work14 F)) =
      cfg (some .restoreD) next
        (mainBank tape n pad r d (D+v) B R work13 work14 F) := by
  induction v generalizing D control with
  | zero => exact ⟨control, by simp [run]⟩
  | succ v ih =>
      obtain ⟨next,h⟩ := ih (D+1) (some true)
      refine ⟨next, ?_⟩
      simp only [List.replicate_succ, List.cons_append]
      rw [run_succ (restoreD_true tape
        (List.replicate v true ++ work13) work14 n pad r d D B R F control) v]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem moveLog_stage (b D B R : Nat) (tape : List Bool)
    (F : LogCopyStack → List Bool) :
    run (b + 1) (cfg (some .moveLog) none
      (mainBank tape 0 0 0 0 D B R [] []
        (withLog F (List.replicate b true)))) =
      cfg (some .copyB) none
        (mainBank tape b 0 0 0 D B R [] [] (withLog F [])) := by
  obtain ⟨control,h⟩ := run_moveLog_prefix b tape [] []
    0 0 0 0 D B R F none
  rw [run_add h 1, run_succ
    (moveLog_done tape [] [] (0+b) 0 0 0 D B R
      (withLog F []) (by simp [withLog]) control) 0]
  simp [run]

theorem copyB_stage (b D B R : Nat) (tape : List Bool)
    (F : LogCopyStack → List Bool) :
    run (2 * B + 2) (cfg (some .copyB) none
      (mainBank tape b 0 0 0 D B R [] [] F)) =
      cfg (some .subtractLog) none
        (mainBank tape b B 0 0 D B R [] [] F) := by
  obtain ⟨control,h1⟩ := run_copyB_prefix B tape [] []
    b 0 0 0 D R F none
  have h2 : run (B+1) (cfg (some .copyB) none
      (mainBank tape b 0 0 0 D B R [] [] F)) =
      cfg (some .restoreB) none
        (mainBank tape b B 0 0 D 0 R (List.replicate B true) [] F) := by
    rw [run_add h1 1]
    simp only [zero_add, List.append_nil]
    simpa [run] using run_succ
      (copyB_done tape (List.replicate B true) [] b B 0 0 D R F
        control) 0
  obtain ⟨control2,h3'⟩ := run_restoreB_prefix B tape [] []
    b B 0 0 D 0 R F none
  have h3 : run (B + 1 + B) (cfg (some .copyB) none
      (mainBank tape b 0 0 0 D B R [] [] F)) =
      cfg (some .restoreB) control2
        (mainBank tape b B 0 0 D B R [] [] F) := by
    rw [run_add h2 B]
    simpa using h3'
  rw [show 2 * B + 2 = B + 1 + B + 1 by omega,
    run_add h3 1, run_succ
      (restoreB_done tape [] b B 0 0 D B R F control2) 0]
  rfl

theorem subtractLog_stage (b p D B R : Nat) (tape : List Bool)
    (F : LogCopyStack → List Bool) :
    run (2 * b + 2) (cfg (some .subtractLog) none
      (mainBank tape b (b+p) 0 0 D B R [] [] F)) =
      cfg (some .copyR) none
        (mainBank tape b p 0 0 D B R [] [] F) := by
  obtain ⟨control,h1⟩ := run_subtractLog_prefix b tape [] []
    p 0 0 D B R F none
  have h2 : run (b+1) (cfg (some .subtractLog) none
      (mainBank tape b (b+p) 0 0 D B R [] [] F)) =
      cfg (some .restoreLog) none
        (mainBank tape 0 p 0 0 D B R [] (List.replicate b true) F) := by
    rw [run_add h1 1]
    simp only [List.append_nil]
    simpa [run] using run_succ
      (subtractLog_done tape [] (List.replicate b true)
        p 0 0 D B R F control) 0
  obtain ⟨control2,h3'⟩ := run_restoreLog_prefix b tape [] []
    0 p 0 0 D B R F none
  have h3 : run (b + 1 + b) (cfg (some .subtractLog) none
      (mainBank tape b (b+p) 0 0 D B R [] [] F)) =
      cfg (some .restoreLog) control2
        (mainBank tape b p 0 0 D B R [] [] F) := by
    rw [run_add h2 b]
    simpa using h3'
  rw [show 2 * b + 2 = b + 1 + b + 1 by omega,
    run_add h3 1, run_succ
      (restoreLog_done tape [] b p 0 0 D B R F control2) 0]
  rfl

theorem copyR_stage (b p D B R : Nat) (tape : List Bool)
    (F : LogCopyStack → List Bool) :
    run (2 * R + 2) (cfg (some .copyR) none
      (mainBank tape b p 0 0 D B R [] [] F)) =
      cfg (some .predD) none
        (mainBank tape b p R 0 D B R [] [] F) := by
  obtain ⟨control,h1⟩ := run_copyR_prefix R tape [] []
    b p 0 0 D B F none
  have h2 : run (R+1) (cfg (some .copyR) none
      (mainBank tape b p 0 0 D B R [] [] F)) =
      cfg (some .restoreR) none
        (mainBank tape b p R 0 D B 0 (List.replicate R true) [] F) := by
    rw [run_add h1 1]
    simp only [zero_add, List.append_nil]
    simpa [run] using run_succ
      (copyR_done tape (List.replicate R true) [] b p R 0 D B F control) 0
  obtain ⟨control2,h3'⟩ := run_restoreR_prefix R tape [] []
    b p R 0 D B 0 F none
  have h3 : run (R + 1 + R) (cfg (some .copyR) none
      (mainBank tape b p 0 0 D B R [] [] F)) =
      cfg (some .restoreR) control2
        (mainBank tape b p R 0 D B R [] [] F) := by
    rw [run_add h2 R]
    simpa using h3'
  rw [show 2 * R + 2 = R + 1 + R + 1 by omega,
    run_add h3 1, run_succ
      (restoreR_done tape [] b p R 0 D B R F control2) 0]
  rfl

theorem predecessor_stage (b p B R d : Nat) (tape : List Bool)
    (F : LogCopyStack → List Bool) :
    run (2 * d + 4) (cfg (some .predD) none
      (mainBank tape b p R 0 (d+1) B R [] [] F)) =
      cfg none none
        (mainBank tape b p R d (d+1) B R [] [] F) := by
  have h1 : run 1 (cfg (some .predD) none
      (mainBank tape b p R 0 (d+1) B R [] [] F)) =
      cfg (some .copyD) (some true)
        (mainBank tape b p R 0 d B R [] [] F) := by
    simpa [run] using run_succ
      (predD_true tape [] [] b p R 0 d B R F none) 0
  obtain ⟨control,h2'⟩ := run_copyD_prefix d tape [] []
    b p R 0 B R F (some true)
  have h2 : run (1+d) (cfg (some .predD) none
      (mainBank tape b p R 0 (d+1) B R [] [] F)) =
      cfg (some .copyD) control
        (mainBank tape b p R d 0 B R (List.replicate d true) [] F) := by
    rw [run_add h1 d]
    simpa using h2'
  have h3 : run (1+d+1) (cfg (some .predD) none
      (mainBank tape b p R 0 (d+1) B R [] [] F)) =
      cfg (some .restoreD) none
        (mainBank tape b p R d 0 B R (List.replicate d true) [] F) := by
    rw [run_add h2 1, run_succ
      (copyD_done tape (List.replicate d true) [] b p R d B R F
        control) 0]
    rfl
  obtain ⟨control2,h4'⟩ := run_restoreD_prefix d tape [] []
    b p R d 0 B R F none
  have h4 : run (1+d+1+d) (cfg (some .predD) none
      (mainBank tape b p R 0 (d+1) B R [] [] F)) =
      cfg (some .restoreD) control2
        (mainBank tape b p R d d B R [] [] F) := by
    rw [run_add h3 d]
    simpa using h4'
  have h5 : run (1+d+1+d+1) (cfg (some .predD) none
      (mainBank tape b p R 0 (d+1) B R [] [] F)) =
      cfg (some .restoreFirst) none
        (mainBank tape b p R d d B R [] [] F) := by
    rw [run_add h4 1, run_succ
      (restoreD_done tape [] b p R d d B R F control2) 0]
    rfl
  rw [show 2 * d + 4 = 1+d+1+d+1+1 by omega,
    run_add h5 1, run_succ
      (restoreFirst_step tape [] b p R d d B R F none) 0]
  rfl

theorem staging_run (b p d R : Nat) (tape : List Bool)
    (F : LogCopyStack → List Bool) :
    run (3*b + 2*(b+p) + 2*R + 2*d + 11)
      (cfg (some .moveLog) none
        (mainBank tape 0 0 0 0 (d+1) (b+p) R [] []
          (withLog F (List.replicate b true)))) =
      cfg none none
        (mainBank tape b p R d (d+1) (b+p) R [] [] (withLog F [])) := by
  let t1 := b + 1
  let t2 := 2 * (b+p) + 2
  let t3 := 2 * b + 2
  let t4 := 2 * R + 2
  let t5 := 2 * d + 4
  have htime : 3*b + 2*(b+p) + 2*R + 2*d + 11 =
      t1 + (t2 + (t3 + (t4 + t5))) := by
    dsimp [t1,t2,t3,t4,t5]; omega
  rw [htime]
  calc
    run (t1 + (t2 + (t3 + (t4 + t5))))
        (cfg (some .moveLog) none
          (mainBank tape 0 0 0 0 (d+1) (b+p) R [] []
            (withLog F (List.replicate b true)))) =
      run (t2 + (t3 + (t4 + t5)))
        (cfg (some .copyB) none
          (mainBank tape b 0 0 0 (d+1) (b+p) R [] [] (withLog F []))) := by
            exact run_add (moveLog_stage b (d+1) (b+p) R tape F) _
    _ = run (t3 + (t4 + t5))
        (cfg (some .subtractLog) none
          (mainBank tape b (b+p) 0 0 (d+1) (b+p) R [] [] (withLog F []))) := by
            exact run_add (copyB_stage b (d+1) (b+p) R tape (withLog F [])) _
    _ = run (t4 + t5)
        (cfg (some .copyR) none
          (mainBank tape b p 0 0 (d+1) (b+p) R [] [] (withLog F []))) := by
            exact run_add (subtractLog_stage b p (d+1) (b+p) R tape
              (withLog F [])) _
    _ = run t5
        (cfg (some .predD) none
          (mainBank tape b p R 0 (d+1) (b+p) R [] [] (withLog F []))) := by
            exact run_add (copyR_stage b p (d+1) (b+p) R tape (withLog F [])) _
    _ = cfg none none
        (mainBank tape b p R d (d+1) (b+p) R [] [] (withLog F [])) := by
            exact predecessor_stage b p (b+p) R d tape (withLog F [])

theorem withLog_self (F : LogCopyStack → List Bool) (word : List Bool)
    (h : F LogInner = word) : withLog F word = F := by
  funext k
  by_cases hk : k = LogInner
  · subst k; simp [withLog, h]
  · simp [withLog, Function.update_of_ne hk]

theorem postprocess_from_log (D B R : Nat) (hD : 0 < D)
    (hB : Nat.clog 2 D ≤ B) (tape : List Bool)
    (F : LogCopyStack → List Bool)
    (hlog : F LogInner = List.replicate (Nat.clog 2 D) true) :
    ∃ t ≤ 3 * Nat.clog 2 D + 2 * B + 2 * R + 2 * (D-1) + 11,
      run t (cfg (some .moveLog) none
        (mainBank tape 0 0 0 0 D B R [] [] F)) =
      cfg none none
        (mainBank tape (Nat.clog 2 D) (B - Nat.clog 2 D)
          R (D-1) D B R [] [] (withLog F [])) := by
  let b := Nat.clog 2 D
  let p := B - b
  let d := D - 1
  have hD' : D = d + 1 := by dsimp [d]; omega
  have hB' : B = b + p := by dsimp [b,p]; omega
  have hs := staging_run b p d R tape F
  rw [← hD', ← hB'] at hs
  rw [withLog_self F (List.replicate b true) (by simpa [b] using hlog)] at hs
  refine ⟨3*b + 2*B + 2*R + 2*d + 11, ?_, ?_⟩
  · simp [b,d]
  · simpa [b,p,d] using hs

theorem afterLogBank_as_main (tape : List Bool) (D B R : Nat)
    (c : ETHParameterScaleMachineLogCopy.logMachine.Config) :
    afterLogBank tape D B R c =
      mainBank tape 0 0 0 0 D B R [] []
        (fun k => afterLogBank tape D B R c (.inr k)) := by
  funext k
  cases k with
  | inl i =>
      by_cases hi : i = 10
      · subst i
        rw [afterLogBank_D]
        rfl
      · rw [afterLogBank_other tape D B R c i hi]
        rfl
  | inr k => rfl

theorem postprocess_afterLog (tape : List Bool) (D B R : Nat)
    (hD : 0 < D) (hB : Nat.clog 2 D ≤ B)
    (c : ETHParameterScaleMachineLogCopy.logMachine.Config)
    (ho : c.stk ETHParameterScaleMachineLogCopy.logMachine.output =
      List.replicate (Nat.clog 2 D) true) :
    ∃ t ≤ 3 * Nat.clog 2 D + 2 * B + 2 * R + 2 * (D-1) + 11,
      run t (cfg (some .moveLog) none (afterLogBank tape D B R c)) =
      cfg none none
        (mainBank tape (Nat.clog 2 D) (B - Nat.clog 2 D)
          R (D-1) D B R [] []
          (withLog (fun k => afterLogBank tape D B R c (.inr k)) [])) := by
  have hlog : (fun k => afterLogBank tape D B R c (.inr k)) LogInner =
      List.replicate (Nat.clog 2 D) true := by
    exact afterLogBank_log tape D B R c ho
  obtain ⟨t,ht,hr⟩ := postprocess_from_log D B R hD hB tape
    (fun k => afterLogBank tape D B R c (.inr k)) hlog
  refine ⟨t,ht,?_⟩
  rw [afterLogBank_as_main]
  exact hr

abbrev FullLabel := EthInapproximability.CurrentPaper.BitMachineRawSequence.Label
  ETHParameterScaleMachineLogCopy.Label Label
abbrev FullControl := EthInapproximability.CurrentPaper.BitMachineRawSequence.Control
  ETHParameterScaleMachineLogCopy.Control Control

noncomputable def fullProgram :
    FullLabel → TM2.Stmt (fun _ : Stack => Bool) FullLabel FullControl :=
  EthInapproximability.CurrentPaper.BitMachineRawSequence.program
    logProgram program .moveLog (ETHParameterScaleMachineLogCopy.copyControl none) none

noncomputable def fullStart (tape : List Bool) (D B R : Nat) :
    TM2.Cfg (fun _ : Stack => Bool) FullLabel FullControl :=
  ⟨some (EthInapproximability.CurrentPaper.BitMachineRawSequence.leftLabel
      (Sum.inl EthInapproximability.CurrentPaper.BitMachineCopy.Label.scan)),
    (ETHParameterScaleMachineLogCopy.copyControl none, none),
    (logStart tape D B R).stk⟩

noncomputable def fullRun (t : Nat)
    (c : TM2.Cfg (fun _ : Stack => Bool) FullLabel FullControl) :=
  ((advance fullProgram)^[t]) c

/-- From only unary public `D,B,R` and the tape, a single fixed program
produces every scalar bank required by the already-checked capped draw.
The nested logarithm-machine work bank is disjoint from the ten ready slots. -/
theorem full_loader (tape : List Bool) (D B R : Nat)
    (hD : 0 < D) (hB : Nat.clog 2 D ≤ B) :
    ∃ t : Nat, ∃ c : ETHParameterScaleMachineLogCopy.logMachine.Config,
      t ≤
      (2 * D + 2 +
        (EthInapproximability.CurrentPaper.UnaryBinaryEncoding.coefficient + 6) *
          (D + 1) ^ 2) +
      (3 * Nat.clog 2 D + 2 * B + 2 * R + 2 * (D-1) + 11) + 1 ∧
      fullRun t (fullStart tape D B R) =
        ⟨none, (ETHParameterScaleMachineLogCopy.copyControl none, none),
          mainBank tape (Nat.clog 2 D) (B - Nat.clog 2 D)
            R (D-1) D B R [] []
            (withLog
              (fun k => afterLogBank tape D B R c (.inr k)) [])⟩ := by
  obtain ⟨ta,c,hta,hra,ho⟩ := log_produces tape D B R
  obtain ⟨tb,htb,hrb⟩ := postprocess_afterLog tape D B R hD hB c ho
  let S := (logStart tape D B R).stk
  let T := afterLogBank tape D B R c
  let U := mainBank tape (Nat.clog 2 D) (B - Nat.clog 2 D)
    R (D-1) D B R [] []
    (withLog (fun k => T (.inr k)) [])
  have hstart : logStart tape D B R =
      ⟨some (Sum.inl EthInapproximability.CurrentPaper.BitMachineCopy.Label.scan),
        ETHParameterScaleMachineLogCopy.copyControl none, S⟩ := by
    rfl
  have ha : (((advance logProgram)^[ta])
      (⟨some (Sum.inl EthInapproximability.CurrentPaper.BitMachineCopy.Label.scan),
        ETHParameterScaleMachineLogCopy.copyControl none, S⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            ETHParameterScaleMachineLogCopy.Label
            ETHParameterScaleMachineLogCopy.Control)) =
      ⟨none,
        (ETHParameterScaleMachineLogCopy.afterLog
          (List.replicate D true) c).var, T⟩ := by
    have ha' := hra
    rw [hstart] at ha'
    exact ha'
  have hb : (((advance program)^[tb])
      (⟨some Label.moveLog, none, T⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Label Control)) =
      ⟨none, none, U⟩ := by
    simpa [run, cfg, T, U] using hrb
  obtain ⟨t,ht,hr⟩ :=
    EthInapproximability.CurrentPaper.BitMachineRawSequence.runs
      logProgram program
      (Sum.inl EthInapproximability.CurrentPaper.BitMachineCopy.Label.scan)
      Label.moveLog
      (ETHParameterScaleMachineLogCopy.copyControl none)
      (ETHParameterScaleMachineLogCopy.afterLog
        (List.replicate D true) c).var
      none none S T U ta tb ha hb
  refine ⟨t,c,?_,?_⟩
  · omega
  · simpa [fullRun, fullStart, fullProgram, S, U, T] using hr

def readySlot (i : Fin 10) : Stack :=
  .inl ⟨i.val, Nat.lt_trans i.isLt (by decide : 10 < 16)⟩

theorem fullStart_saved (tape : List Bool) (D B R : Nat) :
    (fullStart tape D B R).stk (.inl 0) = tape ∧
    (fullStart tape D B R).stk (.inl 10) = List.replicate D true ∧
    (fullStart tape D B R).stk (.inl 11) = List.replicate B true ∧
    (fullStart tape D B R).stk (.inl 12) = List.replicate R true := by
  refine ⟨logStart_tape tape D B R, logStart_D tape D B R, ?_, ?_⟩
  · change (logStart tape D B R).stk (.inl 11) = _
    rw [logStart_outer_other tape D B R 11 (by decide)]
    rfl
  · change (logStart tape D B R).stk (.inl 12) = _
    rw [logStart_outer_other tape D B R 12 (by decide)]
    rfl

theorem fullStart_ready_empty (tape : List Bool) (D B R : Nat) :
    (fun i : Fin 10 => (fullStart tape D B R).stk (readySlot i)) =
      Paper2.CappedLoop.WideProjection.bank tape [] [] [] [] [] [] [] [] [] := by
  funext i
  fin_cases i
  · exact logStart_tape tape D B R
  all_goals
    change (logStart tape D B R).stk (.inl _) = _
    rw [logStart_outer_other tape D B R _ (by decide)]
    rfl

/-- The final ten-bank projection is literally the initial bank expected by
`CappedLoop.Cleanup.source_draw_ready`, with no derived scalar supplied. -/
theorem ready_projection (tape : List Bool) (D B R : Nat)
    (F : LogCopyStack → List Bool) :
    (fun i : Fin 10 =>
      mainBank tape (Nat.clog 2 D) (B - Nat.clog 2 D)
        R (D-1) D B R [] [] F (readySlot i)) =
      Paper2.CappedLoop.WideProjection.bank tape
        (List.replicate (Nat.clog 2 D) true) [] []
        (List.replicate (B - Nat.clog 2 D) true)
        (List.replicate R true) [] []
        (List.replicate (D-1) true) [] := by
  funext i
  fin_cases i <;> rfl

theorem loader_bound_polynomial (D B R : Nat) :
    (2 * D + 2 +
      (EthInapproximability.CurrentPaper.UnaryBinaryEncoding.coefficient + 6) *
        (D + 1) ^ 2) +
      (3 * Nat.clog 2 D + 2 * B + 2 * R + 2 * (D-1) + 11) + 1 ≤
      (EthInapproximability.CurrentPaper.UnaryBinaryEncoding.coefficient + 26) *
        (D + B + R + 2) ^ 2 := by
  let b := Nat.clog 2 D
  let N := D + B + R + 2
  let U := EthInapproximability.CurrentPaper.UnaryBinaryEncoding.coefficient + 6
  have hb : b ≤ D := by
    dsimp [b]
    rw [EthInapproximability.CurrentPaper.ExactParameterMachineLog.clog_eq_pred_bits_length]
    exact (EthInapproximability.CurrentPaper.UnaryBinaryEncoding.bits_length_le _).trans
      (Nat.sub_le D 1)
  have hDN : D + 1 ≤ N := by dsimp [N]; omega
  have hsq : (D + 1)^2 ≤ N^2 := Nat.pow_le_pow_left hDN 2
  have hU : U * (D + 1)^2 ≤ U * N^2 := Nat.mul_le_mul_left U hsq
  have hN : N ≤ N^2 := by dsimp [N]; nlinarith
  have hlin : 2*D+2 + 3*b + 2*B + 2*R + 2*(D-1) + 12 ≤ 20*N := by
    dsimp [N]; omega
  have h20 := Nat.mul_le_mul_left 20 hN
  calc
    (2 * D + 2 + U * (D + 1)^2) +
        (3*b + 2*B + 2*R + 2*(D-1) + 11) + 1 ≤
        U*N^2 + 20*N := by omega
    _ ≤ U*N^2 + 20*N^2 := Nat.add_le_add_left h20 _
    _ = (U+20)*N^2 := by ring

#print axioms log_produces
#print axioms postprocess_from_log
#print axioms staging_run
#print axioms full_loader
#print axioms fullStart_saved
#print axioms fullStart_ready_empty
#print axioms ready_projection
#print axioms loader_bound_polynomial

end
end Paper2.DrawParameterLoader
