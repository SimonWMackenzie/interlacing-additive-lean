import EthInapproximability.CurrentPaper.SourceCSPSecondPassInput

/-!
# Physical global-validator lift into the second-pass bank

The validator uses only the left summand.  Its run is simulated step for
step while the initially blank clause-writer bank remains untouched.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPSecondPassGlobalLift

open Turing BitMachineEncoding BitMachineStackEmbedding
open scoped Classical

def globalProgram (a q : Nat) (l : SourceCSPGlobalDecisionProgram.Label a q) :
    TM2.Stmt (fun _ : SourceCSPSecondPassInput.Stack q => Bool)
      (SourceCSPGlobalDecisionProgram.Label a q)
      (SourceCSPGlobalDecisionProgram.Control a q) :=
  stackStmt SourceCSPSecondPassInput.globalEmbedding
    (SourceCSPGlobalDecisionProgram.program a q l)

def blankWriter (q : Nat) :
    SourceClauseRowWriterOperands.Stack q → List Bool := fun _ => []

noncomputable def initial (a q : Nat) (input : List Bool) :
    TM2.Cfg (fun _ : SourceCSPSecondPassInput.Stack q => Bool)
      (SourceCSPGlobalDecisionProgram.Label a q)
      (SourceCSPGlobalDecisionProgram.Control a q) :=
  stackCfg SourceCSPSecondPassInput.globalEmbedding
    (Sum.elim (SourceCSPHeaderRowBridge.initial input) (blankWriter q))
    (SourceCSPGlobalDecisionProgram.initial a q input)

theorem step (a q : Nat)
    (foreign : SourceCSPSecondPassInput.Stack q → List Bool)
    (c : TM2.Cfg (fun _ : SourceCSPGlobalDecisionProgram.Stack q => Bool)
      (SourceCSPGlobalDecisionProgram.Label a q)
      (SourceCSPGlobalDecisionProgram.Control a q)) :
    advance (globalProgram a q)
      (stackCfg SourceCSPSecondPassInput.globalEmbedding foreign c) =
    stackCfg SourceCSPSecondPassInput.globalEmbedding foreign
      (advance (SourceCSPGlobalDecisionProgram.program a q) c) := by
  cases c with
  | mk l v S =>
    cases l with
    | none => rfl
    | some l =>
      simp only [advance, TM2.step, globalProgram, stackCfg,
        Option.getD_some]
      exact stack_stepAux SourceCSPSecondPassInput.globalEmbedding foreign
        (SourceCSPGlobalDecisionProgram.program a q l) v S

theorem run (a q : Nat)
    (foreign : SourceCSPSecondPassInput.Stack q → List Bool)
    (c : TM2.Cfg (fun _ : SourceCSPGlobalDecisionProgram.Stack q => Bool)
      (SourceCSPGlobalDecisionProgram.Label a q)
      (SourceCSPGlobalDecisionProgram.Control a q)) (t : Nat) :
    ((advance (globalProgram a q))^[t])
      (stackCfg SourceCSPSecondPassInput.globalEmbedding foreign c) =
    stackCfg SourceCSPSecondPassInput.globalEmbedding foreign
      (((advance (SourceCSPGlobalDecisionProgram.program a q))^[t]) c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply', ih, step,
        Function.iterate_succ_apply']

theorem initial_left (a q : Nat) (input : List Bool)
    (k : SourceCSPGlobalDecisionProgram.Stack q) :
    (initial a q input).stk (.inl k) =
      (SourceCSPGlobalDecisionProgram.initial a q input).stk k := by
  exact bank_at SourceCSPSecondPassInput.globalEmbedding _ _ k

theorem initial_writer_blank (a q : Nat) (input : List Bool)
    (k : SourceClauseRowWriterOperands.Stack q) :
    (initial a q input).stk (.inr k) = [] := by
  change bank SourceCSPSecondPassInput.globalEmbedding _ _ (.inr k) = []
  rw [bank_outside]
  · rfl
  · rintro ⟨j, hj⟩
    cases hj

theorem run_left (a q : Nat)
    (foreign : SourceCSPSecondPassInput.Stack q → List Bool)
    (c : TM2.Cfg (fun _ : SourceCSPGlobalDecisionProgram.Stack q => Bool)
      (SourceCSPGlobalDecisionProgram.Label a q)
      (SourceCSPGlobalDecisionProgram.Control a q)) (t : Nat)
    (k : SourceCSPGlobalDecisionProgram.Stack q) :
    (((advance (globalProgram a q))^[t])
      (stackCfg SourceCSPSecondPassInput.globalEmbedding foreign c)).stk
        (.inl k) =
    (((advance (SourceCSPGlobalDecisionProgram.program a q))^[t]) c).stk k := by
  rw [run]
  exact bank_at SourceCSPSecondPassInput.globalEmbedding _ _ k

theorem run_writer (a q : Nat)
    (foreign : SourceCSPSecondPassInput.Stack q → List Bool)
    (c : TM2.Cfg (fun _ : SourceCSPGlobalDecisionProgram.Stack q => Bool)
      (SourceCSPGlobalDecisionProgram.Label a q)
      (SourceCSPGlobalDecisionProgram.Control a q)) (t : Nat)
    (k : SourceClauseRowWriterOperands.Stack q) :
    (((advance (globalProgram a q))^[t])
      (stackCfg SourceCSPSecondPassInput.globalEmbedding foreign c)).stk
        (.inr k) = foreign (.inr k) := by
  rw [run]
  exact bank_outside SourceCSPSecondPassInput.globalEmbedding _ _ _
    (by rintro ⟨j, hj⟩; cases hj)

end EthInapproximability.CurrentPaper.SourceCSPSecondPassGlobalLift
