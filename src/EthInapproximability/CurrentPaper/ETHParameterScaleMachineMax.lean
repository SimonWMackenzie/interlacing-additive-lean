import EthInapproximability.CurrentPaper.BitMachineEncoding

/-! A five-stack unary maximum primitive. It restores both supplied words
and clears both scratches; the output is the longer unary word's length. -/

namespace EthInapproximability.CurrentPaper.ETHParameterScaleMachineMax

open Turing Turing.TM2.Stmt BitMachineEncoding

inductive Label where
  | scan | restoreA | restoreB
  deriving DecidableEq, Fintype

abbrev Control := Option Bool × Option Bool
abbrev Config := TM2.Cfg (fun _ : Fin 5 => Bool) Label Control

def program : Label → TM2.Stmt (fun _ : Fin 5 => Bool) Label Control
  | .scan => pop 0 (fun v b => (b,v.2))
      (pop 1 (fun v b => (v.1,b))
        (branch (fun v => v.1.isSome || v.2.isSome)
          (branch (fun v => v.1.isSome)
            (push 2 (fun v => v.1.getD false)
              (branch (fun v => v.2.isSome)
                (push 3 (fun v => v.2.getD false)
                  (push 4 (fun _ => true) (goto (fun _ => .scan))))
                (push 4 (fun _ => true) (goto (fun _ => .scan)))))
            (push 3 (fun v => v.2.getD false)
              (push 4 (fun _ => true) (goto (fun _ => .scan)))))
          (goto (fun _ => .restoreA))))
  | .restoreA => pop 2 (fun v b => (b,v.2))
      (branch (fun v => v.1.isSome)
        (push 0 (fun v => v.1.getD false) (goto (fun _ => .restoreA)))
        (goto (fun _ => .restoreB)))
  | .restoreB => pop 3 (fun v b => (v.1,b))
      (branch (fun v => v.2.isSome)
        (push 1 (fun v => v.2.getD false) (goto (fun _ => .restoreB)))
        halt)

def cfg (l : Option Label) (v : Control)
    (a b scratchA scratchB output : List Bool) : Config :=
  ⟨l,v,![a,b,scratchA,scratchB,output]⟩

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

private theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t+u) c = run u d := by
  simp only [run] at h ⊢
  rw [show t+u=u+t by omega, Function.iterate_add_apply, h]

private theorem step_both (v : Control) (x y : Bool)
    (a b s t out : List Bool) :
    advance program (cfg (some .scan) v (x::a) (y::b) s t out) =
      cfg (some .scan) (some x,some y) a b (x::s) (y::t) (true::out) := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]
  funext k
  fin_cases k <;> rfl

private theorem step_left (v : Control) (x : Bool)
    (a s t out : List Bool) :
    advance program (cfg (some .scan) v (x::a) [] s t out) =
      cfg (some .scan) (some x,none) a [] (x::s) t (true::out) := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]
  funext k
  fin_cases k <;> rfl

private theorem step_right (v : Control) (y : Bool)
    (b s t out : List Bool) :
    advance program (cfg (some .scan) v [] (y::b) s t out) =
      cfg (some .scan) (none,some y) [] b s (y::t) (true::out) := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]
  funext k
  fin_cases k <;> rfl

private theorem step_nil (v : Control) (s t out : List Bool) :
    advance program (cfg (some .scan) v [] [] s t out) =
      cfg (some .restoreA) (none,none) [] [] s t out := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]
  funext k
  fin_cases k <;> rfl

private theorem scan_run (a b s t out : List Bool) (v : Control) :
    run (max a.length b.length + 1) (cfg (some .scan) v a b s t out) =
      cfg (some .restoreA) (none,none) [] []
        (a.reverse ++ s) (b.reverse ++ t)
        (List.replicate (max a.length b.length) true ++ out) := by
  induction a generalizing b s t out v with
  | nil =>
      induction b generalizing t out v with
      | nil => simpa [run] using step_nil v s t out
      | cons y b ih =>
          rw [run, Function.iterate_succ_apply]
          simp only [List.length_nil, Nat.zero_max, List.length_cons]
          rw [step_right]
          simpa [run, List.reverse_cons, List.replicate_succ', List.append_assoc]
            using ih (y::t) (true::out) (none,some y)
  | cons x a ih =>
      cases b with
      | nil =>
          rw [run, Function.iterate_succ_apply]
          simp only [List.length_nil, Nat.max_zero, List.length_cons]
          rw [step_left]
          simpa [run, List.reverse_cons, List.replicate_succ', List.append_assoc]
            using ih [] (x::s) t (true::out) (some x,none)
      | cons y b =>
          rw [run, Function.iterate_succ_apply]
          simp only [List.length_cons, Nat.succ_max_succ]
          rw [step_both]
          simpa [run, List.reverse_cons, List.replicate_succ', List.append_assoc]
            using ih b (x::s) (y::t) (true::out) (some x,some y)

private theorem restoreA_cons (v : Control) (x : Bool)
    (a b s t out : List Bool) :
    advance program (cfg (some .restoreA) v a b (x::s) t out) =
      cfg (some .restoreA) (some x,v.2) (x::a) b s t out := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]
  funext k
  fin_cases k <;> rfl

private theorem restoreA_nil (v : Control) (a b t out : List Bool) :
    advance program (cfg (some .restoreA) v a b [] t out) =
      cfg (some .restoreB) (none,v.2) a b [] t out := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]

private theorem restoreB_cons (v : Control) (y : Bool)
    (a b t out : List Bool) :
    advance program (cfg (some .restoreB) v a b [] (y::t) out) =
      cfg (some .restoreB) (v.1,some y) a (y::b) [] t out := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]
  funext k
  fin_cases k <;> rfl

private theorem restoreB_nil (v : Control) (a b out : List Bool) :
    advance program (cfg (some .restoreB) v a b [] [] out) =
      cfg none (v.1,none) a b [] [] out := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]

private theorem restoreA_run (a b s t out : List Bool) (v : Control) :
    run (s.length+1) (cfg (some .restoreA) v a b s t out) =
      cfg (some .restoreB) (none,v.2) (s.reverse ++ a) b [] t out := by
  induction s generalizing a v with
  | nil => simpa [run] using restoreA_nil v a b t out
  | cons x s ih =>
      rw [run, Function.iterate_succ_apply]
      simp only [List.length_cons]
      rw [restoreA_cons]
      simpa [run, List.reverse_cons, List.append_assoc] using
        ih (x::a) (some x,v.2)

private theorem restoreB_run (a b t out : List Bool) (v : Control) :
    run (t.length+1) (cfg (some .restoreB) v a b [] t out) =
      cfg none (v.1,none) a (t.reverse ++ b) [] [] out := by
  induction t generalizing b v with
  | nil => simpa [run] using restoreB_nil v a b out
  | cons y t ih =>
      rw [run, Function.iterate_succ_apply]
      simp only [List.length_cons]
      rw [restoreB_cons]
      simpa [run, List.reverse_cons, List.append_assoc] using
        ih (y::b) (v.1,some y)

theorem max_run (a b : List Bool) :
    run (max a.length b.length + a.length + b.length + 3)
      (cfg (some .scan) (none,none) a b [] [] []) =
      cfg none (none,none) a b [] []
        (List.replicate (max a.length b.length) true) := by
  have hs := scan_run a b [] [] [] (none,none)
  simp only [List.append_nil] at hs
  have ha := restoreA_run [] [] a.reverse b.reverse
    (List.replicate (max a.length b.length) true) (none,none)
  have hb := restoreB_run a [] b.reverse
    (List.replicate (max a.length b.length) true) (none,none)
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at ha hb
  have hsa := run_add hs (a.length+1)
  rw [ha] at hsa
  have hsab := run_add hsa (b.length+1)
  rw [hb] at hsab
  rw [show max a.length b.length + a.length + b.length + 3 =
    (max a.length b.length + 1 + (a.length+1)) + (b.length+1) by omega]
  exact hsab

/-- The consuming form is used for temporary logarithm words. Original
source fields remain in separate framed banks in the scalar controller. -/
def consumeProgram : Unit → TM2.Stmt (fun _ : Fin 3 => Bool) Unit Control
  | () => pop 0 (fun v b => (b,v.2))
      (pop 1 (fun v b => (v.1,b))
        (branch (fun v => v.1.isSome || v.2.isSome)
          (push 2 (fun _ => true) (goto (fun _ => ())))
          halt))

def consumeCfg (l : Option Unit) (v : Control)
    (a b output : List Bool) : TM2.Cfg (fun _ : Fin 3 => Bool) Unit Control :=
  ⟨l,v,![a,b,output]⟩

def consumeRun (t : ℕ)
    (c : TM2.Cfg (fun _ : Fin 3 => Bool) Unit Control) :=
  ((advance consumeProgram)^[t]) c

private theorem consume_both (v : Control) (x y : Bool)
    (a b out : List Bool) :
    advance consumeProgram (consumeCfg (some ()) v (x::a) (y::b) out) =
      consumeCfg (some ()) (some x,some y) a b (true::out) := by
  simp [advance, consumeProgram, consumeCfg, TM2.step, TM2.stepAux]
  funext k
  fin_cases k <;> rfl

private theorem consume_left (v : Control) (x : Bool)
    (a out : List Bool) :
    advance consumeProgram (consumeCfg (some ()) v (x::a) [] out) =
      consumeCfg (some ()) (some x,none) a [] (true::out) := by
  simp [advance, consumeProgram, consumeCfg, TM2.step, TM2.stepAux]
  funext k
  fin_cases k <;> rfl

private theorem consume_right (v : Control) (y : Bool)
    (b out : List Bool) :
    advance consumeProgram (consumeCfg (some ()) v [] (y::b) out) =
      consumeCfg (some ()) (none,some y) [] b (true::out) := by
  simp [advance, consumeProgram, consumeCfg, TM2.step, TM2.stepAux]
  funext k
  fin_cases k <;> rfl

private theorem consume_nil (v : Control) (out : List Bool) :
    advance consumeProgram (consumeCfg (some ()) v [] [] out) =
      consumeCfg none (none,none) [] [] out := by
  simp [advance, consumeProgram, consumeCfg, TM2.step, TM2.stepAux]
  funext k
  fin_cases k <;> rfl

theorem consume_run (a b out : List Bool) (v : Control) :
    consumeRun (max a.length b.length + 1)
      (consumeCfg (some ()) v a b out) =
      consumeCfg none (none,none) [] []
        (List.replicate (max a.length b.length) true ++ out) := by
  induction a generalizing b out v with
  | nil =>
      induction b generalizing out v with
      | nil => simpa [consumeRun] using consume_nil v out
      | cons y b ih =>
          rw [consumeRun, Function.iterate_succ_apply]
          simp only [List.length_nil, Nat.zero_max, List.length_cons]
          rw [consume_right]
          simpa [consumeRun, List.replicate_succ', List.append_assoc] using
            ih (true::out) (none,some y)
  | cons x a ih =>
      cases b with
      | nil =>
          rw [consumeRun, Function.iterate_succ_apply]
          simp only [List.length_nil, Nat.max_zero, List.length_cons]
          rw [consume_left]
          simpa [consumeRun, List.replicate_succ', List.append_assoc] using
            ih [] (true::out) (some x,none)
      | cons y b =>
          rw [consumeRun, Function.iterate_succ_apply]
          simp only [List.length_cons, Nat.succ_max_succ]
          rw [consume_both]
          simpa [consumeRun, List.replicate_succ', List.append_assoc] using
            ih b (true::out) (some x,some y)

end EthInapproximability.CurrentPaper.ETHParameterScaleMachineMax
