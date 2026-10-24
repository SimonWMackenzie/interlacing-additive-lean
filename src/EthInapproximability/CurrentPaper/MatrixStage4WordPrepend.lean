import EthInapproximability.CurrentPaper.BitMachineCopy

/-!
# Physical serialization of one unary selector word

The fixed controller prepends a delimiter and a unary source word to an
existing serialized stream, preserving the source word. Repeating it in
reverse bin order can form the alignment input; that outer bin loop and its
column-decoder bank linkage remain separate.
-/

namespace EthInapproximability.CurrentPaper.MatrixStage4WordPrepend

open Turing Turing.TM2.Stmt BitMachineEncoding

inductive Label where
  | mark | scan | restore
  deriving DecidableEq, Fintype

abbrev Config := TM2.Cfg (fun _ : Fin 3 => Bool) Label (Option Bool)

def program : Label → TM2.Stmt (fun _ : Fin 3 => Bool) Label (Option Bool)
  | .mark => push 1 (fun _ => false) (goto (fun _ => .scan))
  | .scan => pop 0 (fun _ b => b)
      (branch Option.isSome
        (push 2 (fun _ => true) (goto (fun _ => .scan)))
        (goto (fun _ => .restore)))
  | .restore => pop 2 (fun _ b => b)
      (branch Option.isSome
        (push 0 (fun _ => true)
          (push 1 (fun _ => true) (goto (fun _ => .restore))))
        (load (fun _ => none) halt))

def cfg (l : Option Label) (v : Option Bool)
    (source stream scratch : List Bool) : Config :=
  ⟨l,v,![source,stream,scratch]⟩

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

private theorem run_add {c d : Config} {t : ℕ} (h : run t c=d) (u : ℕ) :
    run (t+u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run,Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem run_succ (c : Config) (t : ℕ) :
    run (t+1) c = run t (advance program c) :=
  Function.iterate_succ_apply _ _ _

theorem mark_step (v : Option Bool) (source stream scratch : List Bool) :
    advance program (cfg (some .mark) v source stream scratch) =
      cfg (some .scan) v source (false::stream) scratch := by
  simp [advance,TM2.step,TM2.stepAux,program,cfg]
  funext k
  fin_cases k <;> rfl

theorem scan_true (v : Option Bool) (source stream scratch : List Bool) :
    advance program (cfg (some .scan) v (true::source) stream scratch) =
      cfg (some .scan) (some true) source stream (true::scratch) := by
  simp [advance,TM2.step,TM2.stepAux,program,cfg]
  funext k
  fin_cases k <;> rfl

theorem scan_nil (v : Option Bool) (stream scratch : List Bool) :
    advance program (cfg (some .scan) v [] stream scratch) =
      cfg (some .restore) none [] stream scratch := by
  simp [advance,TM2.step,TM2.stepAux,program,cfg]

theorem restore_true (v : Option Bool)
    (source stream scratch : List Bool) :
    advance program (cfg (some .restore) v source stream (true::scratch)) =
      cfg (some .restore) (some true)
        (true::source) (true::stream) scratch := by
  simp [advance,TM2.step,TM2.stepAux,program,cfg]
  funext k
  fin_cases k <;> rfl

theorem restore_nil (v : Option Bool) (source stream : List Bool) :
    advance program (cfg (some .restore) v source stream []) =
      cfg none none source stream [] := by
  simp [advance,TM2.step,TM2.stepAux,program,cfg]

private theorem replicate_true_rotate (k : ℕ) (tail : List Bool) :
    List.replicate k true ++ true::tail =
      true::(List.replicate k true ++ tail) := by
  induction k with
  | zero => rfl
  | succ j ih =>
    simpa only [List.replicate_succ,List.cons_append] using
      congrArg (List.cons true) ih

theorem scan_run (k : ℕ) (v : Option Bool)
    (stream scratch : List Bool) :
    run (k+1) (cfg (some .scan) v
      (List.replicate k true) stream scratch) =
      cfg (some .restore) none [] stream
        (List.replicate k true ++ scratch) := by
  induction k generalizing v scratch with
  | zero =>
    simpa only [List.replicate_zero,List.nil_append] using
      run_succ (cfg (some .scan) v [] stream scratch) 0 |>.trans
        (scan_nil v stream scratch)
  | succ k ih =>
    rw [run_succ]
    simp only [List.replicate_succ,scan_true]
    simpa only [replicate_true_rotate] using ih (some true) (true::scratch)

theorem restore_run (k : ℕ) (v : Option Bool)
    (source stream : List Bool) :
    run (k+1) (cfg (some .restore) v source stream
      (List.replicate k true)) =
      cfg none none (List.replicate k true ++ source)
        (List.replicate k true ++ stream) [] := by
  induction k generalizing v source stream with
  | zero =>
    simpa only [List.replicate_zero,List.nil_append] using
      run_succ (cfg (some .restore) v source stream []) 0 |>.trans
        (restore_nil v source stream)
  | succ k ih =>
    rw [run_succ]
    simp only [List.replicate_succ,restore_true]
    simpa only [replicate_true_rotate] using
      ih (some true) (true::source) (true::stream)

theorem prepend_run (p : ℕ) (stream : List Bool) :
    run (1 + (p+1) + (p+1))
      (cfg (some .mark) none (List.replicate p true) stream []) =
      cfg none none (List.replicate p true)
        (List.replicate p true ++ false::stream) [] := by
  have hm : run 1 (cfg (some .mark) none
      (List.replicate p true) stream []) =
      cfg (some .scan) none
        (List.replicate p true) (false::stream) [] := by
    simpa only [run,Function.iterate_one] using
      mark_step none (List.replicate p true) stream []
  calc
    run (1 + (p+1) + (p+1))
        (cfg (some .mark) none (List.replicate p true) stream [])
      = run ((p+1)+(p+1))
          (cfg (some .scan) none
            (List.replicate p true) (false::stream) []) := by
        simpa only [Nat.add_assoc] using run_add hm ((p+1)+(p+1))
    _ = run (p+1) (cfg (some .restore) none []
          (false::stream) (List.replicate p true)) := by
        simpa only [List.append_nil] using
          run_add (scan_run p none (false::stream) []) (p+1)
    _ = _ := by simpa only [List.append_nil] using
      restore_run p none [] (false::stream)

end EthInapproximability.CurrentPaper.MatrixStage4WordPrepend
