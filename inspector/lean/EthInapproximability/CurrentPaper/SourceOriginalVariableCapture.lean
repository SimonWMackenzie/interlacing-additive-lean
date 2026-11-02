import EthInapproximability.CurrentPaper.EncodedCNF
import EthInapproximability.CurrentPaper.BitMachineEncoding
import Mathlib.Tactic

/-!
# Capturing the original source variable count

The first word of a canonical ordered CNF is the unary count of the original
variables. This literal finite-stack pass copies that word to a separate bank
while restoring the complete input. Later source-list stages must transport
this bank through every branch; a sparse branch's own variable count is not a
substitute. The run below charges every pop, push, and terminal test.
-/

namespace EthInapproximability.CurrentPaper.SourceOriginalVariableCapture

open Turing Turing.TM2.Stmt BitMachineEncoding

inductive Label where
  | scan | restore
  deriving DecidableEq, Fintype

abbrev Stack := Fin 3
abbrev Control := Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .scan => pop 0 (fun _ b => b)
      (branch Option.isSome
        (branch (fun v => v.getD false)
          (push 1 (fun _ => true)
            (push 2 (fun _ => true) (goto (fun _ => .scan))))
          (push 1 (fun _ => false) (goto (fun _ => .restore))))
        (goto (fun _ => .restore)))
  | .restore => pop 1 (fun _ b => b)
      (branch Option.isSome
        (push 0 (fun v => v.getD false) (goto (fun _ => .restore)))
        (load (fun _ => none) halt))

def cfg (l : Option Label) (v : Control) (source saved count : List Bool) : Config :=
  ⟨l, v, ![source, saved, count]⟩

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

private theorem run_succ (t : ℕ) (c : Config) :
    run (t+1) c = run t (advance program c) :=
  Function.iterate_succ_apply _ _ _

private theorem run_add (t u : ℕ) (c : Config) :
    run (t+u) c = run u (run t c) := by
  simpa only [run, Nat.add_comm] using
    Function.iterate_add_apply (advance program) u t c

private theorem scan_true (v : Control) (source saved count : List Bool) :
    advance program (cfg (some .scan) v (true :: source) saved count) =
      cfg (some .scan) (some true) source (true :: saved) (true :: count) := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]
  funext i
  fin_cases i <;> rfl

private theorem scan_false (v : Control) (source saved count : List Bool) :
    advance program (cfg (some .scan) v (false :: source) saved count) =
      cfg (some .restore) (some false) source (false :: saved) count := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]
  funext i
  fin_cases i <;> rfl

private theorem restore_cons (v : Control) (b : Bool)
    (source saved count : List Bool) :
    advance program (cfg (some .restore) v source (b :: saved) count) =
      cfg (some .restore) (some b) (b :: source) saved count := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]
  funext i
  fin_cases i <;> rfl

private theorem restore_nil (v : Control) (source count : List Bool) :
    advance program (cfg (some .restore) v source [] count) =
      cfg none none source [] count := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]

private theorem replicate_true_rotate (n : ℕ) (rest : List Bool) :
    List.replicate n true ++ true :: rest =
      true :: List.replicate n true ++ rest := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa [List.replicate_succ, List.append_assoc] using
        (congrArg (List.cons true) ih)

theorem scan_unary (n : ℕ) (v : Control) (tail saved count : List Bool) :
    run (n+1) (cfg (some .scan) v
      (List.replicate n true ++ false :: tail) saved count) =
      cfg (some .restore) (some false) tail
        (false :: List.replicate n true ++ saved)
        (List.replicate n true ++ count) := by
  induction n generalizing v saved count with
  | zero =>
      change run 1 (cfg (some .scan) v (false :: tail) saved count) = _
      rw [run_succ, scan_false]
      rfl
  | succ n ih =>
      simp only [List.replicate_succ, List.cons_append, Nat.succ_add]
      rw [run_succ, scan_true]
      have h := ih (some true) (true :: saved) (true :: count)
      simpa only [List.cons_append, replicate_true_rotate] using h

theorem restore_all (saved source count : List Bool) (v : Control) :
    run (saved.length+1) (cfg (some .restore) v source saved count) =
      cfg none none (saved.reverse ++ source) [] count := by
  induction saved generalizing v source with
  | nil =>
      change run 1 (cfg (some .restore) v source [] count) = _
      rw [run_succ, restore_nil]
      rfl
  | cons b saved ih =>
      rw [List.length_cons, run_succ, restore_cons]
      simpa [List.reverse_cons, List.append_assoc] using
        ih (b :: source) (some b)

theorem capture_run (n : ℕ) (tail : List Bool) :
    run (2*n+3)
      (cfg (some .scan) none (List.replicate n true ++ false :: tail) [] []) =
      cfg none none (List.replicate n true ++ false :: tail) []
        (List.replicate n true) := by
  have hs := scan_unary n none tail [] []
  have hr := restore_all (false :: List.replicate n true) tail
    (List.replicate n true) (some false)
  calc
    run (2*n+3)
        (cfg (some .scan) none (List.replicate n true ++ false :: tail) [] []) =
      run (n+2) (run (n+1)
        (cfg (some .scan) none (List.replicate n true ++ false :: tail) [] [])) := by
          rw [← run_add]
          congr 1
          omega
    _ = cfg none none (List.replicate n true ++ false :: tail) []
        (List.replicate n true) := by
          rw [hs]
          simpa [List.reverse_cons, List.reverse_replicate, List.append_assoc] using hr

noncomputable def machine : BitMachine.Machine :=
  ofFinite (0 : Stack) 2 .scan (none : Control) program

private theorem initial_eq (source : List Bool) :
    rawInit (0 : Stack) .scan (none : Control) source =
      cfg (some .scan) none source [] [] := by
  unfold rawInit cfg
  congr 1
  funext i
  fin_cases i <;> rfl

/-- On every canonical CNF, the output is the original unary variable count;
the complete CNF remains on the input stack of the raw terminal state. -/
theorem canonical_outputs (f : EncodedCNF.Formula) :
    machine.OutputsWithin (EncodedCNF.encode f)
      (List.replicate f.variables true) (2*f.variables+3) := by
  let tail := EncodedCommunication.natField f.clauses.length ++
    EncodedCNF.clauseFields f.clauses
  have he : EncodedCNF.encode f =
      List.replicate f.variables true ++ false :: tail := by
    simp [EncodedCNF.encode, EncodedGraph.unary, tail, List.append_assoc]
  apply outputsWithin_of_raw_run (0 : Stack) 2 .scan (none : Control)
    program (EncodedCNF.encode f) (List.replicate f.variables true)
    (2*f.variables+3) _ le_rfl
  · change (run (2*f.variables+3) _).l = none
    rw [initial_eq, he, capture_run]
    rfl
  · change (run (2*f.variables+3) _).stk 2 = List.replicate f.variables true
    rw [initial_eq, he, capture_run]
    rfl

theorem canonical_raw_run (f : EncodedCNF.Formula) :
    run (2*f.variables+3)
      (rawInit (0 : Stack) .scan (none : Control) (EncodedCNF.encode f)) =
      cfg none none (EncodedCNF.encode f) []
        (List.replicate f.variables true) := by
  let tail := EncodedCommunication.natField f.clauses.length ++
    EncodedCNF.clauseFields f.clauses
  have he : EncodedCNF.encode f =
      List.replicate f.variables true ++ false :: tail := by
    simp [EncodedCNF.encode, EncodedGraph.unary, tail, List.append_assoc]
  rw [initial_eq, he, capture_run]

theorem canonical_machine_run (f : EncodedCNF.Formula) :
    machine.run (2*f.variables+3) (machine.init (EncodedCNF.encode f)) =
      renameCfg (Fintype.equivFin Stack) (Fintype.equivFin Label)
        (Fintype.equivFin Control)
        (cfg none none (EncodedCNF.encode f) []
          (List.replicate f.variables true)) := by
  have hi := ofFinite_init (0 : Stack) 2 .scan (none : Control) program
    (EncodedCNF.encode f)
  have hr := ofFinite_run (0 : Stack) 2 .scan (none : Control) program
    (rawInit (0 : Stack) .scan (none : Control) (EncodedCNF.encode f))
    (2*f.variables+3)
  have h := (congrArg (machine.run (2*f.variables+3)) hi).trans hr
  have hraw := canonical_raw_run f
  unfold run at hraw
  rw [hraw] at h
  exact h

theorem original_n_le_input (f : EncodedCNF.Formula) :
    f.variables ≤ (EncodedCNF.encode f).length := by
  simp only [EncodedCNF.encode, EncodedGraph.unary,
    List.length_append, List.length_replicate, List.length_cons,
    List.length_nil]
  omega

end EthInapproximability.CurrentPaper.SourceOriginalVariableCapture
