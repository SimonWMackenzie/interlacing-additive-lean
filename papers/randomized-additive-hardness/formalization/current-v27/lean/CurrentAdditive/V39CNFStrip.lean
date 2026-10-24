import EthInapproximability.CurrentPaper.EncodedCNF
import EthInapproximability.CurrentPaper.EncodedComplexity
import EthInapproximability.CurrentPaper.BitMachineEncoding
import EthInapproximability.CurrentPaper.BitMachineSubroutine

/-! Physical deletion of two headers inside the original outer field.
Every test reads literal Boolean cells; binary counts are skipped without
converting them to unbounded finite control. Syntax validation is separate. -/
namespace CurrentAdditive.V39CNFStrip

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EthInapproximability.CurrentPaper
open Turing TM2.Stmt BitMachineEncoding EncodedCommunication

inductive Label where | unary | binary
  deriving DecidableEq, Fintype

def failure : TM2.Stmt (fun _ : Fin 1 => Bool) Label (Option Bool) :=
  push 0 (fun _ => false) halt
def tagged (next : TM2.Stmt (fun _ : Fin 1 => Bool) Label (Option Bool)) :
    TM2.Stmt (fun _ : Fin 1 => Bool) Label (Option Bool) :=
  pop 0 (fun _ b => b) (branch (fun b => b.getD false) next failure)
def payload (next : TM2.Stmt (fun _ : Fin 1 => Bool) Label (Option Bool)) :
    TM2.Stmt (fun _ : Fin 1 => Bool) Label (Option Bool) :=
  pop 0 (fun _ b => b) (branch Option.isSome next failure)
def program : Label → TM2.Stmt (fun _ : Fin 1 => Bool) Label (Option Bool)
  | .unary => tagged (payload (branch (fun b => b.getD false)
      (goto (fun _ => .unary)) (goto (fun _ => .binary))))
  | .binary => tagged (payload (branch (fun b => b.getD false)
      (tagged (payload (goto (fun _ => .binary))))
      (push 0 (fun _ => true) halt)))

noncomputable def machine : BitMachine.Machine :=
  ofFinite (0 : Fin 1) 0 .unary (none : Option Bool) program
def cfg (l : Option Label) (v : Option Bool) (code : List Bool) :
    TM2.Cfg (fun _ : Fin 1 => Bool) Label (Option Bool) := ⟨l, v, fun _ => code⟩
def run (t : ℕ) (c : TM2.Cfg (fun _ : Fin 1 => Bool) Label (Option Bool)) :=
  ((advance program)^[t]) c

theorem unary_step (v : Option Bool) (b : Bool) (code : List Bool) :
    advance program (cfg (some .unary) v (true :: b :: code)) =
      cfg (some (if b then .unary else .binary)) (some b) code := by
  cases b <;> simp [advance, cfg, program, tagged, payload, TM2.step, TM2.stepAux]
  all_goals funext k; fin_cases k; rfl

theorem binary_step (v : Option Bool) (b : Bool) (code : List Bool) :
    advance program (cfg (some .binary) v (true :: true :: true :: b :: code)) =
      cfg (some .binary) (some b) code := by
  simp [advance, cfg, program, tagged, payload, TM2.step, TM2.stepAux]
  funext k
  fin_cases k
  rfl

theorem binary_end (v : Option Bool) (code : List Bool) :
    advance program (cfg (some .binary) v (true :: false :: code)) =
      cfg none (some false) (true :: code) := by
  simp [advance, cfg, program, tagged, payload, TM2.step, TM2.stepAux]
  funext k
  fin_cases k
  rfl

theorem halts (code : List Bool) (l : Label) (v : Option Bool) :
    ∃ t ≤ code.length + 1, (run t (cfg (some l) v code)).l = none := by
  induction hn : code.length using Nat.strong_induction_on generalizing code l v with
  | h n ih =>
    cases code with
    | nil => exact ⟨1, by simp, by cases l <;> rfl⟩
    | cons a code =>
      cases a with
      | false => exact ⟨1, by simp, by cases l <;> rfl⟩
      | true =>
        cases code with
        | nil => exact ⟨1, by simp, by cases l <;> rfl⟩
        | cons b code =>
          cases l with
          | unary =>
            obtain ⟨t, ht, hh⟩ := ih code.length (by simp at hn; omega) code
              (if b then .unary else .binary) (some b) rfl
            refine ⟨t + 1, by simp at hn ⊢; omega, ?_⟩
            rw [run, Function.iterate_succ_apply, unary_step]
            exact hh
          | binary =>
            cases b with
            | false => exact ⟨1, by simp, by rw [run, Function.iterate_one, binary_end]; rfl⟩
            | true =>
              cases code with
              | nil => exact ⟨1, by simp, rfl⟩
              | cons c code =>
                cases c with
                | false => exact ⟨1, by simp, rfl⟩
                | true =>
                  cases code with
                  | nil => exact ⟨1, by simp, rfl⟩
                  | cons b code =>
                    obtain ⟨t, ht, hh⟩ := ih code.length (by simp at hn; omega) code
                      .binary (some b) rfl
                    refine ⟨t + 1, by simp at hn ⊢; omega, ?_⟩
                    rw [run, Function.iterate_succ_apply, binary_step]
                    exact hh

def result (code : List Bool) : List Bool :=
  (run (code.length + 1) (cfg (some .unary) none code)).stk 0

theorem rawInit_eq (code : List Bool) :
    rawInit (0 : Fin 1) .unary (none : Option Bool) code = cfg (some .unary) none code := by
  unfold rawInit cfg
  congr 1
  funext k
  fin_cases k
  rfl

theorem outputs (code : List Bool) :
    machine.OutputsWithin code (result code) (code.length + 1) := by
  obtain ⟨t, ht, hh⟩ := halts code .unary none
  have hb : (run (code.length + 1) (cfg (some .unary) none code)).l = none := by
    rw [show code.length + 1 = (code.length + 1 - t) + t by omega,
      run, Function.iterate_add_apply]
    change (((advance program)^[code.length + 1 - t]) (run t (cfg (some .unary) none code))).l = none
    rw [BitMachineSubroutine.run_halted program _ hh]
    exact hh
  apply outputsWithin_of_raw_run (0 : Fin 1) 0 .unary (none : Option Bool) program
    code (result code) (code.length + 1) _ le_rfl
  · rw [rawInit_eq]; exact hb
  · rw [rawInit_eq]; rfl

theorem polytime : BitMachine.Polytime result :=
  ⟨machine, 1, 1, by simpa using outputs⟩

theorem binary_fields (bs tail assignment : List Bool) (v : Option Bool) :
    ∃ w, run (bs.length + 1)
      (cfg (some .binary) v (field (field bs ++ tail) ++ assignment)) =
      cfg none w (true :: (field tail ++ assignment)) := by
  induction bs generalizing v with
  | nil => exact ⟨some false, by simpa [field, run] using binary_end v (field tail ++ assignment)⟩
  | cons b bs ih =>
    obtain ⟨w, hw⟩ := ih (some b)
    refine ⟨w, ?_⟩
    simp only [field, List.cons_append, List.length_cons]
    rw [run, Function.iterate_succ_apply, binary_step]
    exact hw

theorem unary_fields (n : ℕ) (tail assignment : List Bool) (v : Option Bool) :
    run (n + 1) (cfg (some .unary) v
      (field (EncodedGraph.unary n ++ tail) ++ assignment)) =
      cfg (some .binary) (some false) (field tail ++ assignment) := by
  induction n generalizing v with
  | zero => simpa [EncodedGraph.unary, field, run] using unary_step v false (field tail ++ assignment)
  | succ n ih =>
    simp only [EncodedGraph.unary, List.replicate_succ, List.cons_append, field]
    rw [run, Function.iterate_succ_apply, unary_step]
    exact ih (some true)

theorem result_pair_formula (f : EncodedCNF.Formula) (assignment : List Bool) :
    result (EncodedComplexity.pair (EncodedCNF.encode f) assignment) =
      true :: EncodedComplexity.pair (EncodedCNF.clauseFields f.clauses) assignment := by
  let code := EncodedComplexity.pair (EncodedCNF.encode f) assignment
  obtain ⟨w, hb⟩ := binary_fields f.clauses.length.bits
    (EncodedCNF.clauseFields f.clauses) assignment (some false)
  have hr : run (f.variables + 1 + (f.clauses.length.bits.length + 1))
      (cfg (some .unary) none code) =
      cfg none w (true :: EncodedComplexity.pair (EncodedCNF.clauseFields f.clauses) assignment) := by
    rw [run, Nat.add_comm, Function.iterate_add_apply]
    change run (f.clauses.length.bits.length + 1) (run (f.variables + 1) _) = _
    unfold code EncodedComplexity.pair EncodedCNF.encode
    rw [List.append_assoc, unary_fields]
    exact hb
  have hn : f.variables + 1 + (f.clauses.length.bits.length + 1) ≤ code.length + 1 := by
    simp only [code, EncodedComplexity.pair, EncodedCNF.encode, field_length,
      List.length_append, EncodedGraph.unary, List.length_replicate, List.length_singleton,
      natField] at *
    omega
  unfold result
  change (run (code.length + 1) (cfg (some .unary) none code)).stk 0 = _
  rw [show code.length + 1 = (code.length + 1 -
    (f.variables + 1 + (f.clauses.length.bits.length + 1))) +
    (f.variables + 1 + (f.clauses.length.bits.length + 1)) by omega,
    run, Function.iterate_add_apply]
  simp only [run] at hr
  rw [hr]
  rw [BitMachineSubroutine.run_halted program _ rfl]
  rfl

theorem result_false : result [false] = [false] := by
  rfl

end CurrentAdditive.V39CNFStrip
