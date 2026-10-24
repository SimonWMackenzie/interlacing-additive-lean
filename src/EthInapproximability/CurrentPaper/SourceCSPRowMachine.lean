import EthInapproximability.CurrentPaper.SourceCSPCodec
import EthInapproximability.CurrentPaper.ProtocolBinaryHeader

/-!
# Literal truth-table blocks in the PCP constraint parser

Source: frozen v8 `06-eth.tex`, `thm:paper-sparse-gap-source`, concrete
Boolean-source construction. The table size is a fixed program parameter,
stored in finite labels. Each table bit is read by an actual stack pop;
no unit-cost block access is used. This module is a row-parser component,
not a completed CSP parser or a full source-construction runtime theorem.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPRowMachine

open Turing TM2.Stmt BitMachineEncoding

inductive Label (H : ℕ) where
  | read : Fin (H + 1) → Label H
  | restore
  deriving DecidableEq, Fintype

abbrev Control := Option Bool

def program (H : ℕ) : Label H → TM2.Stmt (fun _ : Fin 3 => Bool) (Label H) Control
  | .read i =>
      if h : i.val < H then
        pop 0 (fun _ b => b)
          (branch Option.isSome
            (push 1 (fun b => b.getD false)
              (goto (fun _ => .read ⟨i.val + 1, by omega⟩)))
            (push 2 (fun _ => false) halt))
      else goto (fun _ => .restore)
  | .restore =>
      pop 1 (fun _ b => b)
        (branch Option.isSome
          (push 2 (fun b => b.getD false) (goto (fun _ => .restore)))
          (push 2 (fun _ => true) halt))

def contents (source saved output : List Bool) : Fin 3 → List Bool :=
  fun k => if k = 0 then source else if k = 1 then saved else output

def cfg {H : ℕ} (l : Option (Label H)) (v : Control)
    (source saved output : List Bool) : TM2.Cfg (fun _ : Fin 3 => Bool) (Label H) Control :=
  ⟨l, v, contents source saved output⟩

def run {H : ℕ} (t : ℕ) (c : TM2.Cfg (fun _ : Fin 3 => Bool) (Label H) Control) :=
  ((advance (program H))^[t]) c

theorem run_succ {H : ℕ} (t : ℕ)
    (c : TM2.Cfg (fun _ : Fin 3 => Bool) (Label H) Control) :
    run (t + 1) c = run t (advance (program H) c) :=
  Function.iterate_succ_apply _ _ _

theorem run_add {H : ℕ} (t u : ℕ)
    (c : TM2.Cfg (fun _ : Fin 3 => Bool) (Label H) Control) :
    run (t + u) c = run u (run t c) := by
  simpa only [run, Nat.add_comm] using Function.iterate_add_apply (advance (program H)) u t c

theorem read_cons {H : ℕ} (i : Fin (H + 1)) (hi : i.val < H) (v : Control)
    (b : Bool) (source saved output : List Bool) :
    advance (program H) (cfg (some (.read i)) v (b :: source) saved output) =
      cfg (some (.read ⟨i.val + 1, by omega⟩)) (some b) source (b :: saved) output := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, contents, hi]
  funext k
  fin_cases k <;> rfl

theorem read_nil {H : ℕ} (i : Fin (H + 1)) (hi : i.val < H) (v : Control)
    (saved output : List Bool) :
    advance (program H) (cfg (some (.read i)) v [] saved output) =
      cfg none none [] saved (false :: output) := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, contents, hi]
  funext k
  fin_cases k <;> rfl

theorem read_end {H : ℕ} (i : Fin (H + 1)) (hi : i.val = H) (v : Control)
    (source saved output : List Bool) :
    advance (program H) (cfg (some (.read i)) v source saved output) =
      cfg (some .restore) v source saved output := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, hi]

theorem restore_cons {H : ℕ} (v : Control) (b : Bool)
    (source saved output : List Bool) :
    advance (program H) (cfg (some .restore) v source (b :: saved) output) =
      cfg (some .restore) (some b) source saved (b :: output) := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, contents]
  funext k
  fin_cases k <;> rfl

theorem restore_nil {H : ℕ} (v : Control) (source output : List Bool) :
    advance (program H) (cfg (some .restore) v source [] output) =
      cfg none none source [] (true :: output) := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, contents]
  funext k
  fin_cases k <;> rfl

theorem restore_run {H : ℕ} (v : Control) (source saved output : List Bool) :
    run (H := H) (saved.length + 1) (cfg (some .restore) v source saved output) =
      cfg none none source [] (true :: (saved.reverse ++ output)) := by
  induction saved generalizing v output with
  | nil => simpa only [List.length_nil, Nat.zero_add, List.reverse_nil, List.nil_append] using
      restore_nil (H := H) v source output
  | cons b saved ih =>
      rw [List.length_cons, run_succ, restore_cons, ih]
      simp

theorem read_block {H : ℕ} (table : List Bool) (i : Fin (H + 1))
    (hi : i.val + table.length = H) (v : Control) (rest saved output : List Bool) :
    ∃ w, run (table.length + 1) (cfg (some (.read i)) v (table ++ rest) saved output) =
      cfg (some .restore) w rest (table.reverse ++ saved) output := by
  induction table generalizing i v saved with
  | nil =>
      refine ⟨v, ?_⟩
      simpa only [List.length_nil, Nat.zero_add, List.nil_append, List.reverse_nil] using
        read_end i (by simpa using hi) v rest saved output
  | cons b table ih =>
      have hil : i.val < H := by simp only [List.length_cons] at hi; omega
      obtain ⟨w, hw⟩ := ih ⟨i.val + 1, by omega⟩ (by
        change i.val + 1 + table.length = H
        simp only [List.length_cons] at hi
        omega)
        (some b) (b :: saved)
      refine ⟨w, ?_⟩
      rw [List.length_cons, run_succ, List.cons_append, read_cons i hil]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hw

/-- Read an entire literal truth table, retaining the following source
suffix. The exact `2*H+2` cost includes all reads, reversing and status. -/
theorem table_run (H : ℕ) (table rest output : List Bool) (ht : table.length = H) :
    run (2 * H + 2) (cfg (some (.read 0)) none (table ++ rest) [] output) =
      cfg (H := H) none none rest [] (true :: (table ++ output)) := by
  obtain ⟨w, hw⟩ := read_block table (0 : Fin (H + 1)) (by simp [ht]) none rest [] output
  have htime : 2 * H + 2 = (table.length + 1) + (table.reverse.length + 1) := by
    simp only [List.length_reverse, ht]
    omega
  rw [htime, run_add, hw]
  simp only [List.append_nil, restore_run, List.reverse_reverse]

/-- Truncated tables fail after the actual available bits and one failed
read. Their partially filled work stack is not falsely reported as clean. -/
theorem short_run {H : ℕ} (input : List Bool) (i : Fin (H + 1))
    (hi : i.val + input.length < H) (v : Control) (saved output : List Bool) :
    run (input.length + 1) (cfg (some (.read i)) v input saved output) =
      cfg none none [] (input.reverse ++ saved) (false :: output) := by
  induction input generalizing i v saved with
  | nil =>
      simpa only [List.length_nil, Nat.zero_add, List.reverse_nil, List.nil_append] using
        read_nil i (by simpa using hi) v saved output
  | cons b input ih =>
      have hil : i.val < H := by simp only [List.length_cons] at hi; omega
      rw [List.length_cons, run_succ, read_cons i hil]
      have hr := ih ⟨i.val + 1, by omega⟩ (by
        change i.val + 1 + input.length < H
        simp only [List.length_cons] at hi
        omega)
        (some b) (b :: saved)
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hr

def result (H : ℕ) (input : List Bool) : List Bool :=
  if H ≤ input.length then true :: input.take H else [false]

noncomputable def machine (H : ℕ) : BitMachine.Machine :=
  ofFinite (0 : Fin 3) 2 (.read 0 : Label H) (none : Control) (program H)

theorem rawInit_eq (H : ℕ) (input : List Bool) :
    rawInit (0 : Fin 3) (.read 0 : Label H) (none : Control) input =
      cfg (some (.read 0)) none input [] [] := by
  unfold rawInit cfg
  congr 1
  funext k
  fin_cases k <;> rfl

/-- Total operational bound for the fixed-size block reader, including
truncation. `H` is part of the finite program, not an unbounded register. -/
theorem outputs (H : ℕ) (input : List Bool) :
    (machine H).OutputsWithin input (result H input) (2 * H + 2) := by
  by_cases hlen : H ≤ input.length
  · have hr := table_run H (input.take H) (input.drop H) [] (by simp [hlen])
    simp only [List.take_append_drop, List.append_nil] at hr
    apply outputsWithin_of_raw_run (0 : Fin 3) 2 (.read 0 : Label H) (none : Control)
      (program H) input (result H input) (2 * H + 2) (2 * H + 2) le_rfl
    · rw [rawInit_eq]
      exact congrArg (fun c => c.l) hr
    · rw [rawInit_eq]
      simpa only [result, if_pos hlen, cfg, contents, show ¬(2 : Fin 3) = 0 by decide,
        show ¬(2 : Fin 3) = 1 by decide, ↓reduceIte] using congrArg (fun c => c.stk 2) hr
  · have hr := short_run input (0 : Fin (H + 1)) (by simp; omega) none [] []
    apply outputsWithin_of_raw_run (0 : Fin 3) 2 (.read 0 : Label H) (none : Control)
      (program H) input (result H input) (input.length + 1) (2 * H + 2) (by omega)
    · rw [rawInit_eq]
      exact congrArg (fun c => c.l) hr
    · rw [rawInit_eq]
      simpa only [result, if_neg hlen, cfg, contents, show ¬(2 : Fin 3) = 0 by decide,
        show ¬(2 : Fin 3) = 1 by decide, ↓reduceIte] using congrArg (fun c => c.stk 2) hr

theorem polytime (H : ℕ) : BitMachine.Polytime (result H) := by
  refine ⟨machine H, 2 * H + 2, 0, ?_⟩
  intro input
  simpa only [pow_zero, Nat.mul_one] using outputs H input

/-- The truth entries are extracted in exactly the finite-function order
used by `constraintBits`, preserving all remaining source bits. -/
theorem csp_table_run {n a q : ℕ} (row : SourceCSPCodec.Row n a q)
    (rest output : List Bool) :
    run (2 * a ^ q + 2)
      (cfg (some (.read 0)) none (List.ofFn row.2 ++ rest) [] output) =
      cfg (H := a ^ q) none none rest [] (true :: (List.ofFn row.2 ++ output)) :=
  table_run (a ^ q) (List.ofFn row.2) rest output List.length_ofFn

/-- The existing canonical-number machine reads an actual valid query
field and leaves its suffix intact. This component alone does not perform
the separate comparison with the declared vertex count. -/
theorem canonical_query_run {n : ℕ} (v : Fin n) (rest output : List Bool) :
    ∃ t ≤ 2 * (EncodedCommunication.natField v.val ++ rest).length + 2,
      let c := ProtocolBinaryHeader.run t
        (ProtocolBinaryHeader.cfg (some .scan) (none, none)
          (EncodedCommunication.natField v.val ++ rest) [] output)
      c.l = none ∧ c.stk 0 = rest ∧ c.stk 1 = [] ∧
        c.stk 2 = true :: (v.val.bits ++ output) := by
  have hh : ProtocolBinaryHeader.readChecked none
      (EncodedCommunication.natField v.val ++ rest) = some (v.val.bits, rest) := by
    simp [ProtocolBinaryHeader.readChecked_spec, EncodedCommunication.natField,
      EncodedCommunication.readField_append, ProtocolBinaryHeader.canonicalFrom_none,
      ProtocolBinaryHeader.canonical_of_bits]
  obtain ⟨t, ht, hp⟩ := ProtocolBinaryHeader.scan_correct
    (EncodedCommunication.natField v.val ++ rest) none none [] output
  refine ⟨t, by simpa using ht, ?_⟩
  simpa only [ProtocolBinaryHeader.Post, hh, List.reverse_nil, List.nil_append] using hp

end EthInapproximability.CurrentPaper.SourceCSPRowMachine
