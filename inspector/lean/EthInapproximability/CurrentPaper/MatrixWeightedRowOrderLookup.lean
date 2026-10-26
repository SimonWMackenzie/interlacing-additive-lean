import EthInapproximability.CurrentPaper.MatrixIndexSplit
import EthInapproximability.CurrentPaper.Construction
import EthInapproximability.CurrentPaper.EncodedGraph

/-! # Physical lookup in a serialized `Construction.ItemOrder` table

The table is a concatenation of `true^rank ++ [false]` fields in increasing
input-label order. The selector traverses the requested number of fields,
copies the selected unary rank, then restores both the table and index.
The table is an explicit input, not a semantic lookup oracle.
-/

namespace EthInapproximability.CurrentPaper.MatrixWeightedRowOrderLookup

open Turing Turing.TM2.Stmt BitMachineEncoding

def fields (rs : List ℕ) : List Bool :=
  rs.flatMap EncodedGraph.unary

def orderWord {nv nb : ℕ} (order : Construction.ItemOrder nv nb) : List Bool :=
  fields (List.ofFn (fun j : Fin (nv + nb) => (order j).val))

inductive Label where
  | select | skip | read | restoreTable | restoreIndex
  deriving DecidableEq, Fintype

abbrev Stack := Fin 5
abbrev Control := Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .select => pop 0 (fun _ b => b)
      (branch Option.isSome
        (push 3 (fun _ => true) (goto (fun _ => .skip)))
        (goto (fun _ => .read)))
  | .skip => pop 1 (fun _ b => b)
      (branch Option.isSome
        (push 2 (fun v => v.getD false)
          (branch (fun v => v == some false)
            (goto (fun _ => .select)) (goto (fun _ => .skip))))
        (goto (fun _ => .select)))
  | .read => pop 1 (fun _ b => b)
      (branch Option.isSome
        (push 2 (fun v => v.getD false)
          (branch (fun v => v == some true)
            (push 4 (fun _ => true) (goto (fun _ => .read)))
            (goto (fun _ => .restoreTable))))
        (goto (fun _ => .restoreTable)))
  | .restoreTable => pop 2 (fun _ b => b)
      (branch Option.isSome
        (push 1 (fun v => v.getD false) (goto (fun _ => .restoreTable)))
        (goto (fun _ => .restoreIndex)))
  | .restoreIndex => pop 3 (fun _ b => b)
      (branch Option.isSome
        (push 0 (fun _ => true) (goto (fun _ => .restoreIndex)))
        halt)

def cfg (l : Option Label) (v : Control)
    (index table saved count output : List Bool) : Config :=
  ⟨l, v, ![index, table, saved, count, output]⟩

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem run_succ {c d : Config} (h : advance program c = d) (t : ℕ) :
    run (t + 1) c = run t d := by
  simp only [run, Function.iterate_succ_apply, h]

private theorem select_cons (idx table saved count out : List Bool)
    (v : Control) :
    advance program (cfg (some .select) v (true :: idx) table saved count out) =
      cfg (some .skip) (some true) idx table saved (true :: count) out := by
  simp [advance, program, TM2.step, TM2.stepAux, cfg]
  funext k
  fin_cases k <;> rfl

private theorem select_nil (table saved count out : List Bool) (v : Control) :
    advance program (cfg (some .select) v [] table saved count out) =
      cfg (some .read) none [] table saved count out := by
  simp [advance, program, TM2.step, TM2.stepAux, cfg]

private theorem skip_true (idx tail saved count out : List Bool) (v : Control) :
    advance program (cfg (some .skip) v idx (true :: tail) saved count out) =
      cfg (some .skip) (some true) idx tail (true :: saved) count out := by
  simp [advance, program, TM2.step, TM2.stepAux, cfg]
  funext k
  fin_cases k <;> rfl

private theorem skip_false (idx tail saved count out : List Bool) (v : Control) :
    advance program (cfg (some .skip) v idx (false :: tail) saved count out) =
      cfg (some .select) (some false) idx tail (false :: saved) count out := by
  simp [advance, program, TM2.step, TM2.stepAux, cfg]
  funext k
  fin_cases k <;> rfl

private theorem read_true (tail saved count out : List Bool) (v : Control) :
    advance program (cfg (some .read) v [] (true :: tail) saved count out) =
      cfg (some .read) (some true) [] tail (true :: saved) count (true :: out) := by
  simp [advance, program, TM2.step, TM2.stepAux, cfg]
  funext k
  fin_cases k <;> rfl

private theorem read_false (tail saved count out : List Bool) (v : Control) :
    advance program (cfg (some .read) v [] (false :: tail) saved count out) =
      cfg (some .restoreTable) (some false) [] tail (false :: saved) count out := by
  simp [advance, program, TM2.step, TM2.stepAux, cfg]
  funext k
  fin_cases k <;> rfl

private theorem restore_table_cons (index table saved count out : List Bool)
    (v : Control) (b : Bool) :
    advance program (cfg (some .restoreTable) v index table (b :: saved) count out) =
      cfg (some .restoreTable) (some b) index (b :: table) saved count out := by
  simp [advance, program, TM2.step, TM2.stepAux, cfg]
  funext k
  fin_cases k <;> rfl

private theorem restore_table_nil (index table count out : List Bool) (v : Control) :
    advance program (cfg (some .restoreTable) v index table [] count out) =
      cfg (some .restoreIndex) none index table [] count out := by
  simp [advance, program, TM2.step, TM2.stepAux, cfg]

private theorem restore_index_cons (index count table out : List Bool)
    (v : Control) :
    advance program (cfg (some .restoreIndex) v index table [] (true :: count) out) =
      cfg (some .restoreIndex) (some true) (true :: index) table [] count out := by
  simp [advance, program, TM2.step, TM2.stepAux, cfg]
  funext k
  fin_cases k <;> rfl

private theorem restore_index_nil (index table out : List Bool) (v : Control) :
    advance program (cfg (some .restoreIndex) v index table [] [] out) =
      cfg none none index table [] [] out := by
  simp [advance, program, TM2.step, TM2.stepAux, cfg]

private theorem true_rotate (n : ℕ) (tail : List Bool) :
    List.replicate n true ++ true :: tail =
      true :: List.replicate n true ++ tail := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa [List.replicate_succ, List.append_assoc] using
        (congrArg (List.cons true) ih)

theorem skip_field_run (n : ℕ) (idx tail saved count out : List Bool)
    (v : Control) :
    run (n + 1) (cfg (some .skip) v idx
      (EncodedGraph.unary n ++ tail) saved count out) =
      cfg (some .select) (some false) idx tail
        ((EncodedGraph.unary n).reverse ++ saved) count out := by
  induction n generalizing v saved with
  | zero =>
      simpa [EncodedGraph.unary, run] using
        skip_false idx tail saved count out v
  | succ n ih =>
      have h := (run_succ
        (skip_true idx (EncodedGraph.unary n ++ tail) saved count out v)
        (n + 1)).trans (ih (true :: saved) (some true))
      simpa [EncodedGraph.unary, List.replicate_succ,
        List.reverse_cons, List.append_assoc] using h

theorem read_field_run (n : ℕ) (tail saved count out : List Bool)
    (v : Control) :
    run (n + 1) (cfg (some .read) v []
      (EncodedGraph.unary n ++ tail) saved count out) =
      cfg (some .restoreTable) (some false) [] tail
        ((EncodedGraph.unary n).reverse ++ saved) count
        (List.replicate n true ++ out) := by
  induction n generalizing v saved out with
  | zero =>
      simpa [EncodedGraph.unary, run] using
        read_false tail saved count out v
  | succ n ih =>
      have h := (run_succ
        (read_true (EncodedGraph.unary n ++ tail) saved count out v)
        (n + 1)).trans (ih (true :: saved) (true :: out) (some true))
      rw [true_rotate] at h
      simpa [EncodedGraph.unary, List.replicate_succ,
        List.reverse_cons, List.append_assoc] using h

theorem restore_table_run (saved index table count out : List Bool)
    (v : Control) :
    run (saved.length + 1) (cfg (some .restoreTable) v index table saved count out) =
      cfg (some .restoreIndex) none index (saved.reverse ++ table) [] count out := by
  induction saved generalizing table v with
  | nil => simpa [run] using restore_table_nil index table count out v
  | cons b saved ih =>
      have h := (run_succ
        (restore_table_cons index table saved count out v b)
        (saved.length + 1)).trans (ih (b :: table) (some b))
      simpa [List.reverse_cons, List.append_assoc] using h

theorem restore_index_run (n : ℕ) (index table out : List Bool)
    (v : Control) :
    run (n + 1) (cfg (some .restoreIndex) v index table []
      (List.replicate n true) out) =
      cfg none none (List.replicate n true ++ index) table [] [] out := by
  induction n generalizing index v with
  | zero => simpa [run] using restore_index_nil index table out v
  | succ n ih =>
      have h := (run_succ
        (restore_index_cons index (List.replicate n true) table out v)
        (n + 1)).trans (ih (true :: index) (some true))
      rw [true_rotate] at h
      simpa [List.replicate_succ, List.cons_append] using h

theorem skip_prefix_run (ps : List ℕ) (selected saved count out : List Bool)
    (v : Control) :
    run ((fields ps).length + ps.length + 1)
      (cfg (some .select) v (List.replicate ps.length true)
        (fields ps ++ selected) saved count out) =
      cfg (some .read) none [] selected
        ((fields ps).reverse ++ saved)
        (List.replicate ps.length true ++ count) out := by
  induction ps generalizing saved count v with
  | nil =>
      simpa [fields, run] using select_nil selected saved count out v
  | cons n ps ih =>
      let rest := fields ps ++ selected
      let tailTime := (fields ps).length + ps.length + 1
      have h₀ := select_cons (List.replicate ps.length true)
        (EncodedGraph.unary n ++ rest) saved count out v
      have h₁ := skip_field_run n (List.replicate ps.length true)
        rest saved (true :: count) out (some true)
      have h₂ := ih ((EncodedGraph.unary n).reverse ++ saved)
        (true :: count) (some false)
      have h := (run_succ h₀ (n + 1 + tailTime)).trans
        ((run_add h₁ tailTime).trans h₂)
      have hcount : List.replicate ps.length true ++ true :: count =
          List.replicate (n :: ps).length true ++ count := by
        simpa [List.length_cons, List.replicate_succ] using
          true_rotate ps.length count
      have htime : n + 1 + tailTime + 1 =
          (fields (n :: ps)).length + (n :: ps).length + 1 := by
        simp [fields, EncodedGraph.unary, tailTime]
        omega
      rw [htime] at h
      simpa [fields, rest, tailTime, EncodedGraph.unary,
        List.reverse_append, List.append_assoc, hcount] using h

theorem select_run (ps : List ℕ) (rank : ℕ) (suffix out : List Bool) :
    let table := fields ps ++ EncodedGraph.unary rank ++ suffix;
    ∃ t ≤ 2 * table.length + 2 * ps.length + 3,
      run t (cfg (some .select) none (List.replicate ps.length true)
        table [] [] out) =
      cfg none none (List.replicate ps.length true)
        table [] [] (List.replicate rank true ++ out) := by
  let pre := fields ps
  let selected := EncodedGraph.unary rank
  let table := pre ++ selected ++ suffix
  let a := pre.length + ps.length + 1
  let b := rank + 1
  let c := (pre ++ selected).length + 1
  let d := ps.length + 1
  have h₁ := skip_prefix_run ps (selected ++ suffix) [] [] out none
  have h₂ := read_field_run rank suffix pre.reverse
    (List.replicate ps.length true) out none
  have h₃ := restore_table_run (selected.reverse ++ pre.reverse)
    [] suffix (List.replicate ps.length true)
    (List.replicate rank true ++ out) (some false)
  have h₄ := restore_index_run ps.length [] table
    (List.replicate rank true ++ out) none
  have h₁' : run a (cfg (some .select) none (List.replicate ps.length true)
      table [] [] out) =
      cfg (some .read) none [] (selected ++ suffix)
        pre.reverse (List.replicate ps.length true) out := by
    simpa [a, table, pre, selected, List.append_assoc] using h₁
  have h₂' : run b (cfg (some .read) none [] (selected ++ suffix)
      pre.reverse (List.replicate ps.length true) out) =
      cfg (some .restoreTable) (some false) [] suffix
        (selected.reverse ++ pre.reverse)
        (List.replicate ps.length true) (List.replicate rank true ++ out) := by
    simpa [b, selected] using h₂
  have h₃' : run c (cfg (some .restoreTable) (some false) [] suffix
      (selected.reverse ++ pre.reverse)
      (List.replicate ps.length true) (List.replicate rank true ++ out)) =
      cfg (some .restoreIndex) none [] table []
        (List.replicate ps.length true) (List.replicate rank true ++ out) := by
    simpa [c, table, selected, pre, List.reverse_append,
      List.append_assoc, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using h₃
  have h₄' : run d (cfg (some .restoreIndex) none [] table []
      (List.replicate ps.length true) (List.replicate rank true ++ out)) =
      cfg none none (List.replicate ps.length true) table [] []
        (List.replicate rank true ++ out) := by
    simpa [d] using h₄
  let t := a + b + c + d
  have hr := (run_add (run_add (run_add h₁' b |>.trans h₂') c |>.trans h₃') d).trans h₄'
  refine ⟨t, ?_, ?_⟩
  · dsimp [t, a, b, c, d, table, pre, selected]
    simp only [List.length_append, EncodedGraph.unary, List.length_replicate,
      List.length_singleton]
    omega
  · simpa [t, table] using hr

theorem orderWord_split {nv nb : ℕ}
    (order : Construction.ItemOrder nv nb) (j : Fin (nv + nb)) :
    let rs := List.ofFn (fun k : Fin (nv + nb) => (order k).val)
    orderWord order = fields (rs.take j.val) ++
      EncodedGraph.unary (order j).val ++ fields (rs.drop (j.val + 1)) ∧
    (rs.take j.val).length = j.val := by
  let rs := List.ofFn (fun k : Fin (nv + nb) => (order k).val)
  have hj : j.val < rs.length := by simp [rs]
  have hget : rs[j.val] = (order j).val := by
    simp [rs]
  have hdrop := List.drop_eq_getElem_cons hj
  have hsplit := List.take_append_drop j.val rs
  have hwords : rs = rs.take j.val ++ (order j).val :: rs.drop (j.val + 1) := by
    rw [← hget, ← hdrop]
    exact hsplit.symm
  constructor
  · change fields rs = fields (rs.take j.val) ++
        EncodedGraph.unary (order j).val ++ fields (rs.drop (j.val + 1))
    conv_lhs => rw [hwords]
    simp [fields, List.flatMap_append, List.append_assoc]
  · simp

/-- The requested semantic permutation entry is extracted from literal
serialized fields by the same fixed physical selector. This theorem assumes
the table word is already on its input stack; its producer is separate. -/
theorem orderWord_run {nv nb : ℕ}
    (order : Construction.ItemOrder nv nb) (j : Fin (nv + nb))
    (out : List Bool) :
    ∃ t ≤ 2 * (orderWord order).length + 2 * j.val + 3,
      run t (cfg (some .select) none (List.replicate j.val true)
        (orderWord order) [] [] out) =
      cfg none none (List.replicate j.val true)
        (orderWord order) [] []
        (List.replicate (order j).val true ++ out) := by
  let rs := List.ofFn (fun k : Fin (nv + nb) => (order k).val)
  obtain ⟨hsplit, hlen⟩ := orderWord_split order j
  obtain ⟨t, ht, hr⟩ := select_run (rs.take j.val)
    (order j).val (fields (rs.drop (j.val + 1))) out
  have hsplit' : orderWord order = fields (rs.take j.val) ++
      EncodedGraph.unary (order j).val ++ fields (rs.drop (j.val + 1)) := hsplit
  refine ⟨t, ?_, ?_⟩
  · rw [hlen] at ht
    rw [hsplit']
    exact ht
  · rw [hlen] at hr
    simpa only [← hsplit', List.append_assoc] using hr

end EthInapproximability.CurrentPaper.MatrixWeightedRowOrderLookup
