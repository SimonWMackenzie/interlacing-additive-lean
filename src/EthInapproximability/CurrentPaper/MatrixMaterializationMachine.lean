import EthInapproximability.CurrentPaper.MatrixMaterialization
import Mathlib.Data.Fintype.Sigma

/-!
# Finite-stack execution of matrix-entry rules

Source: locked v8 `03-exact-hardness.tex`, the explicit exact matrix, and
`B-effectivity-details.tex`, literal entry evaluation. This module compiles
the source-row rule first. A query carries the alignment bit, three tail
bits, the preceding source-column bits, and the current source bit. The
machine itself counts active predecessors, saturating at two, and selects
the exact output bit. No active-rank or source-support certificate is input.

Predecessor bits are encoded as `true, bit` pairs followed by `false`.
Collecting these bits from the row-major source table, the template-row
branch, and enumeration of the complete output table remain separate
controller obligations. This module does not claim they cost one step.
-/

namespace EthInapproximability.CurrentPaper.MatrixMaterializationMachine

open Turing Turing.TM2.Stmt BitMachineEncoding

def increment (r : Fin 3) (b : Bool) : Fin 3 :=
  if b then ⟨min 2 (r.val + 1), by omega⟩ else r

theorem increment_val (r : Fin 3) (b : Bool) :
    (increment r b).val = min 2 (r.val + if b then 1 else 0) := by
  fin_cases r <;> cases b <;> rfl

def countFrom : Fin 3 → List Bool → Fin 3
  | r, [] => r
  | r, b :: q => countFrom (increment r b) q

theorem countFrom_val (r : Fin 3) (q : List Bool) :
    (countFrom r q).val = min 2 (r.val + (q.filter id).length) := by
  induction q generalizing r with
  | nil => simp [countFrom, Nat.min_eq_right (by omega : r.val ≤ 2)]
  | cons b q ih =>
      rw [countFrom, ih, increment_val]
      cases b <;> simp only [List.filter, id_eq, Bool.false_eq_true, reduceIte,
        List.length_cons] <;> omega

structure Control where
  aligned : Bool := false
  tail0 : Bool := false
  tail1 : Bool := false
  tail2 : Bool := false
  rank : Fin 3 := 0
  answer : Bool := false
  live : Bool := false
  deriving DecidableEq

private def controlEquiv : (Bool × Bool × Bool × Bool × Fin 3 × Bool × Bool) ≃ Control where
  toFun v := ⟨v.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1,
    v.2.2.2.2.2.1, v.2.2.2.2.2.2⟩
  invFun s := (s.aligned, s.tail0, s.tail1, s.tail2, s.rank, s.answer, s.live)
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype Control := Fintype.ofEquiv _ controlEquiv

inductive Label where
  | alignment | tail0 | tail1 | tail2 | flag | predecessor | current | clear
  deriving DecidableEq, Fintype

def select (s : Control) (active : Bool) : Bool :=
  if s.aligned && active then
    if s.rank.val = 0 then s.tail0 else if s.rank.val = 1 then s.tail1 else s.tail2
  else s.tail2

def program : Label → TM2.Stmt (fun _ : Fin 1 => Bool) Label Control
  | .alignment => pop 0 (fun s b => {s with aligned := b.getD false}) (goto (fun _ => .tail0))
  | .tail0 => pop 0 (fun s b => {s with tail0 := b.getD false}) (goto (fun _ => .tail1))
  | .tail1 => pop 0 (fun s b => {s with tail1 := b.getD false}) (goto (fun _ => .tail2))
  | .tail2 => pop 0 (fun s b => {s with tail2 := b.getD false}) (goto (fun _ => .flag))
  | .flag => pop 0 (fun s b => {s with live := b.getD false})
      (branch Control.live (goto (fun _ => .predecessor)) (goto (fun _ => .current)))
  | .predecessor => pop 0 (fun s b => {s with rank := increment s.rank (b.getD false)})
      (goto (fun _ => .flag))
  | .current => pop 0 (fun s b => {s with answer := select s (b.getD false)})
      (goto (fun _ => .clear))
  | .clear => pop 0 (fun s b => {s with live := b.isSome})
      (branch Control.live (goto (fun _ => .clear))
        (push 0 Control.answer (load (fun _ => {}) halt)))

def cfg (l : Option Label) (s : Control) (q : List Bool) :
    TM2.Cfg (fun _ : Fin 1 => Bool) Label Control := ⟨l, s, fun _ => q⟩

def run (n : ℕ) (c : TM2.Cfg (fun _ : Fin 1 => Bool) Label Control) :=
  ((advance program)^[n]) c

private theorem run_succ {c d : TM2.Cfg (fun _ : Fin 1 => Bool) Label Control}
    (h : TM2.step program c = some d) (n : ℕ) : run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : TM2.Cfg (fun _ : Fin 1 => Bool) Label Control}
    {m : ℕ} (h : run m c = d) (n : ℕ) : run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem update_stack (q t : List Bool) :
    Function.update (fun _ : Fin 1 => q) 0 t = fun _ => t := by
  funext k
  fin_cases k
  rfl

def header (aligned : Bool) (tail : Fin 3 → Bool) : Control :=
  ⟨aligned, tail 0, tail 1, tail 2, 0, false, false⟩

def prefixBits (q : List Bool) : List Bool := q.flatMap (fun b => [true, b]) ++ [false]

def encodeQuery (aligned : Bool) (tail : Fin 3 → Bool) (before : List Bool)
    (active : Bool) : List Bool :=
  aligned :: tail 0 :: tail 1 :: tail 2 :: (prefixBits before ++ [active])

def answer (aligned : Bool) (tail : Fin 3 → Bool) (before : List Bool)
    (active : Bool) : Bool :=
  select {header aligned tail with rank := countFrom 0 before} active

private theorem step_alignment (s : Control) (b : Bool) (q : List Bool) :
    TM2.step program (cfg (some .alignment) s (b :: q)) =
      some (cfg (some .tail0) {s with aligned := b} q) := by
  simp [TM2.step, TM2.stepAux, program, cfg, update_stack]

private theorem step_tail0 (s : Control) (b : Bool) (q : List Bool) :
    TM2.step program (cfg (some .tail0) s (b :: q)) =
      some (cfg (some .tail1) {s with tail0 := b} q) := by
  simp [TM2.step, TM2.stepAux, program, cfg, update_stack]

private theorem step_tail1 (s : Control) (b : Bool) (q : List Bool) :
    TM2.step program (cfg (some .tail1) s (b :: q)) =
      some (cfg (some .tail2) {s with tail1 := b} q) := by
  simp [TM2.step, TM2.stepAux, program, cfg, update_stack]

private theorem step_tail2 (s : Control) (b : Bool) (q : List Bool) :
    TM2.step program (cfg (some .tail2) s (b :: q)) =
      some (cfg (some .flag) {s with tail2 := b} q) := by
  simp [TM2.step, TM2.stepAux, program, cfg, update_stack]

private theorem step_flag_true (s : Control) (q : List Bool) :
    TM2.step program (cfg (some .flag) s (true :: q)) =
      some (cfg (some .predecessor) {s with live := true} q) := by
  simp [TM2.step, TM2.stepAux, program, cfg, update_stack]

private theorem step_flag_false (s : Control) (q : List Bool) :
    TM2.step program (cfg (some .flag) s (false :: q)) =
      some (cfg (some .current) {s with live := false} q) := by
  simp [TM2.step, TM2.stepAux, program, cfg, update_stack]

private theorem step_predecessor (s : Control) (b : Bool) (q : List Bool) :
    TM2.step program (cfg (some .predecessor) s (b :: q)) =
      some (cfg (some .flag) {s with rank := increment s.rank b} q) := by
  simp [TM2.step, TM2.stepAux, program, cfg, update_stack]

private theorem step_current (s : Control) (b : Bool) (q : List Bool) :
    TM2.step program (cfg (some .current) s (b :: q)) =
      some (cfg (some .clear) {s with answer := select s b} q) := by
  simp [TM2.step, TM2.stepAux, program, cfg, update_stack]

private theorem step_clear_cons (s : Control) (b : Bool) (q : List Bool) :
    TM2.step program (cfg (some .clear) s (b :: q)) =
      some (cfg (some .clear) {s with live := true} q) := by
  simp [TM2.step, TM2.stepAux, program, cfg, update_stack]

private theorem step_clear_nil (s : Control) :
    TM2.step program (cfg (some .clear) s []) = some (cfg none {} [s.answer]) := by
  simp [TM2.step, TM2.stepAux, program, cfg, update_stack]

theorem header_correct (aligned : Bool) (tail : Fin 3 → Bool) (q : List Bool) :
    run 4 (cfg (some .alignment) {} (aligned :: tail 0 :: tail 1 :: tail 2 :: q)) =
      cfg (some .flag) (header aligned tail) q := by
  rw [run_succ (step_alignment _ _ _) 3, run_succ (step_tail0 _ _ _) 2,
    run_succ (step_tail1 _ _ _) 1, run_succ (step_tail2 _ _ _) 0]
  rfl

theorem prefix_correct (s : Control) (before suffix : List Bool) :
    run (2 * before.length + 1) (cfg (some .flag) s (prefixBits before ++ suffix)) =
      cfg (some .current) {s with rank := countFrom s.rank before, live := false} suffix := by
  induction before generalizing s with
  | nil => simpa [prefixBits, countFrom] using run_succ (step_flag_false s suffix) 0
  | cons b before ih =>
      simp only [prefixBits, List.flatMap_cons, List.append_assoc, List.cons_append,
        List.nil_append, List.length_cons]
      rw [show 2 * (before.length + 1) + 1 = (2 * before.length + 1) + 1 + 1 by omega]
      rw [run_succ (step_flag_true _ _) _, run_succ (step_predecessor _ _ _) _]
      simpa only [prefixBits, countFrom, List.append_assoc, List.singleton_append] using
        ih {s with live := true, rank := increment s.rank b}

theorem clear_correct (s : Control) (q : List Bool) :
    run (q.length + 1) (cfg (some .clear) s q) = cfg none {} [s.answer] := by
  induction q generalizing s with
  | nil => exact run_succ (step_clear_nil s) 0
  | cons b q ih =>
      rw [List.length_cons, run_succ (step_clear_cons _ _ _) _]
      exact ih _

theorem run_correct (aligned : Bool) (tail : Fin 3 → Bool) (before : List Bool)
    (active : Bool) :
    run (2 * before.length + 7)
      (cfg (some .alignment) {} (encodeQuery aligned tail before active)) =
      cfg none {} [answer aligned tail before active] := by
  have h₁ := header_correct aligned tail (prefixBits before ++ [active])
  have h₂ := prefix_correct (header aligned tail) before [active]
  have h₃ := run_succ (step_current
    {header aligned tail with rank := countFrom 0 before, live := false} active []) 0
  have h₄ := clear_correct
    {{header aligned tail with rank := countFrom 0 before, live := false} with
      answer := select {header aligned tail with rank := countFrom 0 before, live := false} active} []
  have h₁₂ := (run_add h₁ (2 * before.length + 1)).trans h₂
  have h₁₂₃ := (run_add h₁₂ 1).trans h₃
  have h := (run_add h₁₂₃ 1).trans h₄
  have htime : 4 + (2 * before.length + 1) + 1 + 1 = 2 * before.length + 7 := by omega
  simpa only [htime, encodeQuery, answer, select, header] using h

noncomputable def bitMachine : BitMachine.Machine :=
  ofFinite (0 : Fin 1) 0 .alignment ({} : Control) program

theorem bitMachine_outputs (aligned : Bool) (tail : Fin 3 → Bool) (before : List Bool)
    (active : Bool) :
    bitMachine.OutputsWithin (encodeQuery aligned tail before active)
      [answer aligned tail before active] (2 * before.length + 7) := by
  have hi : rawInit (0 : Fin 1) .alignment ({} : Control)
      (encodeQuery aligned tail before active) =
      cfg (some .alignment) {} (encodeQuery aligned tail before active) := by
    unfold rawInit cfg
    congr 1
    funext k
    fin_cases k
    rfl
  apply outputsWithin_of_raw_run (0 : Fin 1) 0 .alignment ({} : Control) program
    (encodeQuery aligned tail before active) [answer aligned tail before active]
    (2 * before.length + 7) _ le_rfl
  · change (run (2 * before.length + 7) _).l = none
    rw [hi, run_correct]
    rfl
  · change (run (2 * before.length + 7) _).stk 0 = _
    rw [hi, run_correct]
    rfl

/-! ## Correspondence with the literal exact matrix

The list below reads the actual source bits. Positions at or after the
current row contribute zero, so it has the public fixed length `n`. It
contains no supplied rank, coloring, support promise, or matrix answer.
Its gathering from the row-major source encoding is not yet compiled here.
-/

def precedingColumn {n d : ℕ} (v : Fin n → Fin d → Bool) (i : Fin n) (α : Fin d) :
    List Bool := (List.finRange n).map (fun j => if j < i then v j α else false)

@[simp] theorem precedingColumn_length {n d : ℕ}
    (v : Fin n → Fin d → Bool) (i : Fin n) (α : Fin d) :
    (precedingColumn v i α).length = n := by simp [precedingColumn]

theorem precedingColumn_count {n d : ℕ}
    (v : Fin n → Fin d → Bool) (i : Fin n) (α : Fin d) :
    ((precedingColumn v i α).filter id).length = Construction.activeRank v α i := by
  let p : Fin n → Bool := fun j => if j < i then v j α else false
  change (((List.finRange n).map p).filter id).length = _
  rw [List.filter_map, List.length_map]
  have hn := (List.nodup_finRange n).filter (id ∘ p)
  rw [← List.toFinset_card_of_nodup hn, List.toFinset_filter, List.toFinset_finRange]
  congr 1
  ext j
  simp only [Construction.activeBefore, Construction.activeItems, Finset.mem_filter,
    Finset.mem_univ, true_and, p]
  by_cases h : j < i <;> simp [h, and_comm]

theorem answer_eq (aligned : Bool) (tail : Fin 3 → Bool) (before : List Bool)
    (active : Bool) :
    answer aligned tail before active =
      if aligned && active then tail (countFrom 0 before) else tail 2 := by
  unfold answer select header
  generalize countFrom 0 before = r
  fin_cases r <;> cases aligned <;> cases active <;> rfl

theorem source_answer_correct {n d N₁ : ℕ}
    (v : Fin n → Fin d → Bool)
    (cap : ∀ α, (Construction.activeItems v α).card ≤ 2)
    (i : Fin n) (c : ExactConstruction.Columns d N₁) :
    answer (decide (ExactConstruction.aligned c)) c.1
      (precedingColumn v i (c.2 0).1) (v i (c.2 0).1) =
      ExactConstruction.vectorEntry v cap i c := by
  rw [answer_eq]
  unfold ExactConstruction.vectorEntry
  by_cases h : ExactConstruction.aligned c
  · simp only [h, decide_true, Bool.true_and, ↓reduceIte]
    by_cases hi : v i (c.2 0).1 = true
    · simp only [hi, ↓reduceIte, ↓reduceDIte]
      apply congrArg c.1
      apply Fin.ext
      rw [countFrom_val, precedingColumn_count]
      have hr := (Construction.activeRank_lt_card v (c.2 0).1 i hi).trans_le (cap _)
      change min 2 (0 + Construction.activeRank v (c.2 0).1 i) =
        Construction.activeRank v (c.2 0).1 i
      omega
    · simp [hi]
  · simp [h]

def sourceQuery {n d N₁ : ℕ} (v : Fin n → Fin d → Bool)
    (i : Fin n) (c : ExactConstruction.Columns d N₁) : List Bool :=
  encodeQuery (decide (ExactConstruction.aligned c)) c.1
    (precedingColumn v i (c.2 0).1) (v i (c.2 0).1)

/-- Literal source-row execution. The support bound is used only to identify
the answer with the manuscript matrix, never by the query or machine. -/
theorem source_matrix_outputs {a d N₁ N₂ n : ℕ} (ha : 2 ≤ a)
    (C₁ : ExactConstruction.FirstFamily a N₁) (C₂ : ExactConstruction.SecondFamily a d N₂)
    (v : Fin n → Fin d → Bool)
    (cap : ∀ α, (Construction.activeItems v α).card ≤ 2)
    (i : Fin n) (c : ExactConstruction.Columns d N₁) :
    bitMachine.OutputsWithin (sourceQuery v i c)
      [ExactConstruction.matrix ha C₁ C₂ v cap (.inr i) c] (2 * n + 7) := by
  have h := bitMachine_outputs (decide (ExactConstruction.aligned c)) c.1
    (precedingColumn v i (c.2 0).1) (v i (c.2 0).1)
  rw [source_answer_correct v cap i c] at h
  simpa only [sourceQuery, precedingColumn_length,
    ExactConstruction.matrix] using h

end EthInapproximability.CurrentPaper.MatrixMaterializationMachine
