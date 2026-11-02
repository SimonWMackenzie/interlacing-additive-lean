import EthInapproximability.CurrentPaper.SourceFieldWriter
import EthInapproximability.CurrentPaper.EncodedCNF

/-!
# Literal-by-literal emission of an ordered three-CNF clause

Source: frozen v8 `06-eth.tex`, source encoding. Three binary variable words
are stored in physical stacks; the three signs are fixed finite control.
Every marker, sign and variable bit is pushed by the controller below.
-/

namespace EthInapproximability.CurrentPaper.SourceLiteralWriter

open Turing TM2.Stmt BitMachineEncoding EncodedCommunication

inductive Label where
  | begin : Fin 4 → Label
  | emit : Fin 3 → Label
  | finish
  deriving DecidableEq, Fintype

abbrev Stack := Fin 5
abbrev Bank := Fin 3 → List Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label (Option Bool)

def contents (S : Bank) (saved output : List Bool) : Stack → List Bool :=
  fun i => if h : i.val < 3 then S ⟨i.val, h⟩ else if i = 3 then saved else output

def cfg (l : Option Label) (v : Option Bool) (S : Bank)
    (saved output : List Bool) : Config := ⟨l, v, contents S saved output⟩

def program (sign : Fin 3 → Bool) : Label → TM2.Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | .begin i => if h : i.val < 3 then
      push 3 (fun _ => sign ⟨i.val, h⟩) (goto (fun _ => .emit ⟨i.val, h⟩))
      else goto (fun _ => .finish)
  | .emit i => pop ⟨i.val, by omega⟩ (fun _ b => b)
      (branch Option.isSome
        (push 3 (fun _ => true) (push 3 (fun b => b.getD false) (goto (fun _ => .emit i))))
        (push 3 (fun _ => false) (goto (fun _ => .begin ⟨i.val + 1, by omega⟩))))
  | .finish => pop 3 (fun _ b => b)
      (branch Option.isSome (push 4 (fun b => b.getD false) (goto (fun _ => .finish)))
        (load (fun _ => none) halt))

def run (sign : Fin 3 → Bool) (t : ℕ) (c : Config) := ((advance (program sign))^[t]) c

theorem run_succ (sign : Fin 3 → Bool) (t : ℕ) (c : Config) :
    run sign (t + 1) c = run sign t (advance (program sign) c) :=
  Function.iterate_succ_apply _ _ _

theorem run_add (sign : Fin 3 → Bool) (t u : ℕ) (c : Config) :
    run sign (t + u) c = run sign u (run sign t c) := by
  simpa only [run, Nat.add_comm] using Function.iterate_add_apply (advance (program sign)) u t c

theorem begin_step (sign : Fin 3 → Bool) (i : Fin 3) (v : Option Bool)
    (S : Bank) (saved output : List Bool) :
    advance (program sign) (cfg (some (.begin ⟨i.val, by omega⟩)) v S saved output) =
      cfg (some (.emit i)) v S (sign i :: saved) output := by
  simp only [advance, cfg, TM2.step, program, dif_pos i.isLt, TM2.stepAux,
    Option.getD_some]
  congr 1
  funext k
  fin_cases k <;> rfl

theorem emit_cons (sign : Fin 3 → Bool) (i : Fin 3) (v : Option Bool)
    (S : Bank) (b : Bool) (q saved output : List Bool) (hS : S i = b :: q) :
    advance (program sign) (cfg (some (.emit i)) v S saved output) =
      cfg (some (.emit i)) (some b) (Function.update S i q) (b :: true :: saved) output := by
  simp only [advance, cfg, TM2.step, program, TM2.stepAux, contents, dif_pos i.isLt,
    hS, List.head?_cons, List.tail_cons, Option.isSome_some, cond_true, Option.getD_some]
  congr 1
  funext k
  fin_cases k <;> fin_cases i <;> simp_all [contents, Function.update_apply]

theorem emit_nil (sign : Fin 3 → Bool) (i : Fin 3) (v : Option Bool)
    (S : Bank) (saved output : List Bool) (hS : S i = []) :
    advance (program sign) (cfg (some (.emit i)) v S saved output) =
      cfg (some (.begin ⟨i.val + 1, by omega⟩)) none S (false :: saved) output := by
  simp only [advance, cfg, TM2.step, program, TM2.stepAux, contents, dif_pos i.isLt,
    hS, List.head?_nil, List.tail_nil, Option.isSome_none, cond_false, Option.getD_some]
  congr 1
  funext k
  fin_cases k <;> fin_cases i <;> simp_all [contents, Function.update_apply]

theorem emit_word (sign : Fin 3 → Bool) (i : Fin 3) (v : Option Bool)
    (S : Bank) (word saved output : List Bool) (hS : S i = word) :
    run sign (word.length + 1) (cfg (some (.emit i)) v S saved output) =
      cfg (some (.begin ⟨i.val + 1, by omega⟩)) none (Function.update S i [])
        ((field word).reverse ++ saved) output := by
  induction word generalizing v S saved with
  | nil =>
      rw [show ([] : List Bool).length + 1 = 0 + 1 by rfl, run_succ, emit_nil sign i v S _ _ hS]
      have hu : Function.update S i [] = S := by rw [← hS, Function.update_eq_self]
      simp [run, hu, field]
  | cons b word ih =>
      rw [List.length_cons, run_succ, emit_cons sign i v S b word _ _ hS,
        ih _ _ _ (Function.update_self _ _ _)]
      simp [field, List.reverse_cons, List.append_assoc, Function.update_idem]

theorem one_literal (sign : Fin 3 → Bool) (i : Fin 3) (v : Option Bool)
    (S : Bank) (saved output : List Bool) :
    run sign ((S i).length + 2)
      (cfg (some (.begin ⟨i.val, by omega⟩)) v S saved output) =
      cfg (some (.begin ⟨i.val + 1, by omega⟩)) none (Function.update S i [])
        ((sign i :: field (S i)).reverse ++ saved) output := by
  rw [show (S i).length + 2 = ((S i).length + 1) + 1 by omega,
    run_succ, begin_step, emit_word sign i v S (S i) _ _ rfl]
  simp [List.reverse_cons, List.append_assoc]

theorem finish_cons (sign : Fin 3 → Bool) (v : Option Bool) (S : Bank)
    (b : Bool) (q output : List Bool) :
    advance (program sign) (cfg (some .finish) v S (b :: q) output) =
      cfg (some .finish) (some b) S q (b :: output) := by
  simp [advance, cfg, TM2.step, program, TM2.stepAux, contents]
  congr 1
  funext k
  fin_cases k <;> rfl

theorem finish_nil (sign : Fin 3 → Bool) (v : Option Bool) (S : Bank)
    (output : List Bool) :
    advance (program sign) (cfg (some .finish) v S [] output) = cfg none none S [] output := by
  simp [advance, cfg, TM2.step, program, TM2.stepAux, contents]

theorem finish_run (sign : Fin 3 → Bool) (v : Option Bool) (S : Bank)
    (saved output : List Bool) :
    run sign (saved.length + 1) (cfg (some .finish) v S saved output) =
      cfg none none S [] (saved.reverse ++ output) := by
  induction saved generalizing v output with
  | nil =>
      change run sign (0 + 1) (cfg (some .finish) v S [] output) = cfg none none S [] output
      rw [run_succ, finish_nil]
      rfl
  | cons b q ih =>
      rw [List.length_cons, run_succ, finish_cons, ih]
      simp [List.reverse_cons, List.append_assoc]

def clauseBits (sign : Fin 3 → Bool) (S : Bank) : List Bool :=
  (sign 0 :: field (S 0)) ++ (sign 1 :: field (S 1)) ++ (sign 2 :: field (S 2))

def emitTime (S : Bank) : ℕ := (S 0).length + 2 + ((S 1).length + 2 + ((S 2).length + 2))

theorem emit_clause (sign : Fin 3 → Bool) (v : Option Bool) (S : Bank)
    (saved output : List Bool) :
    run sign (emitTime S) (cfg (some (.begin 0)) v S saved output) =
      cfg (some (.begin 3)) none (fun _ => []) ((clauseBits sign S).reverse ++ saved) output := by
  let S₀ := Function.update S 0 []
  let S₁ := Function.update S₀ 1 []
  have hs₀ : S₀ 1 = S 1 := by simp [S₀]
  have hs₁ : S₁ 2 = S 2 := by simp [S₁, S₀]
  have hempty : Function.update S₁ 2 [] = fun _ => [] := by
    funext i
    fin_cases i <;> simp [S₁, S₀]
  have h₀ := one_literal sign 0 v S saved output
  have h₁ := one_literal sign 1 none S₀ ((sign 0 :: field (S 0)).reverse ++ saved) output
  have h₂ := one_literal sign 2 none S₁
    ((sign 1 :: field (S₀ 1)).reverse ++ ((sign 0 :: field (S 0)).reverse ++ saved)) output
  change run sign ((S 0).length + 2) (cfg (some (.begin 0)) v S saved output) =
    cfg (some (.begin 1)) none S₀ ((sign 0 :: field (S 0)).reverse ++ saved) output at h₀
  change run sign ((S₀ 1).length + 2)
    (cfg (some (.begin 1)) none S₀ ((sign 0 :: field (S 0)).reverse ++ saved) output) =
    cfg (some (.begin 2)) none S₁
      ((sign 1 :: field (S₀ 1)).reverse ++ ((sign 0 :: field (S 0)).reverse ++ saved)) output at h₁
  change run sign ((S₁ 2).length + 2)
    (cfg (some (.begin 2)) none S₁
      ((sign 1 :: field (S₀ 1)).reverse ++ ((sign 0 :: field (S 0)).reverse ++ saved)) output) =
    cfg (some (.begin 3)) none (Function.update S₁ 2 [])
      ((sign 2 :: field (S₁ 2)).reverse ++
        ((sign 1 :: field (S₀ 1)).reverse ++ ((sign 0 :: field (S 0)).reverse ++ saved))) output at h₂
  unfold emitTime
  rw [run_add, h₀]
  change run sign ((S 1).length + 2 + ((S 2).length + 2))
    (cfg (some (.begin 1)) none S₀ _ output) = _
  rw [run_add, ← hs₀, h₁]
  rw [← hs₁, h₂, hempty]
  simp only [hs₀, hs₁, clauseBits, List.reverse_append, List.append_assoc]

theorem begin_end (sign : Fin 3 → Bool) (S : Bank) (saved output : List Bool) :
    advance (program sign) (cfg (some (.begin 3)) none S saved output) =
      cfg (some .finish) none S saved output := rfl

theorem clauseBits_length (sign : Fin 3 → Bool) (S : Bank) :
    (clauseBits sign S).length = 2 * ((S 0).length + (S 1).length + (S 2).length) + 6 := by
  simp only [clauseBits, List.length_append, List.length_cons, field_length]
  omega

/-- A complete physical clause write. All three source words are consumed,
the reversal buffer is cleared, and an arbitrary output suffix is retained. -/
theorem write_clause (sign : Fin 3 → Bool) (S : Bank) (output : List Bool) :
    run sign (3 * ((S 0).length + (S 1).length + (S 2).length) + 14)
      (cfg (some (.begin 0)) none S [] output) =
      cfg none none (fun _ => []) [] (clauseBits sign S ++ output) := by
  have ht : 3 * ((S 0).length + (S 1).length + (S 2).length) + 14 =
      emitTime S + ((clauseBits sign S).reverse.length + 1 + 1) := by
    simp only [List.length_reverse, clauseBits_length, emitTime]
    omega
  rw [ht, run_add, emit_clause, List.append_nil, run_succ, begin_end, finish_run,
    List.reverse_reverse]

def signs (c : EncodedCNF.Clause) : Fin 3 → Bool :=
  ![c.first.positive, c.second.positive, c.third.positive]

def words (c : EncodedCNF.Clause) : Bank :=
  ![c.first.variable.bits, c.second.variable.bits, c.third.variable.bits]

theorem clauseBits_eq (c : EncodedCNF.Clause) :
    clauseBits (signs c) (words c) = EncodedCNF.encodeClause c := rfl

/-- The emitted word is the existing CNF codec, not a substitute encoding. -/
theorem write_encoded_clause (c : EncodedCNF.Clause) (output : List Bool) :
    run (signs c) (3 * (c.first.variable.bits.length + c.second.variable.bits.length +
      c.third.variable.bits.length) + 14)
      (cfg (some (.begin 0)) none (words c) [] output) =
      cfg none none (fun _ => []) [] (EncodedCNF.encodeClause c ++ output) := by
  simpa only [clauseBits_eq, words, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two] using write_clause (signs c) (words c) output

end EthInapproximability.CurrentPaper.SourceLiteralWriter
