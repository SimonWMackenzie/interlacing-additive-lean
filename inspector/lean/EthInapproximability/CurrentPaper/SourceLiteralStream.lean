import EthInapproximability.CurrentPaper.SourceLiteralWriter

/-!
# Streaming clause emission without a per-clause global reversal

Source: frozen v8 `06-eth.tex`, explicit source output construction.
Each clause is prepended in reverse to a physical accumulator. Thus processing
clauses in their natural order produces the reverse of the entire CNF payload;
one final stack reversal restores the literal ordered codec.
-/

namespace EthInapproximability.CurrentPaper.SourceLiteralStream

open Turing BitMachineEncoding SourceLiteralWriter

def program (sign : Fin 3 → Bool) (l : Label) :
    TM2.Stmt (fun _ : Stack => Bool) Label (Option Bool) :=
  if l = .begin 3 then .halt else SourceLiteralWriter.program sign l

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
  have hi : (⟨i.val, by omega⟩ : Fin 4) ≠ 3 := by
    intro h
    have he : i.val = 3 := congrArg Fin.val h
    exact (Nat.ne_of_lt i.isLt) he
  simpa only [advance, cfg, TM2.step, program, Label.begin.injEq, hi, ↓reduceIte] using
    SourceLiteralWriter.begin_step sign i v S saved output

theorem emit_cons (sign : Fin 3 → Bool) (i : Fin 3) (v : Option Bool)
    (S : Bank) (b : Bool) (q saved output : List Bool) (hS : S i = b :: q) :
    advance (program sign) (cfg (some (.emit i)) v S saved output) =
      cfg (some (.emit i)) (some b) (Function.update S i q) (b :: true :: saved) output := by
  have hi : (.emit i : Label) ≠ .begin 3 := by intro h; cases h
  simpa only [advance, cfg, TM2.step, program, hi, ↓reduceIte] using
    SourceLiteralWriter.emit_cons sign i v S b q saved output hS

theorem emit_nil (sign : Fin 3 → Bool) (i : Fin 3) (v : Option Bool)
    (S : Bank) (saved output : List Bool) (hS : S i = []) :
    advance (program sign) (cfg (some (.emit i)) v S saved output) =
      cfg (some (.begin ⟨i.val + 1, by omega⟩)) none S (false :: saved) output := by
  have hi : (.emit i : Label) ≠ .begin 3 := by intro h; cases h
  simpa only [advance, cfg, TM2.step, program, hi, ↓reduceIte] using
    SourceLiteralWriter.emit_nil sign i v S saved output hS

theorem emit_word (sign : Fin 3 → Bool) (i : Fin 3) (v : Option Bool)
    (S : Bank) (word saved output : List Bool) (hS : S i = word) :
    run sign (word.length + 1) (cfg (some (.emit i)) v S saved output) =
      cfg (some (.begin ⟨i.val + 1, by omega⟩)) none (Function.update S i [])
        ((EncodedCommunication.field word).reverse ++ saved) output := by
  induction word generalizing v S saved with
  | nil =>
      rw [show ([] : List Bool).length + 1 = 0 + 1 by rfl, run_succ, emit_nil sign i v S _ _ hS]
      have hu : Function.update S i [] = S := by rw [← hS, Function.update_eq_self]
      simp [run, hu, EncodedCommunication.field]
  | cons b word ih =>
      rw [List.length_cons, run_succ, emit_cons sign i v S b word _ _ hS,
        ih _ _ _ (Function.update_self _ _ _)]
      simp [EncodedCommunication.field, List.reverse_cons, List.append_assoc, Function.update_idem]

theorem one_literal (sign : Fin 3 → Bool) (i : Fin 3) (v : Option Bool)
    (S : Bank) (saved output : List Bool) :
    run sign ((S i).length + 2)
      (cfg (some (.begin ⟨i.val, by omega⟩)) v S saved output) =
      cfg (some (.begin ⟨i.val + 1, by omega⟩)) none (Function.update S i [])
        ((sign i :: EncodedCommunication.field (S i)).reverse ++ saved) output := by
  rw [show (S i).length + 2 = ((S i).length + 1) + 1 by omega,
    run_succ, begin_step, emit_word sign i v S (S i) _ _ rfl]
  simp [List.reverse_cons, List.append_assoc]

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
  have h₁ := one_literal sign 1 none S₀ ((sign 0 :: EncodedCommunication.field (S 0)).reverse ++ saved) output
  have h₂ := one_literal sign 2 none S₁
    ((sign 1 :: EncodedCommunication.field (S₀ 1)).reverse ++
      ((sign 0 :: EncodedCommunication.field (S 0)).reverse ++ saved)) output
  change run sign ((S 0).length + 2) (cfg (some (.begin 0)) v S saved output) =
    cfg (some (.begin 1)) none S₀ ((sign 0 :: EncodedCommunication.field (S 0)).reverse ++ saved) output at h₀
  change run sign ((S₀ 1).length + 2)
    (cfg (some (.begin 1)) none S₀ ((sign 0 :: EncodedCommunication.field (S 0)).reverse ++ saved) output) =
    cfg (some (.begin 2)) none S₁
      ((sign 1 :: EncodedCommunication.field (S₀ 1)).reverse ++
        ((sign 0 :: EncodedCommunication.field (S 0)).reverse ++ saved)) output at h₁
  change run sign ((S₁ 2).length + 2)
    (cfg (some (.begin 2)) none S₁
      ((sign 1 :: EncodedCommunication.field (S₀ 1)).reverse ++
        ((sign 0 :: EncodedCommunication.field (S 0)).reverse ++ saved)) output) =
    cfg (some (.begin 3)) none (Function.update S₁ 2 [])
      ((sign 2 :: EncodedCommunication.field (S₁ 2)).reverse ++
        ((sign 1 :: EncodedCommunication.field (S₀ 1)).reverse ++
          ((sign 0 :: EncodedCommunication.field (S 0)).reverse ++ saved))) output at h₂
  unfold emitTime
  rw [run_add, h₀]
  change run sign ((S 1).length + 2 + ((S 2).length + 2))
    (cfg (some (.begin 1)) none S₀ _ output) = _
  rw [run_add, ← hs₀, h₁, ← hs₁, h₂, hempty]
  simp only [hs₀, hs₁, clauseBits, List.reverse_append, List.append_assoc]

theorem halt_step (sign : Fin 3 → Bool) (S : Bank) (saved output : List Bool) :
    advance (program sign) (cfg (some (.begin 3)) none S saved output) =
      cfg none none S saved output := by
  simp [advance, TM2.step, cfg, program, TM2.stepAux]

theorem stream_clause (c : EncodedCNF.Clause) (saved output : List Bool) :
    run (signs c) (emitTime (words c) + 1)
      (cfg (some (.begin 0)) none (words c) saved output) =
      cfg none none (fun _ => []) ((EncodedCNF.encodeClause c).reverse ++ saved) output := by
  rw [run_add, emit_clause, show 1 = 0 + 1 by rfl, run_succ, halt_step]
  simp only [run, Function.iterate_zero_apply, SourceLiteralWriter.clauseBits_eq]

end EthInapproximability.CurrentPaper.SourceLiteralStream
