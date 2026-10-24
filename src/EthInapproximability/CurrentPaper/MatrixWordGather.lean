import EthInapproximability.CurrentPaper.MatrixReadAt
import EthInapproximability.CurrentPaper.BitMachineSubroutine
import EthInapproximability.CurrentPaper.MatrixDuplicateRow

/-!
# A literal loop gathering a contiguous sampled word

The loop counter is a Boolean stack. Each iteration invokes the proved
nondestructive indexed reader, increments its unary address by one push,
and decrements the counter by one pop. The source array is preserved;
collected bits are prepended in reverse order to the existing output.

This is an actual finite TM2 controller, not a list-level loop-cost oracle.
The supplied start/width values below describe the initial unary stacks.
-/

namespace EthInapproximability.CurrentPaper.MatrixWordGather

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition BitMachineSubroutine

abbrev Label := MatrixReadAt.Label ⊕ Bool
abbrev Control := MatrixReadAt.Control × Bool
abbrev Config := TM2.Cfg (fun _ : Fin 7 ⊕ Fin 1 => Bool) Label Control

def baseControl : MatrixReadAt.Control := (none, none, (false, false), (false, false))

def program : Label → TM2.Stmt (fun _ : Fin 7 ⊕ Fin 1 => Bool) Label Control
  | .inl l => liftStmt (some true) (MatrixReadAt.program l)
  | .inr false => pop (.inr 0) (fun s b => (s.1, b.isSome))
      (branch Prod.snd (goto (fun _ => .inl (.inl BitMachineCopy.Label.scan))) halt)
  | .inr true => push (.inl 0) (fun _ => true)
      (load (fun s => (s.1, false)) (goto (fun _ => .inr false)))

def cfg (label : Option Label) (flag : Bool) (index source out counter : List Bool) : Config :=
  ⟨label, (baseControl, flag),
    Sum.elim (![index, [], [], source, [], out, []] : Fin 7 → List Bool) (fun _ => counter)⟩

def run (n : ℕ) (c : Config) := ((advance program)^[n]) c

private theorem run_succ {c d : Config} (h : TM2.step program c = some d) (n : ℕ) :
    run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : Config} {m : ℕ} (h : run m c = d) (n : ℕ) :
    run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem step_test_cons (flag : Bool) (idx source out counter : List Bool) :
    TM2.step program (cfg (some (.inr false)) flag idx source out (true :: counter)) =
      some (cfg (some (.inl (.inl BitMachineCopy.Label.scan))) true idx source out counter) := by
  apply congrArg (fun S => some (⟨some (.inl (.inl BitMachineCopy.Label.scan)), (baseControl, true), S⟩ : Config))
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

private theorem step_test_nil (flag : Bool) (idx source out : List Bool) :
    TM2.step program (cfg (some (.inr false)) flag idx source out []) =
      some (cfg none false idx source out []) := by
  apply congrArg (fun S => some (⟨none, (baseControl, false), S⟩ : Config))
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

private theorem step_increment (flag : Bool) (idx source out counter : List Bool) :
    TM2.step program (cfg (some (.inr true)) flag idx source out counter) =
      some (cfg (some (.inr false)) false (true :: idx) source out counter) := by
  apply congrArg (fun S => some (⟨some (.inr false), (baseControl, false), S⟩ : Config))
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

theorem body_run (i : ℕ) (flag : Bool) (source out counter : List Bool) :
    ∃ t ≤ 3 * i + 3 * source.length + 8,
      run t (cfg (some (.inl (.inl BitMachineCopy.Label.scan))) flag
        (List.replicate i true) source out counter) =
        cfg (some (.inr true)) flag (List.replicate i true) source
          (source[i]?.getD false :: out) counter := by
  obtain ⟨k, hk, hr⟩ := MatrixReadAt.readAt_run i source out
  have hh : (((advance MatrixReadAt.program)^[k])
      (MatrixReadAt.initial (List.replicate i true) source out)).l = none := by
    change (MatrixReadAt.run k _).l = none
    rw [hr]
    rfl
  obtain ⟨t, ht, hrun⟩ := lift_outputs MatrixReadAt.program program (some true)
    (fun _ => rfl) flag (fun _ : Fin 1 => counter)
    (MatrixReadAt.initial (List.replicate i true) source out) k hh
  refine ⟨t, ht.trans hk, ?_⟩
  change run t _ = _ at hrun
  change MatrixReadAt.run k _ = _ at hr
  change (((advance MatrixReadAt.program)^[k]) _) = _ at hr
  rw [hr] at hrun
  exact hrun

def word : ℕ → ℕ → List Bool → List Bool
  | _, 0, _ => []
  | start, width + 1, source => source[start]?.getD false :: word (start + 1) width source

@[simp] theorem word_length (start width : ℕ) (source : List Bool) :
    (word start width source).length = width := by
  induction width generalizing start with
  | zero => rfl
  | succ w ih => simp [word, ih]

theorem word_eq_ofFn (start width : ℕ) (source : List Bool) :
    word start width source = List.ofFn (fun j : Fin width => source[start + j.val]?.getD false) := by
  induction width generalizing start with
  | zero => simp [word]
  | succ w ih =>
      rw [word, List.ofFn_succ, ih]
      simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ]
      congr 1
      apply congrArg List.ofFn
      funext j
      rw [show start + 1 + j.val = start + (j.val + 1) by omega]

/-- The entire repeated-read loop, including tests and increments, has a
literal polynomial transition bound and preserves the source register. -/
theorem gather_run (width start : ℕ) (flag : Bool) (source out : List Bool) :
    ∃ t ≤ width * (3 * (start + width) + 3 * source.length + 10) + 1,
      run t (cfg (some (.inr false)) flag (List.replicate start true)
        source out (List.replicate width true)) =
        cfg none false (List.replicate (start + width) true) source
          ((word start width source).reverse ++ out) [] := by
  induction width generalizing start flag out with
  | zero =>
      refine ⟨1, by simp, ?_⟩
      simpa [word] using run_succ (step_test_nil flag (List.replicate start true) source out) 0
  | succ width ih =>
      have h₁ := run_succ (step_test_cons flag (List.replicate start true) source out
        (List.replicate width true)) 0
      obtain ⟨tb, htb, hb⟩ := body_run start true source out (List.replicate width true)
      have h₂ := run_succ (step_increment true (List.replicate start true) source
        (source[start]?.getD false :: out) (List.replicate width true)) 0
      obtain ⟨tr, htr, hr⟩ := ih (start + 1) false (source[start]?.getD false :: out)
      have hinc : true :: List.replicate start true = List.replicate (start + 1) true :=
        List.replicate_succ.symm
      rw [hinc] at h₂
      have h₁b := (run_add h₁ tb).trans hb
      have h₁b₂ := (run_add h₁b 1).trans h₂
      have hall := (run_add h₁b₂ tr).trans hr
      refine ⟨1 + tb + 1 + tr, ?_, ?_⟩
      · have he : start + 1 + width = start + (width + 1) := by omega
        rw [he] at htr
        nlinarith
      · simpa only [List.replicate_succ, word, List.reverse_cons, List.append_assoc,
          List.singleton_append, Nat.add_assoc, Nat.add_comm 1 width, Nat.zero_add] using hall

namespace Forward

inductive Admin where
  | test | increment | reverse
  deriving DecidableEq, Fintype

abbrev Stack := Fin 7 ⊕ Fin 2
abbrev Label := MatrixReadAt.Label ⊕ Admin
abbrev Control := MatrixReadAt.Control × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

/-- The source-preserving read loop writes to a reverse buffer. A final
literal transfer restores the sampled word's original bit order. -/
def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt (some .increment) (MatrixReadAt.program l)
  | .inr .test => pop (.inr 0) (fun s b => (s.1, b))
      (branch (fun s => s.2.isSome)
        (goto (fun _ => .inl (.inl BitMachineCopy.Label.scan)))
        (goto (fun _ => .inr .reverse)))
  | .inr .increment => push (.inl 0) (fun _ => true)
      (load (fun s => (s.1, none)) (goto (fun _ => .inr .test)))
  | .inr .reverse => pop (.inl 5) (fun s b => (s.1, b))
      (branch (fun s => s.2.isSome)
        (push (.inr 1) (fun s => s.2.getD false) (goto (fun _ => .inr .reverse))) halt)

def cfg (label : Option Label) (s : Option Bool)
    (index source buffer counter out : List Bool) : Config :=
  ⟨label, (baseControl, s),
    Sum.elim (![index, [], [], source, [], buffer, []] : Fin 7 → List Bool)
      (![counter, out] : Fin 2 → List Bool)⟩

def run (n : ℕ) (c : Config) := ((advance program)^[n]) c

private theorem run_succ {c d : Config} (h : TM2.step program c = some d) (n : ℕ) :
    run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : Config} {m : ℕ} (h : run m c = d) (n : ℕ) :
    run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem test_cons (s : Option Bool) (index source buffer counter out : List Bool) :
    TM2.step program (cfg (some (.inr .test)) s index source buffer (true :: counter) out) =
      some (cfg (some (.inl (.inl BitMachineCopy.Label.scan))) (some true)
        index source buffer counter out) := by
  apply congrArg (fun S => some (⟨some (.inl (.inl BitMachineCopy.Label.scan)),
    (baseControl, some true), S⟩ : Config))
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

private theorem test_nil (s : Option Bool) (index source buffer out : List Bool) :
    TM2.step program (cfg (some (.inr .test)) s index source buffer [] out) =
      some (cfg (some (.inr .reverse)) none index source buffer [] out) := by
  apply congrArg (fun S => some (⟨some (.inr .reverse), (baseControl, none), S⟩ : Config))
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

private theorem increment_step (s : Option Bool) (index source buffer counter out : List Bool) :
    TM2.step program (cfg (some (.inr .increment)) s index source buffer counter out) =
      some (cfg (some (.inr .test)) none (true :: index) source buffer counter out) := by
  apply congrArg (fun S => some (⟨some (.inr .test), (baseControl, none), S⟩ : Config))
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

private theorem reverse_step_symbolic (s : Control) (bank : Stack → List Bool)
    (b : Bool) (buffer : List Bool) (hb : bank (.inl 5) = b :: buffer) :
    TM2.step program ⟨some (.inr .reverse), s, bank⟩ =
      some ⟨some (.inr .reverse), (s.1, some b),
        Function.update (Function.update bank (.inl 5) buffer) (.inr 1)
          (b :: bank (.inr 1))⟩ := by
  simp only [TM2.step, program, TM2.stepAux, hb, List.head?_cons, List.tail_cons,
    Option.isSome_some, Option.getD_some,
    Function.update_of_ne (show (Sum.inr (1 : Fin 2) : Stack) ≠ .inl 5 by decide)]
  rfl

/-- Keep finite-bank rewriting separate from the symbolic TM2 transition:
this avoids duplicating the expanded instruction body in kernel conversion. -/
private theorem reverse_stack (b : Bool) (index source buffer out : List Bool) :
    Function.update
      (Function.update
        (Sum.elim (![index, [], [], source, [], b :: buffer, []] : Fin 7 → List Bool)
          (![( [] : List Bool), out] : Fin 2 → List Bool)) (.inl 5) buffer)
      (.inr 1) (b :: out) =
    Sum.elim (![index, [], [], source, [], buffer, []] : Fin 7 → List Bool)
      (![( [] : List Bool), b :: out] : Fin 2 → List Bool) := by
  funext k
  cases k with
  | inl k =>
      fin_cases k <;> norm_num only [Function.update_apply, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_succ, reduceCtorEq]
      all_goals split_ifs <;> simp_all
  | inr k =>
      fin_cases k <;> norm_num only [Function.update_apply, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_succ, reduceCtorEq]
      all_goals split_ifs <;> simp_all

private theorem reverse_cons (s : Option Bool) (b : Bool)
    (index source buffer out : List Bool) :
    TM2.step program (cfg (some (.inr .reverse)) s index source (b :: buffer) [] out) =
      some (cfg (some (.inr .reverse)) (some b) index source buffer [] (b :: out)) := by
  exact (reverse_step_symbolic (baseControl, s) _ b buffer rfl).trans
    (congrArg (fun S => some
      (⟨some (.inr .reverse), (baseControl, some b), S⟩ : Config))
      (reverse_stack b index source buffer out))

private theorem reverse_nil (s : Option Bool) (index source out : List Bool) :
    TM2.step program (cfg (some (.inr .reverse)) s index source [] [] out) =
      some (cfg none none index source [] [] out) := by
  apply congrArg (fun S => some (⟨none, (baseControl, none), S⟩ : Config))
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

theorem reverse_run (s : Option Bool) (index source buffer out : List Bool) :
    run (buffer.length + 1) (cfg (some (.inr .reverse)) s index source buffer [] out) =
      cfg none none index source [] [] (buffer.reverse ++ out) := by
  induction buffer generalizing s out with
  | nil => simpa using run_succ (reverse_nil s index source out) 0
  | cons b buffer ih =>
      rw [List.length_cons, run_succ (reverse_cons _ _ _ _ _ _) _]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
        ih (some b) (b :: out)

theorem body_run (i : ℕ) (s : Option Bool) (source buffer counter out : List Bool) :
    ∃ t ≤ 3 * i + 3 * source.length + 8,
      run t (cfg (some (.inl (.inl BitMachineCopy.Label.scan))) s
        (List.replicate i true) source buffer counter out) =
        cfg (some (.inr .increment)) s (List.replicate i true) source
          (source[i]?.getD false :: buffer) counter out := by
  obtain ⟨k, hk, hr⟩ := MatrixReadAt.readAt_run i source buffer
  have hh : (((advance MatrixReadAt.program)^[k])
      (MatrixReadAt.initial (List.replicate i true) source buffer)).l = none := by
    change (MatrixReadAt.run k _).l = none
    rw [hr]
    rfl
  obtain ⟨t, ht, hrun⟩ := lift_outputs MatrixReadAt.program program (some .increment)
    (fun _ => rfl) s (![counter, out] : Fin 2 → List Bool)
    (MatrixReadAt.initial (List.replicate i true) source buffer) k hh
  refine ⟨t, ht.trans hk, ?_⟩
  change run t _ = _ at hrun
  change (((advance MatrixReadAt.program)^[k]) _) = _ at hr
  rw [hr] at hrun
  exact hrun

theorem loop_run (width start : ℕ) (s : Option Bool) (source buffer out : List Bool) :
    ∃ t ≤ width * (3 * (start + width) + 3 * source.length + 10) + 1,
      run t (cfg (some (.inr .test)) s (List.replicate start true)
        source buffer (List.replicate width true) out) =
        cfg (some (.inr .reverse)) none (List.replicate (start + width) true) source
          ((word start width source).reverse ++ buffer) [] out := by
  induction width generalizing start s buffer with
  | zero =>
      refine ⟨1, by simp, ?_⟩
      simpa [word] using run_succ (test_nil s (List.replicate start true) source buffer out) 0
  | succ width ih =>
      have h₁ := run_succ (test_cons s (List.replicate start true) source buffer
        (List.replicate width true) out) 0
      obtain ⟨tb, htb, hb⟩ := body_run start (some true) source buffer (List.replicate width true) out
      have h₂ := run_succ (increment_step (some true) (List.replicate start true) source
        (source[start]?.getD false :: buffer) (List.replicate width true) out) 0
      rw [show true :: List.replicate start true = List.replicate (start + 1) true
        from List.replicate_succ.symm] at h₂
      obtain ⟨tr, htr, hr⟩ := ih (start + 1) none (source[start]?.getD false :: buffer)
      have hall := (run_add ((run_add ((run_add h₁ tb).trans hb) 1).trans h₂) tr).trans hr
      have he : start + 1 + width = start + (width + 1) := by omega
      refine ⟨1 + tb + 1 + tr, ?_, ?_⟩
      · rw [he] at htr
        nlinarith
      · simpa only [List.replicate_succ, word, List.reverse_cons, List.append_assoc,
          List.singleton_append, Nat.zero_add, he] using hall

theorem gather_run (width start : ℕ) (source out : List Bool) :
    ∃ t ≤ width * (3 * (start + width) + 3 * source.length + 11) + 2,
      run t (cfg (some (.inr .test)) none (List.replicate start true)
        source [] (List.replicate width true) out) =
        cfg none none (List.replicate (start + width) true) source [] []
          (word start width source ++ out) := by
  obtain ⟨t, ht, hr⟩ := loop_run width start none source [] out
  simp only [List.append_nil] at hr
  have hrev := reverse_run none (List.replicate (start + width) true) source
    (word start width source).reverse out
  simp only [List.length_reverse, word_length, List.reverse_reverse] at hrev
  refine ⟨t + (width + 1), ?_, (run_add hr _).trans hrev⟩
  clear hr hrev
  nlinarith

/-- The actual loop reads the selected field-element word from the literal
flat second-family payload, in the original bit order. -/
theorem stored_word_run {a d N₁ N₂ n : ℕ}
    (C₁ : ExactConstruction.FirstFamily a N₁) (C₂ : ExactConstruction.SecondFamily a d N₂)
    (v : Fin n → Fin d → Bool) (z : Fin N₂) (α : Fin d) (out : List Bool) :
    let start := (z.val * d + α.val) * a
    let source := (MatrixMaterialization.storeBits C₁ C₂ v).second
    ∃ t ≤ a * (3 * (start + a) + 3 * source.length + 11) + 2,
      run t (cfg (some (.inr .test)) none (List.replicate start true)
        source [] (List.replicate a true) out) =
        cfg none none (List.replicate (start + a) true) source [] []
          (List.ofFn ((MatrixMaterialization.wordCode a).symm (C₂ z α)) ++ out) := by
  dsimp only
  have hw : word ((z.val * d + α.val) * a) a
      (MatrixMaterialization.storeBits C₁ C₂ v).second =
        List.ofFn ((MatrixMaterialization.wordCode a).symm (C₂ z α)) := by
    rw [word_eq_ofFn]
    apply congrArg List.ofFn
    funext j
    simp only [MatrixMaterialization.storeBits_second_entry, Option.getD_some]
  simpa only [hw] using gather_run a ((z.val * d + α.val) * a)
    (MatrixMaterialization.storeBits C₁ C₂ v).second out

/-- Gather just the first-family prefix, excluding its three tail bits. -/
theorem stored_prefix_run {a d N₁ N₂ n : ℕ}
    (C₁ : ExactConstruction.FirstFamily a N₁) (C₂ : ExactConstruction.SecondFamily a d N₂)
    (v : Fin n → Fin d → Bool) (ℓ : Fin N₁) (out : List Bool) :
    let q := ExactConstruction.prefixLength a
    let start := ℓ.val * (q + 3)
    let source := (MatrixMaterialization.storeBits C₁ C₂ v).first
    ∃ t ≤ q * (3 * (start + q) + 3 * source.length + 11) + 2,
      run t (cfg (some (.inr .test)) none (List.replicate start true)
        source [] (List.replicate q true) out) =
        cfg none none (List.replicate (start + q) true) source [] []
          (MatrixDuplicateRow.prefixWord C₁ ℓ ++ out) := by
  dsimp only
  have hw : word (ℓ.val * (ExactConstruction.prefixLength a + 3))
      (ExactConstruction.prefixLength a) (MatrixMaterialization.storeBits C₁ C₂ v).first =
        MatrixDuplicateRow.prefixWord C₁ ℓ := by
    rw [word_eq_ofFn]
    apply congrArg List.ofFn
    funext j
    have h := MatrixMaterialization.rowMajor_entry C₁ ℓ (ExactConstruction.prefixCoordinate a j)
    simpa only [MatrixMaterialization.storeBits, ExactConstruction.prefixCoordinate,
      Fin.val_castAdd, Option.getD_some] using
      congrArg (fun b : Option Bool => b.getD false) h
  simpa only [hw] using gather_run (ExactConstruction.prefixLength a)
    (ℓ.val * (ExactConstruction.prefixLength a + 3))
    (MatrixMaterialization.storeBits C₁ C₂ v).first out

end Forward

end EthInapproximability.CurrentPaper.MatrixWordGather
