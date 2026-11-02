import EthInapproximability.CurrentPaper.MatrixBinaryAddress
import EthInapproximability.CurrentPaper.BitMachineSubroutine

/-!
# Finite-stack execution of a template-row entry

The sampled binary label is decoded by the literal address machine while
the selected first-family row is retained in a foreign stack bank. The
controller then skips the unary address, reads that bit, and clears its
working data. Its input is a binary label and an explicitly duplicated
first-family row, not the answer bit or a supplied numeric address.

The full materializer must still select these two words from its family
tables and enumerate the output positions. The entry theorem below does
not treat those operations as free or claim a whole-materializer runtime.
-/

namespace EthInapproximability.CurrentPaper.MatrixTemplateMachine

set_option maxRecDepth 2048

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition BitMachineSubroutine

inductive LookupLabel where
  | skip | readBit | clear | finish
  deriving DecidableEq, Fintype

abbrev Stack := Fin 3 ⊕ Fin 2
abbrev Label := MatrixBinaryAddress.Label ⊕ LookupLabel
abbrev Control := (Bool × Bool) × (Bool × Bool)
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt (some .skip) (MatrixBinaryAddress.program l)
  | .inr .skip => pop (.inl 0) (fun s b => (s.1, s.2.1, b.isSome))
      (branch (fun s => s.2.2)
        (pop (.inr 0) (fun s _ => s) (goto (fun _ => .inr .skip)))
        (goto (fun _ => .inr .readBit)))
  | .inr .readBit => pop (.inr 0) (fun s b => (s.1, b.getD false, s.2.2))
      (goto (fun _ => .inr .clear))
  | .inr .clear => pop (.inr 0) (fun s b => (s.1, s.2.1, b.isSome))
      (branch (fun s => s.2.2) (goto (fun _ => .inr .clear))
        (goto (fun _ => .inr .finish)))
  | .inr .finish => push (.inr 1) (fun s => s.2.1)
      (load (fun _ => ((false, false), (false, false))) halt)

def foreign (row output : List Bool) : Fin 2 → List Bool :=
  fun k => if k = 0 then row else output

@[simp] private theorem foreign_zero (q o : List Bool) : foreign q o 0 = q := rfl
@[simp] private theorem foreign_one (q o : List Bool) : foreign q o 1 = o := rfl

def cfg (l : Option Label) (s : Control) (index row output : List Bool) : Config :=
  ⟨l, s, Sum.elim (MatrixBinaryAddress.stackContents index [] []) (foreign row output)⟩

def run (n : ℕ) (c : Config) := ((advance program)^[n]) c

private theorem run_succ {c d : Config} (h : TM2.step program c = some d) (n : ℕ) :
    run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : Config} {m : ℕ} (h : run m c = d) (n : ℕ) :
    run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem step_skip_cons (s : Control) (idx row out : List Bool) :
    TM2.step program (cfg (some (.inr .skip)) s (true :: idx) row out) =
      some (cfg (some (.inr .skip)) (s.1, s.2.1, true) idx row.tail out) := by
  apply congrArg (fun S => some (⟨some (.inr .skip), (s.1, s.2.1, true), S⟩ : Config))
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

private theorem step_skip_nil (s : Control) (row out : List Bool) :
    TM2.step program (cfg (some (.inr .skip)) s [] row out) =
      some (cfg (some (.inr .readBit)) (s.1, s.2.1, false) [] row out) := by
  apply congrArg (fun S => some (⟨some (.inr .readBit), (s.1, s.2.1, false), S⟩ : Config))
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

private theorem step_read (s : Control) (row out : List Bool) :
    TM2.step program (cfg (some (.inr .readBit)) s [] row out) =
      some (cfg (some (.inr .clear)) (s.1, row.head?.getD false, s.2.2) [] row.tail out) := by
  apply congrArg (fun S => some (⟨some (.inr .clear), (s.1, row.head?.getD false, s.2.2), S⟩ : Config))
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

private theorem step_clear_cons (s : Control) (b : Bool) (row out : List Bool) :
    TM2.step program (cfg (some (.inr .clear)) s [] (b :: row) out) =
      some (cfg (some (.inr .clear)) (s.1, s.2.1, true) [] row out) := by
  apply congrArg (fun S => some (⟨some (.inr .clear), (s.1, s.2.1, true), S⟩ : Config))
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

private theorem step_clear_nil (s : Control) (out : List Bool) :
    TM2.step program (cfg (some (.inr .clear)) s [] [] out) =
      some (cfg (some (.inr .finish)) (s.1, s.2.1, false) [] [] out) := by
  apply congrArg (fun S => some (⟨some (.inr .finish), (s.1, s.2.1, false), S⟩ : Config))
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

private theorem step_finish (s : Control) (out : List Bool) :
    TM2.step program (cfg (some (.inr .finish)) s [] [] out) =
      some (cfg none ((false, false), (false, false)) [] [] (s.2.1 :: out)) := by
  apply congrArg (fun S => some (⟨none, ((false, false), (false, false)), S⟩ : Config))
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

theorem skip_correct (i : ℕ) (s : Control) (row out : List Bool) :
    run (i + 1) (cfg (some (.inr .skip)) s (List.replicate i true) row out) =
      cfg (some (.inr .readBit)) (s.1, s.2.1, false) [] (row.drop i) out := by
  induction i generalizing row s with
  | zero => simpa using run_succ (step_skip_nil s row out) 0
  | succ i ih =>
      rw [List.replicate_succ, run_succ (step_skip_cons _ _ _ _) _]
      simpa only [List.drop_tail] using ih (s.1, s.2.1, true) row.tail

theorem clear_correct (s : Control) (row out : List Bool) :
    run (row.length + 2) (cfg (some (.inr .clear)) s [] row out) =
      cfg none ((false, false), (false, false)) [] [] (s.2.1 :: out) := by
  induction row generalizing s with
  | nil =>
      change run (1 + 1) _ = _
      rw [run_succ (step_clear_nil _ _) 1, run_succ (step_finish _ _) 0]
      rfl
  | cons b row ih =>
      rw [List.length_cons, run_succ (step_clear_cons _ _ _ _) _]
      exact ih (s.1, s.2.1, true)

theorem lookup_correct (i : ℕ) (s : Control) (row out : List Bool) :
    run (i + 4 + (row.drop i).tail.length)
      (cfg (some (.inr .skip)) s (List.replicate i true) row out) =
      cfg none ((false, false), (false, false)) [] [] (row[i]?.getD false :: out) := by
  have h₁ := skip_correct i s row out
  have h₂ := run_succ (step_read (s.1, s.2.1, false) (row.drop i) out) 0
  have h₃ := clear_correct (s.1, (row.drop i).head?.getD false, false) (row.drop i).tail out
  have h := (run_add ((run_add h₁ 1).trans h₂) ((row.drop i).tail.length + 2)).trans h₃
  have ht : (i + 1) + 1 + ((row.drop i).tail.length + 2) = i + 4 + (row.drop i).tail.length := by omega
  simpa only [ht, List.head?_drop] using h

def initial (bits row out : List Bool) : Config :=
  liftCfg (some LookupLabel.skip) (false, false) (foreign row out)
    (MatrixBinaryAddress.cfg (some .readBit) (false, false) bits [] [])

theorem query_run (bits row out : List Bool) :
    ∃ t ≤ 5 * MatrixBinaryAddress.valueFrom 0 bits + 3 * bits.length + row.length + 6,
      run t (initial bits row out) =
        cfg none ((false, false), (false, false)) [] []
          (row[MatrixBinaryAddress.valueFrom 0 bits]?.getD false :: out) := by
  let c := MatrixBinaryAddress.cfg (some .readBit) (false, false) bits [] []
  have hr := MatrixBinaryAddress.run_correct bits 0 (false, false)
  simp only [List.replicate_zero, MatrixBinaryAddress.run] at hr
  have hh : (((advance MatrixBinaryAddress.program)^[MatrixBinaryAddress.workFrom 0 bits]) c).l = none := by
    rw [show c = MatrixBinaryAddress.cfg (some .readBit) (false, false) bits [] [] from rfl, hr]
    rfl
  obtain ⟨k, hk, hrun⟩ := lift_outputs MatrixBinaryAddress.program program
    (some LookupLabel.skip) (fun _ => rfl) (false, false) (foreign row out) c
    (MatrixBinaryAddress.workFrom 0 bits) hh
  rw [show c = MatrixBinaryAddress.cfg (some .readBit) (false, false) bits [] [] from rfl, hr] at hrun
  change run k (initial bits row out) =
    cfg (some (.inr .skip)) ((false, false), (false, false))
      (List.replicate (MatrixBinaryAddress.valueFrom 0 bits) true) row out at hrun
  let j := MatrixBinaryAddress.valueFrom 0 bits
  refine ⟨k + (j + 4 + (row.drop j).tail.length), ?_, ?_⟩
  · have hw := MatrixBinaryAddress.workFrom_bound 0 bits
    have hlen : (row.drop j).tail.length ≤ row.length := by
      simp only [List.length_tail, List.length_drop]
      omega
    dsimp [j] at *
    omega
  · exact (run_add hrun _).trans (lookup_correct j _ row out)

theorem sampled_label_run {a : ℕ} (label : Fin (2 ^ a)) (row out : List Bool) :
    ∃ t ≤ 5 * label.val + 3 * a + row.length + 6,
      run t (initial (List.ofFn ((MatrixMaterialization.wordCode a).symm label)) row out) =
        cfg none ((false, false), (false, false)) [] [] (row[label.val]?.getD false :: out) := by
  have hv : MatrixBinaryAddress.valueFrom 0
      (List.ofFn ((MatrixMaterialization.wordCode a).symm label)) = label.val := by
    rw [MatrixBinaryAddress.valueFrom_wordCode, Equiv.apply_symm_apply]
  simpa only [hv, List.length_ofFn] using
    query_run (List.ofFn ((MatrixMaterialization.wordCode a).symm label)) row out

def duplicatedRow {a N₁ : ℕ} (ha : 2 ≤ a) (C₁ : ExactConstruction.FirstFamily a N₁)
    (ℓ : Fin N₁) : List Bool :=
  List.ofFn (fun j : Fin (2 ^ a) =>
    C₁ ℓ (ExactConstruction.prefixCoordinate a (ExactConstruction.duplicateLabel a ha j)))

theorem duplicatedRow_entry {a N₁ : ℕ} (ha : 2 ≤ a)
    (C₁ : ExactConstruction.FirstFamily a N₁) (ℓ : Fin N₁) (j : Fin (2 ^ a)) :
    (duplicatedRow ha C₁ ℓ)[j.val]?.getD false =
      C₁ ℓ (ExactConstruction.prefixCoordinate a (ExactConstruction.duplicateLabel a ha j)) := by
  simp [duplicatedRow, j.isLt]

/-- Both selected words are genuine sampled data. The machine computes the
numeric label and performs the selection; the caller supplies no answer. -/
theorem template_matrix_run {a d N₁ N₂ n : ℕ} (ha : 2 ≤ a)
    (C₁ : ExactConstruction.FirstFamily a N₁) (C₂ : ExactConstruction.SecondFamily a d N₂)
    (v : Fin n → Fin d → Bool)
    (cap : ∀ α, (Construction.activeItems v α).card ≤ 2)
    (p : Fin 4) (z : Fin N₂) (c : ExactConstruction.Columns d N₁) (out : List Bool) :
    ∃ t ≤ 6 * 2 ^ a + 3 * a + 6,
      run t (initial
        (List.ofFn ((MatrixMaterialization.wordCode a).symm (C₂ z (c.2 p).1)))
        (duplicatedRow ha C₁ (c.2 p).2) out) =
        cfg none ((false, false), (false, false)) [] []
          (ExactConstruction.matrix ha C₁ C₂ v cap (.inl (p, z)) c :: out) := by
  obtain ⟨t, ht, hr⟩ := sampled_label_run (C₂ z (c.2 p).1)
    (duplicatedRow ha C₁ (c.2 p).2) out
  refine ⟨t, ?_, ?_⟩
  · have hj := (C₂ z (c.2 p).1).isLt
    simp only [duplicatedRow, List.length_ofFn] at ht
    change (C₂ z (c.2 p).1).val < 2 ^ a at hj
    omega
  · rw [duplicatedRow_entry] at hr
    exact hr

end EthInapproximability.CurrentPaper.MatrixTemplateMachine
