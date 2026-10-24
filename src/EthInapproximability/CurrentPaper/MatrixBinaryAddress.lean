import EthInapproximability.CurrentPaper.MatrixMaterialization

/-!
# Literal conversion of a sampled binary label to a unary address

The matrix's second family supplies `a`-bit numeric labels. This fixed
three-Boolean-stack machine reads their big-endian bits and constructs the
unary address by repeated doubling. Both the doubling and transfer passes
are literal stack operations with proved transition counts.

The bound is output-sensitive, not polynomial in the binary word length
alone. The exact construction already contains a first-family word of
width approximately `2^a`; using that fact to price the complete matrix
controller is a separate composition obligation.
-/

namespace EthInapproximability.CurrentPaper.MatrixBinaryAddress

open Turing Turing.TM2.Stmt BitMachineEncoding

def bitVal (b : Bool) : ℕ := if b then 1 else 0

def valueFrom : ℕ → List Bool → ℕ
  | n, [] => n
  | n, b :: q => valueFrom (2 * n + bitVal b) q

def workFrom : ℕ → List Bool → ℕ
  | n, [] => n + 2
  | n, b :: q => 3 * n + bitVal b + 3 + workFrom (2 * n + bitVal b) q

theorem workFrom_bound (n : ℕ) (q : List Bool) :
    workFrom n q + 3 * n ≤ 4 * valueFrom n q + 3 * q.length + 2 := by
  induction q generalizing n with
  | nil => simp only [workFrom, valueFrom, List.length_nil]; omega
  | cons b q ih =>
      have h := ih (2 * n + bitVal b)
      simp only [workFrom, valueFrom, List.length_cons]
      omega

inductive Label where
  | readBit | double | transfer | finish
  deriving DecidableEq, Fintype

def program : Label → TM2.Stmt (fun _ : Fin 3 => Bool) Label (Bool × Bool)
  | .readBit => pop 0 (fun _ b => (b.getD false, b.isSome))
      (branch Prod.snd (goto (fun _ => .double)) (goto (fun _ => .finish)))
  | .double => pop 1 (fun s b => (s.1, b.isSome))
      (branch Prod.snd
        (push 2 (fun _ => true) (push 2 (fun _ => true) (goto (fun _ => .double))))
        (branch Prod.fst
          (push 2 (fun _ => true) (goto (fun _ => .transfer)))
          (goto (fun _ => .transfer))))
  | .transfer => pop 2 (fun s b => (s.1, b.isSome))
      (branch Prod.snd
        (push 1 (fun _ => true) (goto (fun _ => .transfer)))
        (goto (fun _ => .readBit)))
  | .finish => pop 1 (fun s b => (s.1, b.isSome))
      (branch Prod.snd
        (push 0 (fun _ => true) (goto (fun _ => .finish)))
        (load (fun _ => (false, false)) halt))

def stackContents (q counter scratch : List Bool) : Fin 3 → List Bool :=
  fun k => if k = 0 then q else if k = 1 then counter else scratch

@[simp] private theorem stack_zero (q c b : List Bool) : stackContents q c b 0 = q := rfl
@[simp] private theorem stack_one (q c b : List Bool) : stackContents q c b 1 = c := rfl
@[simp] private theorem stack_two (q c b : List Bool) : stackContents q c b 2 = b := rfl

def cfg (l : Option Label) (s : Bool × Bool) (q c b : List Bool) :
    TM2.Cfg (fun _ : Fin 3 => Bool) Label (Bool × Bool) := ⟨l, s, stackContents q c b⟩

def run (n : ℕ) (c : TM2.Cfg (fun _ : Fin 3 => Bool) Label (Bool × Bool)) :=
  ((advance program)^[n]) c

private theorem run_succ {c d : TM2.Cfg (fun _ : Fin 3 => Bool) Label (Bool × Bool)}
    (h : TM2.step program c = some d) (n : ℕ) : run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : TM2.Cfg (fun _ : Fin 3 => Bool) Label (Bool × Bool)}
    {m : ℕ} (h : run m c = d) (n : ℕ) : run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem step_read_cons (s : Bool × Bool) (b : Bool) (q c : List Bool) :
    TM2.step program (cfg (some .readBit) s (b :: q) c []) =
      some (cfg (some .double) (b, true) q c []) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

private theorem step_read_nil (s : Bool × Bool) (c : List Bool) :
    TM2.step program (cfg (some .readBit) s [] c []) =
      some (cfg (some .finish) (false, false) [] c []) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

private theorem step_double_cons (s : Bool × Bool) (q c b : List Bool) :
    TM2.step program (cfg (some .double) s q (true :: c) b) =
      some (cfg (some .double) (s.1, true) q c (true :: true :: b)) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

private theorem step_double_nil (s : Bool × Bool) (q b : List Bool) :
    TM2.step program (cfg (some .double) s q [] b) =
      some (cfg (some .transfer) (s.1, false) q []
        (List.replicate (bitVal s.1) true ++ b)) := by
  rcases s with ⟨s, flag⟩
  cases s <;> simp [TM2.step, TM2.stepAux, program, cfg, bitVal]
  funext k
  fin_cases k <;> rfl

private theorem step_transfer_cons (s : Bool × Bool) (q c b : List Bool) :
    TM2.step program (cfg (some .transfer) s q c (true :: b)) =
      some (cfg (some .transfer) (s.1, true) q (true :: c) b) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

private theorem step_transfer_nil (s : Bool × Bool) (q c : List Bool) :
    TM2.step program (cfg (some .transfer) s q c []) =
      some (cfg (some .readBit) (s.1, false) q c []) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

private theorem step_finish_cons (s : Bool × Bool) (q c : List Bool) :
    TM2.step program (cfg (some .finish) s q (true :: c) []) =
      some (cfg (some .finish) (s.1, true) (true :: q) c []) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

private theorem step_finish_nil (s : Bool × Bool) (q : List Bool) :
    TM2.step program (cfg (some .finish) s q [] []) =
      some (cfg none (false, false) q [] []) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

theorem double_correct (n m : ℕ) (s : Bool × Bool) (q : List Bool) :
    run (n + 1) (cfg (some .double) s q (List.replicate n true) (List.replicate m true)) =
      cfg (some .transfer) (s.1, false) q []
        (List.replicate (2 * n + m + bitVal s.1) true) := by
  induction n generalizing s m with
  | zero =>
      simpa only [List.replicate_zero, Nat.mul_zero, Nat.zero_add, ← List.replicate_add,
        Nat.add_comm m] using run_succ (step_double_nil s q (List.replicate m true)) 0
  | succ n ih =>
      rw [List.replicate_succ, run_succ (step_double_cons _ _ _ _) _]
      have h := ih (m + 2) (s.1, true)
      simpa only [List.replicate_add, List.replicate_succ, List.replicate_zero,
        List.append_cons, List.append_nil, Nat.mul_add, Nat.mul_one,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem transfer_correct (n m : ℕ) (s : Bool × Bool) (q : List Bool) :
    run (n + 1) (cfg (some .transfer) s q (List.replicate m true) (List.replicate n true)) =
      cfg (some .readBit) (s.1, false) q (List.replicate (n + m) true) [] := by
  induction n generalizing s m with
  | zero => simpa using run_succ (step_transfer_nil s q (List.replicate m true)) 0
  | succ n ih =>
      rw [List.replicate_succ, run_succ (step_transfer_cons _ _ _ _) _]
      simpa only [← List.replicate_succ, Nat.add_assoc, Nat.add_comm 1 m] using
        ih (m + 1) (s.1, true)

theorem finish_correct (n m : ℕ) (s : Bool × Bool) :
    run (n + 1) (cfg (some .finish) s (List.replicate m true) (List.replicate n true) []) =
      cfg none (false, false) (List.replicate (n + m) true) [] [] := by
  induction n generalizing s m with
  | zero => simpa using run_succ (step_finish_nil s (List.replicate m true)) 0
  | succ n ih =>
      rw [List.replicate_succ, run_succ (step_finish_cons _ _ _) _]
      simpa only [← List.replicate_succ, Nat.add_assoc, Nat.add_comm 1 m] using
        ih (m + 1) (s.1, true)

theorem run_correct (q : List Bool) (n : ℕ) (s : Bool × Bool) :
    run (workFrom n q) (cfg (some .readBit) s q (List.replicate n true) []) =
      cfg none (false, false) (List.replicate (valueFrom n q) true) [] [] := by
  induction q generalizing n s with
  | nil =>
      rw [workFrom, show n + 2 = (n + 1) + 1 by omega,
        run_succ (step_read_nil _ _) _]
      simpa only [Nat.add_zero] using finish_correct n 0 (false, false)
  | cons b q ih =>
      have h₁ := run_succ (step_read_cons s b q (List.replicate n true)) 0
      have h₂ := double_correct n 0 (b, true) q
      simp only [List.replicate_zero, Nat.add_zero] at h₂
      have h₃ := transfer_correct (2 * n + bitVal b) 0 (b, false) q
      simp only [List.replicate_zero, Nat.add_zero] at h₃
      have h₄ := ih (2 * n + bitVal b) (b, false)
      have h₁₂ := (run_add h₁ (n + 1)).trans h₂
      have h₁₂₃ := (run_add h₁₂ (2 * n + bitVal b + 1)).trans h₃
      have h := (run_add h₁₂₃ (workFrom (2 * n + bitVal b) q)).trans h₄
      have ht : 1 + (n + 1) + (2 * n + bitVal b + 1) + workFrom (2 * n + bitVal b) q =
          workFrom n (b :: q) := by simp only [workFrom]; omega
      simpa only [ht, valueFrom] using h

noncomputable def bitMachine : BitMachine.Machine :=
  ofFinite (0 : Fin 3) 0 .readBit (false, false) program

theorem bitMachine_outputs (q : List Bool) :
    bitMachine.OutputsWithin q (List.replicate (valueFrom 0 q) true)
      (4 * valueFrom 0 q + 3 * q.length + 2) := by
  have hi : rawInit (0 : Fin 3) .readBit (false, false) q =
      cfg (some .readBit) (false, false) q [] [] := by
    unfold rawInit cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  have hw : workFrom 0 q ≤ 4 * valueFrom 0 q + 3 * q.length + 2 := by
    simpa using workFrom_bound 0 q
  apply outputsWithin_of_raw_run (0 : Fin 3) 0 .readBit (false, false) program
    q (List.replicate (valueFrom 0 q) true) (workFrom 0 q) _ hw
  · change (run (workFrom 0 q) _).l = none
    rw [hi]
    change (run (workFrom 0 q) (cfg (some .readBit) (false, false) q (List.replicate 0 true) [])).l = none
    rw [run_correct]
    rfl
  · change (run (workFrom 0 q) _).stk 0 = _
    rw [hi]
    change (run (workFrom 0 q) (cfg (some .readBit) (false, false) q (List.replicate 0 true) [])).stk 0 = _
    rw [run_correct]
    rfl

theorem valueFrom_affine (n : ℕ) (q : List Bool) :
    valueFrom n q = n * 2 ^ q.length + valueFrom 0 q := by
  induction q generalizing n with
  | nil => simp [valueFrom]
  | cons b q ih =>
      simp only [valueFrom, List.length_cons, Nat.mul_zero, Nat.zero_add]
      rw [ih, ih (bitVal b), pow_succ]
      ring

theorem valueFrom_ofFn (a : ℕ) (f : Fin a → Bool) :
    valueFrom 0 (List.ofFn f) =
      ∑ j : Fin a, bitVal (f j.rev) * 2 ^ j.val := by
  induction a with
  | zero => simp [valueFrom]
  | succ a ih =>
      rw [List.ofFn_succ, valueFrom]
      simp only [Nat.mul_zero, Nat.zero_add]
      rw [valueFrom_affine, List.length_ofFn, ih, Fin.sum_univ_castSucc]
      simp only [Fin.rev_castSucc, Fin.rev_last, Fin.val_castSucc, Fin.val_last]
      omega

theorem valueFrom_wordCode (a : ℕ) (f : Fin a → Bool) :
    valueFrom 0 (List.ofFn f) = (MatrixMaterialization.wordCode a f).val := by
  rw [valueFrom_ofFn]
  change (∑ j : Fin a, bitVal (f j.rev) * 2 ^ j.val) =
    ∑ j : Fin a, (finTwoEquiv.symm (f j.rev)).val * 2 ^ j.val
  apply Finset.sum_congr rfl
  intro j _
  cases h : f j.rev <;> rfl

theorem encoded_label_outputs {a : ℕ} (label : Fin (2 ^ a)) :
    bitMachine.OutputsWithin
      (List.ofFn ((MatrixMaterialization.wordCode a).symm label))
      (List.replicate label.val true) (4 * label.val + 3 * a + 2) := by
  have hv : valueFrom 0 (List.ofFn ((MatrixMaterialization.wordCode a).symm label)) =
      label.val := by
    rw [valueFrom_wordCode, Equiv.apply_symm_apply]
  simpa only [hv, List.length_ofFn] using
    bitMachine_outputs (List.ofFn ((MatrixMaterialization.wordCode a).symm label))

end EthInapproximability.CurrentPaper.MatrixBinaryAddress
