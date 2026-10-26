import EthInapproximability.CurrentPaper.SourceClauseFixedUnary

/-!
# A fixed finite batch of unary constant pushes

For a fixed source alphabet and arity, each tuple/position callback requires
several fixed unary words. Their destinations and lengths are compiled into
finite control. Every bit is pushed by an actual machine transition; no
constant word is silently present in an initial scratch bank.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseFixedBatch

open Turing Turing.TM2.Stmt BitMachineEncoding

variable {K : Type*} [DecidableEq K] {M : ℕ}

inductive Label (sizes : Fin M → ℕ) where
  | write : (i : Fin M) → Fin (sizes i + 1) → Label sizes
  | done : Label sizes
  deriving DecidableEq, Fintype

def next (sizes : Fin M → ℕ) (i : Fin M) : Label sizes :=
  if h : i.val + 1 < M then .write ⟨i.val + 1, h⟩ 0 else .done

def program (targets : Fin M → K) (sizes : Fin M → ℕ) :
    Label sizes → TM2.Stmt (fun _ : K => Bool) (Label sizes) Unit
  | .write i j => if h : j.val < sizes i then
      push (targets i) (fun _ => true)
        (goto (fun _ => .write i ⟨j.val + 1, by omega⟩))
    else goto (fun _ => next sizes i)
  | .done => halt

def prepend (S : K → List Bool) (target : K) (n : ℕ) : K → List Bool :=
  Function.update S target (List.replicate n true ++ S target)

def state (targets : Fin M → K) (sizes : Fin M → ℕ)
    (S : K → List Bool) (i : Fin M) (j : Fin (sizes i + 1)) :
    TM2.Cfg (fun _ : K => Bool) (Label sizes) Unit :=
  ⟨some (.write i j), (), prepend S (targets i) j.val⟩

theorem state_zero (targets : Fin M → K) (sizes : Fin M → ℕ)
    (S : K → List Bool) (i : Fin M) :
    state targets sizes S i 0 = ⟨some (.write i 0), (), S⟩ := by
  simp [state, prepend]

theorem write_step (targets : Fin M → K) (sizes : Fin M → ℕ)
    (S : K → List Bool) (i : Fin M) (j : Fin (sizes i + 1))
    (h : j.val < sizes i) :
    advance (program targets sizes) (state targets sizes S i j) =
      state targets sizes S i ⟨j.val + 1, by omega⟩ := by
  simp only [advance, TM2.step, program, dif_pos h, TM2.stepAux,
    state, Option.getD_some]
  congr 1
  funext x
  by_cases hx : x = targets i
  · subst x
    simp [prepend, Function.update, List.replicate_succ]
  · simp [prepend, Function.update, hx]

theorem write_finish (targets : Fin M → K) (sizes : Fin M → ℕ)
    (S : K → List Bool) (i : Fin M) (j : Fin (sizes i + 1))
    (h : j.val = sizes i) :
    advance (program targets sizes) (state targets sizes S i j) =
      ⟨some (next sizes i), (), prepend S (targets i) (sizes i)⟩ := by
  have hn : ¬j.val < sizes i := by omega
  simp [advance, TM2.step, program, hn, state, h]

theorem write_run_from (targets : Fin M → K) (sizes : Fin M → ℕ)
    (S : K → List Bool) (i : Fin M) (j : Fin (sizes i + 1))
    (d : ℕ) (h : j.val + d = sizes i) :
    ((advance (program targets sizes))^[d + 1])
      (state targets sizes S i j) =
      ⟨some (next sizes i), (), prepend S (targets i) (sizes i)⟩ := by
  induction d generalizing j with
  | zero => exact write_finish targets sizes S i j (by omega)
  | succ d ih =>
      have hj : j.val < sizes i := by omega
      let j' : Fin (sizes i + 1) := ⟨j.val + 1, by omega⟩
      have hh : j'.val + d = sizes i := by simp only [j', Fin.val_mk]; omega
      rw [show (d + 1) + 1 = (d + 1) + 1 by rfl,
        Function.iterate_succ_apply, write_step targets sizes S i j hj]
      exact ih j' hh

theorem write_run (targets : Fin M → K) (sizes : Fin M → ℕ)
    (S : K → List Bool) (i : Fin M) :
    ((advance (program targets sizes))^[sizes i + 1])
      (⟨some (.write i 0), (), S⟩ :
        TM2.Cfg (fun _ : K => Bool) (Label sizes) Unit) =
      ⟨some (next sizes i), (), prepend S (targets i) (sizes i)⟩ := by
  rw [← state_zero targets sizes S i]
  exact write_run_from targets sizes S i 0 (sizes i) (by simp)

def labelAt (sizes : Fin M → ℕ) (m : ℕ) : Label sizes :=
  if h : m < M then .write ⟨m, h⟩ 0 else .done

def bankPrefix (targets : Fin M → K) (sizes : Fin M → ℕ)
    (S : K → List Bool) : ℕ → K → List Bool
  | 0 => S
  | m + 1 => if h : m < M then
      prepend (bankPrefix targets sizes S m) (targets ⟨m, h⟩)
        (sizes ⟨m, h⟩)
    else bankPrefix targets sizes S m

def costPrefix (sizes : Fin M → ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => if h : m < M then
      costPrefix sizes m + sizes ⟨m, h⟩ + 1
    else costPrefix sizes m

theorem next_labelAt (sizes : Fin M → ℕ) (m : ℕ)
    (h : m < M) :
    next sizes ⟨m, h⟩ = labelAt sizes (m + 1) := by
  simp [next, labelAt]

theorem prefix_run (targets : Fin M → K) (sizes : Fin M → ℕ)
    (S : K → List Bool) (m : ℕ) (hm : m ≤ M) :
    ((advance (program targets sizes))^[costPrefix sizes m])
      (⟨some (labelAt sizes 0), (), S⟩ :
        TM2.Cfg (fun _ : K => Bool) (Label sizes) Unit) =
      ⟨some (labelAt sizes m), (), bankPrefix targets sizes S m⟩ := by
  induction m with
  | zero => simp [costPrefix, bankPrefix]
  | succ m ih =>
      have h : m < M := by omega
      have hp := ih h.le
      have hw := write_run targets sizes
        (bankPrefix targets sizes S m) ⟨m, h⟩
      have hc : costPrefix sizes (m + 1) =
          costPrefix sizes m + (sizes ⟨m, h⟩ + 1) := by
        simp [costPrefix, h, Nat.add_assoc]
      have hb : bankPrefix targets sizes S (m + 1) =
          prepend (bankPrefix targets sizes S m)
            (targets ⟨m, h⟩) (sizes ⟨m, h⟩) := by
        simp [bankPrefix, h]
      rw [hc, Nat.add_comm, Function.iterate_add_apply, hp]
      simpa [labelAt, h, next_labelAt, hb] using hw

theorem run (targets : Fin M → K) (sizes : Fin M → ℕ)
    (S : K → List Bool) :
    ((advance (program targets sizes))^[costPrefix sizes M + 1])
      (⟨some (labelAt sizes 0), (), S⟩ :
        TM2.Cfg (fun _ : K => Bool) (Label sizes) Unit) =
      ⟨none, (), bankPrefix targets sizes S M⟩ := by
  rw [Function.iterate_succ_apply', prefix_run targets sizes S M (by omega)]
  simp [advance, TM2.step, program, labelAt]

theorem bankPrefix_untouched (targets : Fin M → K) (sizes : Fin M → ℕ)
    (S : K → List Bool) (m : ℕ) (hm : m ≤ M) (x : K)
    (h : ∀ i : Fin M, i.val < m → targets i ≠ x) :
    bankPrefix targets sizes S m x = S x := by
  induction m with
  | zero => rfl
  | succ m ih =>
      have hm' : m < M := by omega
      have hnot := h ⟨m, hm'⟩ (by simp)
      have hprev : ∀ i : Fin M, i.val < m → targets i ≠ x := by
        intro i hi
        exact h i (by omega)
      simp [bankPrefix, hm', prepend, Function.update,
        hnot, Ne.symm hnot, ih hm'.le hprev]

theorem bankPrefix_target (targets : Fin M → K) (sizes : Fin M → ℕ)
    (S : K → List Bool) (hinj : Function.Injective targets)
    (m : ℕ) (hm : m ≤ M) (i : Fin M) (hi : i.val < m) :
    bankPrefix targets sizes S m (targets i) =
      List.replicate (sizes i) true ++ S (targets i) := by
  induction m with
  | zero => omega
  | succ m ih =>
      have hm' : m < M := by omega
      by_cases him : i.val < m
      · have hne : targets ⟨m, hm'⟩ ≠ targets i := by
          intro he
          have heq := hinj he
          have hv := congrArg Fin.val heq
          simp only [Fin.val_mk] at hv
          omega
        simpa [bankPrefix, hm', prepend, Function.update,
          hne, Ne.symm hne] using ih hm'.le him
      · have hieq : i = ⟨m, hm'⟩ := Fin.ext (by simp only [Fin.val_mk]; omega)
        subst i
        have hprev : ∀ j : Fin M, j.val < m →
            targets j ≠ targets ⟨m, hm'⟩ := by
          intro j hj he
          have heq := hinj he
          have hv := congrArg Fin.val heq
          simp only [Fin.val_mk] at hv
          omega
        simp [bankPrefix, hm', prepend,
          bankPrefix_untouched targets sizes S m hm'.le
            (targets ⟨m, hm'⟩) hprev]

theorem result_target (targets : Fin M → K) (sizes : Fin M → ℕ)
    (S : K → List Bool) (hinj : Function.Injective targets)
    (i : Fin M) :
    bankPrefix targets sizes S M (targets i) =
      List.replicate (sizes i) true ++ S (targets i) := by
  exact bankPrefix_target targets sizes S hinj M (by omega) i i.isLt

theorem result_outside (targets : Fin M → K) (sizes : Fin M → ℕ)
    (S : K → List Bool) (x : K)
    (h : ∀ i : Fin M, targets i ≠ x) :
    bankPrefix targets sizes S M x = S x := by
  exact bankPrefix_untouched targets sizes S M (by omega) x
    (fun i _ => h i)

end EthInapproximability.CurrentPaper.SourceClauseFixedBatch
