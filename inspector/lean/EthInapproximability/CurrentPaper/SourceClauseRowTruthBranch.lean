import EthInapproximability.CurrentPaper.SourceClauseRowTruthCursor

/-!
# Finite-control dispatch on an actual row truth bit

After the source-preserving table copy, the program checks its leading marker,
physically consumes the preceding `k` truth bits, and branches to `accept` or
`reject` according to the actual bit at tuple position `k`. The two terminal
labels are callback boundaries for the respective literal schedules; no bit
or branch choice is supplied as a precomputed oracle.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseRowTruthBranch

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

open Turing Turing.TM2.Stmt BitMachineEncoding

abbrev Stack (q : ℕ) := SourceClauseRowTruthCopy.Stack q

inductive Label (N : ℕ) where
  | marker
  | skip : Fin (N + 1) → Label N
  | accept | reject
  deriving DecidableEq, Fintype

def choice (b : Bool) (N : ℕ) : Label N :=
  if b then .accept else .reject

def program {q N : ℕ} (k : Fin N) : Label N →
    TM2.Stmt (fun _ : Stack q => Bool) (Label N) (Option Bool)
  | .marker => pop (.inr 0) (fun _ b => b)
      (branch (fun b => b == some true)
        (goto (fun _ => .skip 0)) halt)
  | .skip i => if h : i.val < k.val then
      pop (.inr 0) (fun _ b => b)
        (branch Option.isSome
          (goto (fun _ => .skip ⟨i.val + 1, by omega⟩)) halt)
    else if i.val = k.val then
      pop (.inr 0) (fun _ b => b)
        (branch (fun b => b == some true)
          (goto (fun _ => .accept))
          (branch Option.isSome (goto (fun _ => .reject)) halt))
    else halt
  | .accept => .halt
  | .reject => .halt

def state {q N : ℕ} (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (label : Option (Label N)) (control : Option Bool)
    (remaining : List Bool) :
    TM2.Cfg (fun _ : Stack q => Bool) (Label N) (Option Bool) :=
  ⟨label, control, Sum.elim row ![remaining, []]⟩

theorem marker_step {q N : ℕ} (k : Fin N)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (bits : List Bool) :
    advance (program k)
      (state (N := N) row (some .marker) none (true :: bits)) =
      state row (some (.skip 0)) (some true) bits := by
  simp only [advance, TM2.step, program, TM2.stepAux, state,
    Sum.elim_inr, Matrix.cons_val_zero, List.head?_cons, List.tail_cons,
    Option.isSome_some, Option.getD_some, Function.update_apply]
  change (⟨some (.skip (0 : Fin (N + 1))), some true,
    Function.update (Sum.elim row ![true :: bits, []]) (.inr 0) bits⟩ :
      TM2.Cfg (fun _ : Stack q => Bool) (Label N) (Option Bool)) =
    ⟨some (.skip 0), some true, Sum.elim row ![bits, []]⟩
  congr 1
  funext x
  cases x with
  | inl x => simp only [Function.update_apply, Sum.inl_ne_inr,
      ↓reduceIte, Sum.elim_inl]
  | inr x => fin_cases x <;> simp [Function.update]

theorem skip_step {q N : ℕ} (k : Fin N)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (i : Fin (N + 1)) (hi : i.val < k.val)
    (b : Bool) (bits : List Bool) (v : Option Bool) :
    advance (program k)
      (state row (some (.skip i)) v (b :: bits)) =
      state row (some (.skip ⟨i.val + 1, by omega⟩)) (some b) bits := by
  simp only [advance, TM2.step, program, dif_pos hi, TM2.stepAux, state,
    Sum.elim_inr, Matrix.cons_val_zero, List.head?_cons, List.tail_cons,
    Option.isSome_some, Option.getD_some, Function.update_apply]
  change (⟨some (.skip ⟨i.val + 1, by omega⟩), some b,
    Function.update (Sum.elim row ![b :: bits, []]) (.inr 0) bits⟩ :
      TM2.Cfg (fun _ : Stack q => Bool) (Label N) (Option Bool)) =
    ⟨some (.skip ⟨i.val + 1, by omega⟩), some b,
      Sum.elim row ![bits, []]⟩
  congr 1
  funext x
  cases x with
  | inl x => simp only [Function.update_apply, Sum.inl_ne_inr,
      ↓reduceIte, Sum.elim_inl]
  | inr x => fin_cases x <;> simp [Function.update]

theorem choice_step {q N : ℕ} (k : Fin N)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (b : Bool) (bits : List Bool) (v : Option Bool) :
    advance (program k)
      (state row (some (.skip ⟨k.val, by omega⟩)) v (b :: bits)) =
      state row (some (choice b N)) (some b) bits := by
  have hn : ¬k.val < k.val := by omega
  cases b <;>
    simp only [advance, TM2.step, program, dif_neg hn,
      if_true, TM2.stepAux, state, choice,
      Sum.elim_inr, Matrix.cons_val_zero, List.head?_cons,
      List.tail_cons]
  all_goals
    change (⟨_, _, Function.update
      (Sum.elim row ![_ :: bits, []]) (.inr 0) bits⟩ :
      TM2.Cfg (fun _ : Stack q => Bool) (Label N) (Option Bool)) =
      ⟨_, _, Sum.elim row ![bits, []]⟩
    congr 1
    funext x
    cases x with
    | inl x => simp [Function.update]
    | inr x => fin_cases x <;> simp [Function.update]

theorem skip_run {q N : ℕ} (k : Fin N)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (i : Fin (N + 1)) (pre suffix : List Bool)
    (hi : i.val + pre.length = k.val) (v : Option Bool) :
    ∃ v', ((advance (program k))^[pre.length])
      (state row (some (.skip i)) v (pre ++ suffix)) =
      state row (some (.skip ⟨k.val, by omega⟩)) v' suffix := by
  induction pre generalizing i v with
  | nil =>
      have he : i = ⟨k.val, by omega⟩ := Fin.ext (by simpa using hi)
      rw [he]
      exact ⟨v, by simp [state]⟩
  | cons b bs ih =>
      have hlt : i.val < k.val := by
        simp only [List.length_cons] at hi
        omega
      let next : Fin (N + 1) := ⟨i.val + 1, by omega⟩
      have hn : next.val + bs.length = k.val := by
        simp only [next, Fin.val_mk]
        simp only [List.length_cons] at hi
        omega
      obtain ⟨v', hv'⟩ := ih next hn (some b)
      refine ⟨v', ?_⟩
      rw [List.length_cons, show bs.length + 1 = bs.length + 1 by rfl,
        Function.iterate_succ_apply]
      rw [List.cons_append, skip_step k row i hlt b (bs ++ suffix) v]
      exact hv'

theorem branch_run {q N : ℕ} (k : Fin N)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (pre suffix : List Bool) (b : Bool)
    (hlen : pre.length = k.val) :
    ((advance (program k))^[k.val + 2])
      (state row (some .marker) none (true :: (pre ++ b :: suffix))) =
      state row (some (choice b N)) (some b) suffix := by
  obtain ⟨v, hv⟩ := skip_run k row (0 : Fin (N + 1)) pre (b :: suffix)
    (by simpa using hlen) (some true)
  rw [show k.val + 2 = (k.val + 1) + 1 by omega,
    Function.iterate_succ_apply, marker_step]
  rw [show k.val + 1 = pre.length + 1 by omega,
    Function.iterate_succ_apply']
  rw [hv, choice_step]

theorem copied_ready {q N : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (bits : List Bool) (h : row (.inr 2) = true :: bits) :
    SourceClauseRowTruthCopy.finalBank row (true :: bits) =
      (state (N := N) row (some .marker) none (true :: bits)).stk := by
  funext x
  cases x with
  | inl x => exact SourceClauseRowTruthCopy.row_preserved row (true :: bits) h x
  | inr x =>
      fin_cases x
      · exact SourceClauseRowTruthCopy.copied_bits row (true :: bits)
      · exact SourceClauseRowTruthCopy.scratch_empty row (true :: bits)

theorem table_split {N : ℕ} (table : Fin N → Bool) (k : Fin N) :
    List.ofFn table =
      (List.ofFn table).take k.val ++ table k ::
        (List.ofFn table).drop (k.val + 1) := by
  let bits := List.ofFn table
  have hk : k.val < bits.length := by simpa [bits] using k.isLt
  calc
    bits = bits.take k.val ++ bits.drop k.val :=
      (List.take_append_drop k.val bits).symm
    _ = bits.take k.val ++ bits[k.val] :: bits.drop (k.val + 1) := by
      rw [List.cons_getElem_drop_succ (h := hk)]
    _ = _ := by simp [bits]

theorem typed_branch_run {q N : ℕ} (k : Fin N)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (table : Fin N → Bool)
    (h : row (.inr 2) = true :: List.ofFn table) :
    ((advance (program k))^[k.val + 2])
      (⟨some .marker, none,
        SourceClauseRowTruthCopy.finalBank row (true :: List.ofFn table)⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) (Label N) (Option Bool)) =
      state row (some (choice (table k) N)) (some (table k))
        ((List.ofFn table).drop (k.val + 1)) := by
  rw [copied_ready (N := N) row (List.ofFn table) h]
  have hpre : ((List.ofFn table).take k.val).length = k.val := by
    simp [List.length_take, show k.val ≤ (List.ofFn table).length by
      simp [k.isLt.le]]
  have ht := branch_run k row ((List.ofFn table).take k.val)
    ((List.ofFn table).drop (k.val + 1)) (table k) hpre
  simpa only [← table_split table k] using ht

end EthInapproximability.CurrentPaper.SourceClauseRowTruthBranch
