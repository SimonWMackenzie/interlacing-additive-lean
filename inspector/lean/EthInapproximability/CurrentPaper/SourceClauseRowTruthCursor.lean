import EthInapproximability.CurrentPaper.SourceClauseRowTruthCopy

/-!
# Physical fixed-arity truth-table cursor

The validated row table has a leading true status marker followed by the
`a^q` truth bits in the source's `Fin (a^q)` order. This finite-control cursor
checks and removes the marker, visits every bit in order with its assignment
index as an instruction label, and writes the resulting decisions on a work
stack. It preserves the entire row frame. A later callback must replace the
decision write by actual Boolean-clause emission; this module is not that
emitter.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseRowTruthCursor

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

open Turing Turing.TM2.Stmt BitMachineEncoding

abbrev Stack (q : ℕ) := SourceClauseRowTruthCopy.Stack q

inductive Label (N : ℕ) where
  | marker
  | read : Fin (N + 1) → Label N
  deriving DecidableEq, Fintype

def program {q N : ℕ} : Label N →
    TM2.Stmt (fun _ : Stack q => Bool) (Label N) (Option Bool)
  | .marker => pop (.inr 0) (fun _ b => b)
      (branch (fun b => b == some true)
        (goto (fun _ => .read 0)) halt)
  | .read i => if h : i.val < N then
      pop (.inr 0) (fun _ b => b)
        (branch Option.isSome
          (push (.inr 1) (fun b => b.getD false)
            (goto (fun _ => .read ⟨i.val + 1, by omega⟩)))
          halt)
    else load (fun _ => none) halt

def state {q N : ℕ} (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (label : Option (Label N)) (control : Option Bool)
    (remaining decisions : List Bool) :
    TM2.Cfg (fun _ : Stack q => Bool) (Label N) (Option Bool) :=
  ⟨label, control, Sum.elim row ![remaining, decisions]⟩

theorem marker_step {q N : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (bits decisions : List Bool) :
    advance program (state (N := N) row (some .marker) none
      (true :: bits) decisions) =
      state row (some (.read 0)) (some true) bits decisions := by
  simp only [advance, TM2.step, program, TM2.stepAux, state,
    Sum.elim_inr, Matrix.cons_val_zero, List.head?_cons, List.tail_cons,
    Option.isSome_some, Option.getD_some, Function.update_apply]
  change (⟨some (.read (0 : Fin (N + 1))), some true,
    Function.update (Sum.elim row ![true :: bits, decisions]) (.inr 0) bits⟩ :
      TM2.Cfg (fun _ : Stack q => Bool) (Label N) (Option Bool)) =
    ⟨some (.read 0), some true, Sum.elim row ![bits, decisions]⟩
  congr 1
  funext k
  cases k with
  | inl j => simp only [Function.update_apply, Sum.inl_ne_inr,
      ↓reduceIte, Sum.elim_inl]
  | inr j => fin_cases j <;> simp [Function.update]

theorem read_step {q N : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (i : Fin (N + 1)) (h : i.val < N)
    (b : Bool) (bits decisions : List Bool) (v : Option Bool) :
    advance program (state row (some (.read i)) v (b :: bits) decisions) =
      state row (some (.read ⟨i.val + 1, by omega⟩)) (some b)
        bits (b :: decisions) := by
  simp only [advance, TM2.step, program, dif_pos h, TM2.stepAux, state,
    Sum.elim_inr, Matrix.cons_val_zero, List.head?_cons, List.tail_cons,
    Option.isSome_some, Option.getD_some, Function.update_apply]
  change (⟨some (.read ⟨i.val + 1, by omega⟩), some b,
    Function.update
      (Function.update (Sum.elim row ![b :: bits, decisions]) (.inr 0) bits)
      (.inr 1) (b :: decisions)⟩ :
      TM2.Cfg (fun _ : Stack q => Bool) (Label N) (Option Bool)) =
    ⟨some (.read ⟨i.val + 1, by omega⟩), some b,
      Sum.elim row ![bits, b :: decisions]⟩
  congr 1
  funext k
  cases k with
  | inl j => simp only [Function.update_apply, Sum.inl_ne_inr,
      ↓reduceIte, Sum.elim_inl]
  | inr j => fin_cases j <;> simp [Function.update]

theorem finish_step {q N : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (i : Fin (N + 1)) (h : i.val = N)
    (decisions : List Bool) (v : Option Bool) :
    advance program (state row (some (.read i)) v [] decisions) =
      state row none none [] decisions := by
  have hn : ¬i.val < N := by omega
  simp [advance, TM2.step, program, hn, state]

theorem read_run {q N : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (i : Fin (N + 1)) (bits decisions : List Bool)
    (hi : i.val + bits.length = N) (v : Option Bool) :
    ((advance program)^[bits.length + 1])
      (state row (some (.read i)) v bits decisions) =
      state row none none [] (bits.reverse ++ decisions) := by
  induction bits generalizing i decisions v with
  | nil =>
      have h : i.val = N := by simpa using hi
      simpa only [List.length_nil, Nat.zero_add, List.reverse_nil,
        List.nil_append] using finish_step row i h decisions v
  | cons b bits ih =>
      have h : i.val < N := by
        simp only [List.length_cons] at hi
        omega
      let next : Fin (N + 1) := ⟨i.val + 1, by omega⟩
      have hnext : next.val + bits.length = N := by
        simp only [next, Fin.val_mk]
        simp only [List.length_cons] at hi
        omega
      rw [List.length_cons, show bits.length + 1 + 1 =
        (bits.length + 1) + 1 by omega, Function.iterate_succ_apply]
      rw [read_step row i h b bits decisions v]
      simpa [List.reverse_cons, List.append_assoc] using
        ih next (b :: decisions) hnext (some b)

theorem table_run {q N : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (bits : List Bool) (h : bits.length = N) :
    ((advance (program (q := q) (N := N)))^[N + 2])
      (state (N := N) row (some .marker) none (true :: bits) []) =
      state (N := N) row none none [] bits.reverse := by
  rw [show N + 2 = (N + 1) + 1 by omega,
    Function.iterate_succ_apply, marker_step]
  have hr := read_run row (0 : Fin (N + 1)) bits []
    (by simpa using h) (some true)
  simpa only [h, List.append_nil] using hr

theorem copied_ready {q N : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (bits : List Bool) (h : row (.inr 2) = true :: bits) :
    (SourceClauseRowTruthCopy.finalBank row (true :: bits)) =
      (state (N := N) row (some .marker) none (true :: bits) []).stk := by
  funext k
  cases k with
  | inl j => exact SourceClauseRowTruthCopy.row_preserved row (true :: bits) h j
  | inr j =>
      fin_cases j
      · exact SourceClauseRowTruthCopy.copied_bits row (true :: bits)
      · exact SourceClauseRowTruthCopy.scratch_empty row (true :: bits)

def combinedProgram {q N : ℕ} :=
  BitMachineRawSequence.program SourceClauseRowTruthCopy.program
    (program (q := q) (N := N)) .marker none none

theorem combined_run {q N : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (bits : List Bool) (hlen : bits.length = N)
    (htable : row (.inr 2) = true :: bits) :
    ∃ t ≤ 3 * N + 7,
      ((advance (combinedProgram (q := q) (N := N)))^[t])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
          (none, none), SourceClauseRowTruthCopy.initial row⟩ :
          TM2.Cfg (fun _ : Stack q => Bool)
            (BitMachineRawSequence.Label BitMachineCopy.Label (Label N))
            (Option Bool × Option Bool)) =
        ⟨none, (none, none),
          (state (N := N) row none none [] bits.reverse).stk⟩ := by
  have hc := SourceClauseRowTruthCopy.copy_run row (true :: bits) htable
  have ht := table_run row bits hlen
  have ht' : ((advance (program (q := q) (N := N)))^[N + 2])
      (⟨some .marker, none,
        SourceClauseRowTruthCopy.finalBank row (true :: bits)⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) (Label N) (Option Bool)) =
      state (N := N) row none none [] bits.reverse := by
    rw [copied_ready (N := N) row bits htable]
    exact ht
  obtain ⟨t, htime, hr⟩ := BitMachineRawSequence.runs
    SourceClauseRowTruthCopy.program (program (q := q) (N := N))
    BitMachineCopy.Label.scan Label.marker none none none none
    (SourceClauseRowTruthCopy.initial row)
    (SourceClauseRowTruthCopy.finalBank row (true :: bits))
    (state (N := N) row none none [] bits.reverse).stk
    (2 * (true :: bits).length + 2) (N + 2) hc ht'
  refine ⟨t, ?_, hr⟩
  simp only [List.length_cons] at htime
  omega

end EthInapproximability.CurrentPaper.SourceClauseRowTruthCursor
