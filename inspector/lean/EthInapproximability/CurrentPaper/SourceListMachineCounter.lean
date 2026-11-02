import EthInapproximability.CurrentPaper.ProtocolBoundedUnary
import EthInapproximability.CurrentPaper.BitMachineInline

/-! # A reusable fixed-width binary loop counter

Source: frozen v8 `B-effectivity-details.tex`, iteration over explicit source
lists. The all-zero test preserves the word, including padding. Positive words
are decremented by the existing literal two-stack predecessor machine.
-/

namespace EthInapproximability.CurrentPaper.SourceListMachineCounter

open Turing TM2.Stmt BitMachineEncoding EncodedCommunication

inductive OuterLabel where
  | scan | restore | finished
  deriving DecidableEq, Fintype

abbrev Stack := Fin 2
abbrev Label := Fin 4 ⊕ OuterLabel
abbrev Control := Fin 3 × (Option Bool × Bool)
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control
abbrev Statement := TM2.Stmt (fun _ : Stack => Bool) Label Control

def initialControl : Control := (0, none, false)
def counterControl (v : Fin 3) : Control := (v, none, false)
def doneControl (b : Bool) : Control := (0, some b, false)

def program : Label → Statement
  | .inl l => BitMachineInline.stmt Sum.inl counterControl Prod.fst
      (some (.inr .finished)) (ProtocolBinaryCounter.program l)
  | .inr .scan => pop 0 (fun s b => (s.1, b, s.2.2 || b.getD false))
      (branch (fun s => s.2.1.isSome)
        (push 1 (fun s => s.2.1.getD false) (goto (fun _ => .inr .scan)))
        (goto (fun _ => .inr .restore)))
  | .inr .restore => pop 1 (fun s b => (s.1, b, s.2.2))
      (branch (fun s => s.2.1.isSome)
        (push 0 (fun s => s.2.1.getD false) (goto (fun _ => .inr .restore)))
        (branch (fun s => s.2.2)
          (load (fun _ => counterControl 0) (goto (fun _ => .inl 0)))
          (load (fun _ => doneControl false) halt)))
  | .inr .finished => load (fun _ => doneControl true) halt

def cfg (l : Option Label) (v : Control) (q work : List Bool) : Config :=
  ⟨l, v, ProtocolBinaryCounter.stackContents q work⟩
def run (n : Nat) (c : Config) : Config := ((advance program)^[n]) c

theorem run_succ {c c' : Config} (h : advance program c = c') (n : Nat) :
    run (n + 1) c = run n c' := by
  exact (Function.iterate_succ_apply _ _ _).trans (congrArg (run n) h)
theorem run_add {c c' : Config} {n : Nat} (h : run n c = c') (m : Nat) :
    run (n + m) c = run m c' := by
  rw [Nat.add_comm, run, Function.iterate_add_apply]
  exact congrArg (run m) h

theorem scan_cons (v : Control) (b : Bool) (q work : List Bool) :
    advance program (cfg (some (.inr .scan)) v (b :: q) work) =
      cfg (some (.inr .scan)) (v.1, some b, v.2.2 || b) q (b :: work) := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]

theorem scan_nil (v : Control) (work : List Bool) :
    advance program (cfg (some (.inr .scan)) v [] work) =
      cfg (some (.inr .restore)) (v.1, none, v.2.2) [] work := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]

theorem restore_cons (v : Control) (b : Bool) (q work : List Bool) :
    advance program (cfg (some (.inr .restore)) v q (b :: work)) =
      cfg (some (.inr .restore)) (v.1, some b, v.2.2) (b :: q) work := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]

theorem restore_nil (v : Control) (q : List Bool) :
    advance program (cfg (some (.inr .restore)) v q []) =
      if v.2.2 then cfg (some (.inl 0)) (counterControl 0) q []
      else cfg none (doneControl false) q [] := by
  rcases v with ⟨a, b, flag⟩
  cases flag <;> simp [advance, TM2.step, TM2.stepAux, program, cfg]

theorem scan_run (v : Control) (q work : List Bool) :
    run (q.length + 1) (cfg (some (.inr .scan)) v q work) =
      cfg (some (.inr .restore)) (v.1, none, v.2.2 || q.any id) [] (q.reverse ++ work) := by
  induction q generalizing v work with
  | nil => simpa using run_succ (scan_nil v work) 0
  | cons b q ih =>
      rw [List.length_cons, run_succ (scan_cons v b q work), ih]
      simp [List.reverse_cons, List.append_assoc, Bool.or_assoc]

theorem restore_run (v : Control) (q work : List Bool) :
    run (work.length + 1) (cfg (some (.inr .restore)) v q work) =
      if v.2.2 then cfg (some (.inl 0)) (counterControl 0) (work.reverse ++ q) []
      else cfg none (doneControl false) (work.reverse ++ q) [] := by
  induction work generalizing v q with
  | nil => simpa using run_succ (restore_nil v q) 0
  | cons b work ih =>
      rw [List.length_cons, run_succ (restore_cons v b q work), ih]
      simp [List.reverse_cons, List.append_assoc]

theorem zero_test (q : List Bool) :
    run (2 * q.length + 2) (cfg (some (.inr .scan)) initialControl q []) =
      if q.any id then cfg (some (.inl 0)) (counterControl 0) q []
      else cfg none (doneControl false) q [] := by
  have hs := scan_run initialControl q []
  simp only [initialControl, Bool.false_or, List.append_nil] at hs
  have hr := restore_run (0, none, q.any id) [] q.reverse
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hr
  simpa only [Nat.two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (run_add hs (q.length + 1)).trans hr

theorem decrement_run (q : List Bool) :
    ∃ t ≤ 2 * q.length + 3,
      run t (cfg (some (.inl 0)) (counterControl 0) q []) =
        cfg none (doneControl true) (ProtocolBinaryCounter.predBits q) [] := by
  have hp := ProtocolBinaryCounter.borrow_correct q [] 0
  change ((advance ProtocolBinaryCounter.program)^[2 * q.length + 0 + 2])
      (ProtocolBinaryCounter.cfg (some 0) 0 q []) =
      ProtocolBinaryCounter.cfg none 0 (ProtocolBinaryCounter.predBits q) [] at hp
  simp only [Nat.add_zero] at hp
  obtain ⟨t, ht, he⟩ := BitMachineInline.outputs Sum.inl counterControl Prod.fst
    (fun _ => rfl) (some (.inr .finished)) ProtocolBinaryCounter.program program (fun _ => rfl)
    (ProtocolBinaryCounter.cfg (some 0) 0 q []) (2 * q.length + 2)
    (by rw [hp]; rfl)
  rw [hp] at he
  change run t (cfg (some (.inl 0)) (counterControl 0) q []) =
    cfg (some (.inr .finished)) (counterControl 0) (ProtocolBinaryCounter.predBits q) [] at he
  have hs : advance program
      (cfg (some (.inr .finished)) (counterControl 0) (ProtocolBinaryCounter.predBits q) []) =
      cfg none (doneControl true) (ProtocolBinaryCounter.predBits q) [] := by
    simp [advance, TM2.step, TM2.stepAux, program, cfg]
  exact ⟨t + 1, by omega, (run_add he 1).trans (run_succ hs 0)⟩

/-- One finite binary-counter step. The zero case keeps every padding bit;
the positive case returns the exact fixed-width predecessor. -/
theorem counter_run (q : List Bool) :
    ∃ t ≤ 4 * q.length + 5,
      run t (cfg (some (.inr .scan)) initialControl q []) =
        match ProtocolBinaryCounter.subOne q with
        | none => cfg none (doneControl false) q []
        | some q' => cfg none (doneControl true) q' [] := by
  have hspec := ProtocolBinaryCounter.subOne_spec q
  cases hs : ProtocolBinaryCounter.subOne q with
  | none =>
      simp only [hs] at hspec
      have hz := (ProtocolBoundedUnary.any_eq_false_iff q).mpr hspec
      refine ⟨2 * q.length + 2, by omega, ?_⟩
      simpa [hs, hz] using zero_test q
  | some q' =>
      simp only [hs] at hspec
      have hz : q.any id = true := by
        cases hh : q.any id
        · have hzero := (ProtocolBoundedUnary.any_eq_false_iff q).mp hh
          omega
        · rfl
      have hzero := zero_test q
      simp only [hz, ↓reduceIte] at hzero
      obtain ⟨t, ht, he⟩ := decrement_run q
      have hp : ProtocolBinaryCounter.predBits q = q' := by
        simp [ProtocolBinaryCounter.predBits, ProtocolBinaryCounter.predInto_eq, hs]
      rw [hp] at he
      exact ⟨2 * q.length + 2 + t, by omega, by simpa [hs] using (run_add hzero t).trans he⟩

theorem counter_positive (q q' : List Bool) (h : ProtocolBinaryCounter.subOne q = some q') :
    ∃ t ≤ 4 * q.length + 5,
      run t (cfg (some (.inr .scan)) initialControl q []) = cfg none (doneControl true) q' [] := by
  simpa [h] using counter_run q

theorem counter_zero (q : List Bool) (h : bitsValue q = 0) :
    run (2 * q.length + 2) (cfg (some (.inr .scan)) initialControl q []) =
      cfg none (doneControl false) q [] := by
  simpa [(ProtocolBoundedUnary.any_eq_false_iff q).mpr h] using zero_test q

end EthInapproximability.CurrentPaper.SourceListMachineCounter
