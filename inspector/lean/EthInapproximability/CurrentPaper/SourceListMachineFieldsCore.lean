import EthInapproximability.CurrentPaper.ProtocolBoundedUnary

/-! # A binary-counted raw payload reader

Source: frozen v8 `B-effectivity-details.tex`, explicit source lists, and
`06-eth.tex`, the Boolean-stack machine convention. Each decrement requires
one actual source bit. The suffix is not scanned or copied. The binary counter
is a stack, not an unbounded machine register.
-/

namespace EthInapproximability.CurrentPaper.SourceListMachineFieldsCore

open Turing Turing.TM2.Stmt BitMachineEncoding
open EncodedCommunication (bitsValue)

inductive Label where
  | zeroScan | zeroRestore | testSource | subtract | copy | restore
  deriving DecidableEq, Fintype

abbrev Stack := Fin 5
abbrev Control := Option Bool × Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .zeroScan => pop 0 (fun s b => (b, s.2 || b.getD false))
      (branch (fun s => s.1.isSome)
        (push 2 (fun s => s.1.getD false) (goto (fun _ => .zeroScan)))
        (goto (fun _ => .zeroRestore)))
  | .zeroRestore => pop 2 (fun s b => (b, s.2))
      (branch (fun s => s.1.isSome)
        (push 0 (fun s => s.1.getD false) (goto (fun _ => .zeroRestore)))
        (branch Prod.snd (goto (fun _ => .testSource))
          (load (fun _ => (some true, false)) halt)))
  | .testSource => pop 1 (fun s b => (b, s.2))
      (branch (fun s => s.1.isSome)
        (push 3 (fun s => s.1.getD false)
          (push 4 (fun _ => true) (goto (fun _ => .subtract))))
        (load (fun _ => (some false, false)) halt))
  | .subtract => pop 0 (fun s b => (b, s.2))
      (branch (fun s => s.1.isSome)
        (branch (fun s => s.1.getD false)
          (push 2 (fun _ => false) (goto (fun _ => .copy)))
          (push 2 (fun _ => true) (goto (fun _ => .subtract)))) halt)
  | .copy => pop 0 (fun s b => (b, s.2))
      (branch (fun s => s.1.isSome)
        (push 2 (fun s => s.1.getD false) (goto (fun _ => .copy)))
        (goto (fun _ => .restore)))
  | .restore => pop 2 (fun s b => (b, s.2))
      (branch (fun s => s.1.isSome)
        (push 0 (fun s => s.1.getD false) (goto (fun _ => .restore)))
        (load (fun _ => (none, false)) (goto (fun _ => .zeroScan))))

def stackContents (q source work payload count : List Bool) : Stack → List Bool :=
  ![q, source, work, payload, count]

def cfg (l : Option Label) (s : Control) (q source work payload count : List Bool) : Config :=
  ⟨l, s, stackContents q source work payload count⟩

def run (n : Nat) (c : Config) : Config := ((advance program)^[n]) c

theorem run_succ {c d : Config} (h : TM2.step program c = some d) (n : Nat) :
    run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

theorem run_add {c d : Config} {m : Nat} (h : run m c = d) (n : Nat) :
    run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem step_scan_cons (s : Control) (b : Bool) (q source work payload count : List Bool) :
    TM2.step program (cfg (some .zeroScan) s (b :: q) source work payload count) =
      some (cfg (some .zeroScan) (some b, s.2 || b) q source (b :: work) payload count) := by
  simp [TM2.step, TM2.stepAux, program, cfg, stackContents]
  funext k; fin_cases k <;> rfl

private theorem step_scan_nil (s : Control) (source work payload count : List Bool) :
    TM2.step program (cfg (some .zeroScan) s [] source work payload count) =
      some (cfg (some .zeroRestore) (none, s.2) [] source work payload count) := by
  simp [TM2.step, TM2.stepAux, program, cfg, stackContents]

private theorem step_zeroRestore_cons (s : Control) (b : Bool) (q source work payload count : List Bool) :
    TM2.step program (cfg (some .zeroRestore) s q source (b :: work) payload count) =
      some (cfg (some .zeroRestore) (some b, s.2) (b :: q) source work payload count) := by
  simp [TM2.step, TM2.stepAux, program, cfg, stackContents]
  funext k; fin_cases k <;> rfl

private theorem step_zeroRestore_nil (s : Control) (q source payload count : List Bool) :
    TM2.step program (cfg (some .zeroRestore) s q source [] payload count) =
      some (if s.2 then cfg (some .testSource) (none, true) q source [] payload count
        else cfg none (some true, false) q source [] payload count) := by
  rcases s with ⟨s, b⟩
  cases b <;> simp [TM2.step, TM2.stepAux, program, cfg, stackContents]

theorem scan_correct (s : Control) (q source work payload count : List Bool) :
    run (q.length + 1) (cfg (some .zeroScan) s q source work payload count) =
      cfg (some .zeroRestore) (none, s.2 || q.any id) [] source (q.reverse ++ work) payload count := by
  induction q generalizing s work with
  | nil => simpa using run_succ (step_scan_nil s source work payload count) 0
  | cons b q ih =>
      rw [List.length_cons, run_succ (step_scan_cons s b q source work payload count), ih]
      simp [List.reverse_cons, List.append_assoc, Bool.or_assoc]

theorem zeroRestore_correct (s : Control) (q source work payload count : List Bool) :
    run (work.length + 1) (cfg (some .zeroRestore) s q source work payload count) =
      if s.2 then cfg (some .testSource) (none, true) (work.reverse ++ q) source [] payload count
      else cfg none (some true, false) (work.reverse ++ q) source [] payload count := by
  induction work generalizing s q with
  | nil => simpa using run_succ (step_zeroRestore_nil s q source payload count) 0
  | cons b work ih =>
      rw [List.length_cons, run_succ (step_zeroRestore_cons s b q source work payload count), ih]
      simp [List.reverse_cons, List.append_assoc]

theorem zero_test (q source payload count : List Bool) :
    run (2 * q.length + 2) (cfg (some .zeroScan) (none, false) q source [] payload count) =
      if q.any id then cfg (some .testSource) (none, true) q source [] payload count
      else cfg none (some true, false) q source [] payload count := by
  have hs := scan_correct (none, false) q source [] payload count
  simp only [Bool.false_or, List.append_nil] at hs
  have hr := zeroRestore_correct (none, q.any id) [] source q.reverse payload count
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hr
  simpa only [Nat.two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (run_add hs (q.length + 1)).trans hr

private theorem step_sub_false (s : Control) (q source work payload count : List Bool) :
    TM2.step program (cfg (some .subtract) s (false :: q) source work payload count) =
      some (cfg (some .subtract) (some false, s.2) q source (true :: work) payload count) := by
  simp [TM2.step, TM2.stepAux, program, cfg, stackContents]
  funext k; fin_cases k <;> rfl

private theorem step_sub_true (s : Control) (q source work payload count : List Bool) :
    TM2.step program (cfg (some .subtract) s (true :: q) source work payload count) =
      some (cfg (some .copy) (some true, s.2) q source (false :: work) payload count) := by
  simp [TM2.step, TM2.stepAux, program, cfg, stackContents]
  funext k; fin_cases k <;> rfl

private theorem step_copy_cons (s : Control) (b : Bool) (q source work payload count : List Bool) :
    TM2.step program (cfg (some .copy) s (b :: q) source work payload count) =
      some (cfg (some .copy) (some b, s.2) q source (b :: work) payload count) := by
  simp [TM2.step, TM2.stepAux, program, cfg, stackContents]
  funext k; fin_cases k <;> rfl

private theorem step_copy_nil (s : Control) (source work payload count : List Bool) :
    TM2.step program (cfg (some .copy) s [] source work payload count) =
      some (cfg (some .restore) (none, s.2) [] source work payload count) := by
  simp [TM2.step, TM2.stepAux, program, cfg, stackContents]

private theorem step_restore_cons (s : Control) (b : Bool) (q source work payload count : List Bool) :
    TM2.step program (cfg (some .restore) s q source (b :: work) payload count) =
      some (cfg (some .restore) (some b, s.2) (b :: q) source work payload count) := by
  simp [TM2.step, TM2.stepAux, program, cfg, stackContents]
  funext k; fin_cases k <;> rfl

private theorem step_restore_nil (s : Control) (q source payload count : List Bool) :
    TM2.step program (cfg (some .restore) s q source [] payload count) =
      some (cfg (some .zeroScan) (none, false) q source [] payload count) := by
  simp [TM2.step, TM2.stepAux, program, cfg, stackContents]

theorem restore_correct (s : Control) (q source work payload count : List Bool) :
    run (work.length + 1) (cfg (some .restore) s q source work payload count) =
      cfg (some .zeroScan) (none, false) (work.reverse ++ q) source [] payload count := by
  induction work generalizing s q with
  | nil => simpa using run_succ (step_restore_nil s q source payload count) 0
  | cons b work ih =>
      rw [List.length_cons, run_succ (step_restore_cons s b q source work payload count), ih]
      simp [List.reverse_cons, List.append_assoc]

theorem copy_correct (s : Control) (q source work payload count : List Bool) :
    run (2 * q.length + work.length + 2) (cfg (some .copy) s q source work payload count) =
      cfg (some .zeroScan) (none, false) (work.reverse ++ q) source [] payload count := by
  induction q generalizing s work with
  | nil =>
      rw [show 2 * ([] : List Bool).length + work.length + 2 =
        (work.length + 1) + 1 by simp,
        run_succ (step_copy_nil s source work payload count), restore_correct]
  | cons b q ih =>
      rw [show 2 * (b :: q).length + work.length + 2 =
        (2 * q.length + (b :: work).length + 2) + 1 by simp; omega,
        run_succ (step_copy_cons s b q source work payload count), ih]
      simp

theorem subtract_correct (s : Control) (q q' source work payload count : List Bool)
    (hq : ProtocolBinaryCounter.subOne q = some q') :
    run (2 * q.length + work.length + 2) (cfg (some .subtract) s q source work payload count) =
      cfg (some .zeroScan) (none, false) (work.reverse ++ q') source [] payload count := by
  induction q generalizing s q' work with
  | nil => simp [ProtocolBinaryCounter.subOne] at hq
  | cons b q ih =>
      cases b with
      | true =>
          simp only [ProtocolBinaryCounter.subOne, Option.some.injEq] at hq
          subst q'
          rw [show 2 * (true :: q).length + work.length + 2 =
            (2 * q.length + (false :: work).length + 2) + 1 by simp; omega,
            run_succ (step_sub_true s q source work payload count), copy_correct]
          simp
      | false =>
          simp only [ProtocolBinaryCounter.subOne] at hq
          obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hq
          rw [show 2 * (false :: q).length + work.length + 2 =
            (2 * q.length + (true :: work).length + 2) + 1 by simp; omega,
            run_succ (step_sub_false s q source work payload count), ih _ _ _ hr]
          simp

private theorem step_source_nil (s : Control) (q payload count : List Bool) :
    TM2.step program (cfg (some .testSource) s q [] [] payload count) =
      some (cfg none (some false, false) q [] [] payload count) := by
  simp [TM2.step, TM2.stepAux, program, cfg, stackContents]

private theorem step_source_cons (s : Control) (b : Bool) (q source payload count : List Bool) :
    TM2.step program (cfg (some .testSource) s q (b :: source) [] payload count) =
      some (cfg (some .subtract) (some b, s.2) q source [] (b :: payload) (true :: count)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, stackContents]
  funext k; fin_cases k <;> rfl

/-- The time depends on the consumed prefix, not on the unvisited suffix.
The exact final frame covers success, truncation and padded binary counters. -/
theorem payload_run (q source payload count : List Bool) :
    ∃ t ≤ (min (bitsValue q) source.length + 1) * (4 * q.length + 5), ∃ q',
      q'.length = q.length ∧
      run t (cfg (some .zeroScan) (none, false) q source [] payload count) =
        cfg none (some (decide (bitsValue q ≤ source.length)), false)
          q' (source.drop (bitsValue q)) []
          ((source.take (bitsValue q)).reverse ++ payload)
          (List.replicate (min (bitsValue q) source.length) true ++ count) := by
  induction source generalizing q payload count with
  | nil =>
      by_cases hz : q.any id = false
      · have hv := (ProtocolBoundedUnary.any_eq_false_iff q).mp hz
        refine ⟨2 * q.length + 2, by simp; omega, q, rfl, ?_⟩
        simpa [hz, hv] using zero_test q [] payload count
      · have hb : q.any id = true := by cases h : q.any id <;> simp_all
        have hv : 0 < bitsValue q := by
          have := (ProtocolBoundedUnary.any_eq_false_iff q).not.mp hz
          omega
        have hs := zero_test q [] payload count
        simp only [hb, ↓reduceIte] at hs
        refine ⟨2 * q.length + 2 + 1, by simp; omega, q, rfl, ?_⟩
        have he := (run_add hs 1).trans (run_succ (step_source_nil (none, true) q payload count) 0)
        simpa [Nat.ne_of_gt hv] using he
  | cons b source ih =>
      by_cases hz : q.any id = false
      · have hv := (ProtocolBoundedUnary.any_eq_false_iff q).mp hz
        refine ⟨2 * q.length + 2, by simp [hv]; omega, q, rfl, ?_⟩
        simpa [hz, hv] using zero_test q (b :: source) payload count
      · have hb : q.any id = true := by cases h : q.any id <;> simp_all
        have hv : 0 < bitsValue q := by
          have := (ProtocolBoundedUnary.any_eq_false_iff q).not.mp hz
          omega
        have hspec := ProtocolBinaryCounter.subOne_spec q
        cases heq : ProtocolBinaryCounter.subOne q with
        | none => simp only [heq] at hspec; omega
        | some q₁ =>
            simp only [heq] at hspec
            obtain ⟨t, ht, q', hlen, hr⟩ := ih q₁ (b :: payload) (true :: count)
            have hs := zero_test q (b :: source) payload count
            simp only [hb, ↓reduceIte] at hs
            have hsource := run_succ (step_source_cons (none, true) b q source payload count) 0
            have hsub := subtract_correct (some b, true) q q₁ source [] (b :: payload) (true :: count) heq
            simp only [List.length_nil, Nat.add_zero, List.reverse_nil, List.nil_append] at hsub
            have hpre := (run_add ((run_add hs 1).trans hsource) (2 * q.length + 2)).trans hsub
            have hn : bitsValue q = bitsValue q₁ + 1 := by omega
            have hm : min (bitsValue q) (b :: source).length = min (bitsValue q₁) source.length + 1 := by
              simp only [List.length_cons]; omega
            refine ⟨(2 * q.length + 2 + 1) + (2 * q.length + 2) + t, ?_, q', hlen.trans hspec.2, ?_⟩
            · rw [hspec.2] at ht
              rw [hm]
              nlinarith
            · have hc : (bitsValue q₁ ≤ source.length) = (bitsValue q ≤ (b :: source).length) := by
                simp only [List.length_cons]; exact propext (by omega)
              have hcount : List.replicate (min (bitsValue q₁) source.length) true ++ true :: count =
                  List.replicate (min (bitsValue q₁) source.length + 1) true ++ count := by
                rw [List.replicate_add, List.append_assoc]; rfl
              have he := (run_add hpre t).trans hr
              rw [hm]
              simpa only [hn, List.drop_succ_cons, List.take_succ_cons, List.reverse_cons,
                List.append_assoc, List.singleton_append, hcount, hc] using he

end EthInapproximability.CurrentPaper.SourceListMachineFieldsCore
