import EthInapproximability.CurrentPaper.SamplerMachineEnumeration

/-!
# First-success search with an actual finite predicate subroutine

Source: locked v8 `E-exact-details.tex`, the exhaustive search for an
irreducible monic polynomial. This reusable controller invokes a supplied
finite program on each coefficient counter, stops at its first acceptance,
and otherwise increments the counter. Its operational theorem takes the
actual correctness/runtime proof of that supplied program as an explicit
subroutine premise; it does not assert the complete irreducible search until
the concrete factor-test controller is installed.
-/

namespace EthInapproximability.CurrentPaper.SamplerMachineSearch

set_option maxHeartbeats 1000000

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open SamplerMachineIncrement SamplerEnumeration

inductive Admin where
  | check | scan | restore | carry | carryRestore
  deriving DecidableEq, Fintype

variable {K L V : Type*} [DecidableEq K]

abbrev Stack (K : Type*) := K ⊕ Unit
abbrev Label (L : Type*) := L ⊕ Admin
abbrev Control (V : Type*) := V × (Bool × Option Bool)
abbrev Config (K L V : Type*) := TM2.Cfg (fun _ : Stack K => Bool) (Label L) (Control V)

def program (P : L → TM2.Stmt (fun _ : K => Bool) L V)
    (source : K) (start : L) (v0 : V) (accept : V → Bool) :
    Label L → TM2.Stmt (fun _ : Stack K => Bool) (Label L) (Control V)
  | .inl l => liftStmt (some .check) (P l)
  | .inr .check => branch (fun s => accept s.1)
      halt (load (fun s => (s.1, true, none)) (goto (fun _ => .inr .scan)))
  | .inr .scan => pop (.inl source) (fun s b => (s.1, s.2.1, b))
      (branch (fun s => s.2.2.isSome)
        (push (.inr ()) (fun s => s.2.2.getD false)
          (load (fun s => (s.1, s.2.1 && s.2.2.getD false, none))
            (goto (fun _ => .inr .scan))))
        (goto (fun _ => .inr .restore)))
  | .inr .restore => pop (.inr ()) (fun s b => (s.1, s.2.1, b))
      (branch (fun s => s.2.2.isSome)
        (push (.inl source) (fun s => s.2.2.getD false) (goto (fun _ => .inr .restore)))
        (branch (fun s => s.2.1) halt (goto (fun _ => .inr .carry))))
  | .inr .carry => pop (.inl source) (fun s b => (s.1, s.2.1, b))
      (branch (fun s => s.2.2.isSome)
        (branch (fun s => s.2.2.getD false)
          (push (.inr ()) (fun _ => false) (goto (fun _ => .inr .carry)))
          (push (.inl source) (fun _ => true) (goto (fun _ => .inr .carryRestore))))
        (goto (fun _ => .inr .carryRestore)))
  | .inr .carryRestore => pop (.inr ()) (fun s b => (s.1, s.2.1, b))
      (branch (fun s => s.2.2.isSome)
        (push (.inl source) (fun s => s.2.2.getD false) (goto (fun _ => .inr .carryRestore)))
        (load (fun _ => (v0, false, none)) (goto (fun _ => .inl start))))

def cfg (source : K) (S : K → List Bool) (l : Option (Label L))
    (s : Control V) (q work : List Bool) : Config K L V :=
  ⟨l, s, Sum.elim (Function.update S source q) (fun _ => work)⟩

def run (P : L → TM2.Stmt (fun _ : K => Bool) L V)
    (source : K) (start : L) (v0 : V) (accept : V → Bool) (t : ℕ)
    (q : Config K L V) := ((advance (program P source start v0 accept))^[t]) q

variable (P : L → TM2.Stmt (fun _ : K => Bool) L V)
  (source : K) (start : L) (v0 : V) (accept : V → Bool) (S : K → List Bool)

private theorem run_succ {c d : Config K L V}
    (h : TM2.step (program P source start v0 accept) c = some d) (n : ℕ) :
    run P source start v0 accept (n + 1) c = run P source start v0 accept n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add (m n : ℕ) (q : Config K L V) :
    run P source start v0 accept (m + n) q =
      run P source start v0 accept m (run P source start v0 accept n q) := by
  exact Function.iterate_add_apply _ _ _ _

private theorem step_scan_cons (v : V) (flag : Bool) (b : Option Bool)
    (x : Bool) (q work : List Bool) :
    TM2.step (program P source start v0 accept)
      (cfg source S (some (.inr .scan)) (v, flag, b) (x :: q) work) =
      some (cfg source S (some (.inr .scan)) (v, flag && x, none) q (x :: work)) := by
  simp only [TM2.step, program, TM2.stepAux, cfg, Sum.elim_inl,
    Function.update_self, List.head?_cons, List.tail_cons, Option.isSome_some,
    Option.getD_some, Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  rcases k with k | k
  · by_cases h : k = source <;>
      simp only [Function.update_apply, Sum.elim_inl, Sum.inl.injEq, h, ↓reduceIte, reduceCtorEq]
  · rfl

private theorem step_scan_nil (v : V) (flag : Bool) (b : Option Bool) (work : List Bool) :
    TM2.step (program P source start v0 accept)
      (cfg source S (some (.inr .scan)) (v, flag, b) [] work) =
      some (cfg source S (some (.inr .restore)) (v, flag, none) [] work) := by
  simp only [TM2.step, program, TM2.stepAux, cfg, Sum.elim_inl,
    Function.update_self, List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  rcases k with k | k
  · by_cases h : k = source <;>
      simp only [Function.update_apply, Sum.elim_inl, Sum.inl.injEq, h, ↓reduceIte, reduceCtorEq]
  · rfl

theorem scan_run (v : V) (flag : Bool) (b : Option Bool) (q work : List Bool) :
    run P source start v0 accept (q.length + 1)
      (cfg source S (some (.inr .scan)) (v, flag, b) q work) =
      cfg source S (some (.inr .restore)) (v, flag && q.all id, none)
        [] (q.reverse ++ work) := by
  induction q generalizing flag b work with
  | nil =>
      simpa using run_succ P source start v0 accept
        (step_scan_nil P source start v0 accept S v flag b work) 0
  | cons x q ih =>
      rw [List.length_cons, run_succ P source start v0 accept
        (step_scan_cons P source start v0 accept S v flag b x q work)]
      simpa only [List.all_cons, id_eq, Bool.and_assoc, List.reverse_cons,
        List.append_assoc, List.singleton_append] using ih (flag && x) none (x :: work)

private theorem step_restore_cons (v : V) (flag : Bool) (b : Option Bool)
    (x : Bool) (q work : List Bool) :
    TM2.step (program P source start v0 accept)
      (cfg source S (some (.inr .restore)) (v, flag, b) q (x :: work)) =
      some (cfg source S (some (.inr .restore)) (v, flag, some x) (x :: q) work) := by
  simp only [TM2.step, program, TM2.stepAux, cfg, Sum.elim_inr,
    List.head?_cons, List.tail_cons, Option.isSome_some,
    Option.getD_some, Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  rcases k with k | k
  · by_cases h : k = source <;>
      simp only [Function.update_apply, Sum.elim_inl, Sum.inl.injEq, h, ↓reduceIte, reduceCtorEq]
  · rfl

private theorem step_restore_nil (v : V) (b : Option Bool) (q : List Bool) :
    TM2.step (program P source start v0 accept)
      (cfg source S (some (.inr .restore)) (v, false, b) q []) =
      some (cfg source S (some (.inr .carry)) (v, false, none) q []) := by
  simp only [TM2.step, program, TM2.stepAux, cfg, Sum.elim_inr,
    List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  rcases k with k | k <;> rfl

theorem restore_run (v : V) (b : Option Bool) (q work : List Bool) :
    run P source start v0 accept (work.length + 1)
      (cfg source S (some (.inr .restore)) (v, false, b) q work) =
      cfg source S (some (.inr .carry)) (v, false, none) (work.reverse ++ q) [] := by
  induction work generalizing b q with
  | nil =>
      simpa using run_succ P source start v0 accept
        (step_restore_nil P source start v0 accept S v b q) 0
  | cons x work ih =>
      rw [List.length_cons, run_succ P source start v0 accept
        (step_restore_cons P source start v0 accept S v false b x q work)]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
        ih (some x) (x :: q)

private theorem step_carry_true (v : V) (b : Option Bool) (q work : List Bool) :
    TM2.step (program P source start v0 accept)
      (cfg source S (some (.inr .carry)) (v, false, b) (true :: q) work) =
      some (cfg source S (some (.inr .carry)) (v, false, some true) q (false :: work)) := by
  simp only [TM2.step, program, TM2.stepAux, cfg, Sum.elim_inl,
    Function.update_self, List.head?_cons, List.tail_cons, Option.isSome_some,
    Option.getD_some, Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  rcases k with k | k
  · by_cases h : k = source <;>
      simp only [Function.update_apply, Sum.elim_inl, Sum.inl.injEq, h, ↓reduceIte, reduceCtorEq]
  · rfl

private theorem step_carry_false (v : V) (b : Option Bool) (q work : List Bool) :
    TM2.step (program P source start v0 accept)
      (cfg source S (some (.inr .carry)) (v, false, b) (false :: q) work) =
      some (cfg source S (some (.inr .carryRestore)) (v, false, some false) (true :: q) work) := by
  simp only [TM2.step, program, TM2.stepAux, cfg, Sum.elim_inl,
    Function.update_self, List.head?_cons, List.tail_cons, Option.isSome_some,
    Option.getD_some, Bool.cond_true, Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  rcases k with k | k
  · by_cases h : k = source <;>
      simp only [Function.update_apply, Sum.elim_inl, Sum.inl.injEq, h, ↓reduceIte, reduceCtorEq]
  · rfl

private theorem step_carry_nil (v : V) (b : Option Bool) (work : List Bool) :
    TM2.step (program P source start v0 accept)
      (cfg source S (some (.inr .carry)) (v, false, b) [] work) =
      some (cfg source S (some (.inr .carryRestore)) (v, false, none) [] work) := by
  simp only [TM2.step, program, TM2.stepAux, cfg, Sum.elim_inl,
    Function.update_self, List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  rcases k with k | k
  · by_cases h : k = source <;>
      simp only [Function.update_apply, Sum.elim_inl, Sum.inl.injEq, h, ↓reduceIte, reduceCtorEq]
  · rfl

private theorem step_carryRestore_cons (v : V) (b : Option Bool)
    (x : Bool) (q work : List Bool) :
    TM2.step (program P source start v0 accept)
      (cfg source S (some (.inr .carryRestore)) (v, false, b) q (x :: work)) =
      some (cfg source S (some (.inr .carryRestore)) (v, false, some x) (x :: q) work) := by
  simp only [TM2.step, program, TM2.stepAux, cfg, Sum.elim_inr,
    List.head?_cons, List.tail_cons, Option.isSome_some,
    Option.getD_some, Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  rcases k with k | k
  · by_cases h : k = source <;>
      simp only [Function.update_apply, Sum.elim_inl, Sum.inl.injEq, h, ↓reduceIte, reduceCtorEq]
  · rfl

private theorem step_carryRestore_nil (v : V) (b : Option Bool) (q : List Bool) :
    TM2.step (program P source start v0 accept)
      (cfg source S (some (.inr .carryRestore)) (v, false, b) q []) =
      some (cfg source S (some (.inl start)) (v0, false, none) q []) := by
  simp only [TM2.step, program, TM2.stepAux, cfg, Sum.elim_inr,
    List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  rcases k with k | k <;> rfl

theorem carryRestore_run (v : V) (b : Option Bool) (q work : List Bool) :
    run P source start v0 accept (work.length + 1)
      (cfg source S (some (.inr .carryRestore)) (v, false, b) q work) =
      cfg source S (some (.inl start)) (v0, false, none) (work.reverse ++ q) [] := by
  induction work generalizing b q with
  | nil =>
      simpa using run_succ P source start v0 accept
        (step_carryRestore_nil P source start v0 accept S v b q) 0
  | cons x work ih =>
      rw [List.length_cons, run_succ P source start v0 accept
        (step_carryRestore_cons P source start v0 accept S v b x q work)]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
        ih (some x) (x :: q)

theorem carry_run (v : V) (b : Option Bool) (q work : List Bool) :
    run P source start v0 accept (2 * carryCount q + work.length + 2)
      (cfg source S (some (.inr .carry)) (v, false, b) q work) =
      cfg source S (some (.inl start)) (v0, false, none) (work.reverse ++ increment q) [] := by
  induction q generalizing b work with
  | nil =>
      simpa [carryCount, increment, Nat.add_assoc] using
        (run_succ P source start v0 accept
          (step_carry_nil P source start v0 accept S v b work) (work.length + 1)).trans
          (carryRestore_run P source start v0 accept S v none [] work)
  | cons x q ih =>
      cases x with
      | false =>
          simpa [carryCount, increment, Nat.add_assoc] using
            (run_succ P source start v0 accept
              (step_carry_false P source start v0 accept S v b q work) (work.length + 1)).trans
              (carryRestore_run P source start v0 accept S v (some false) (true :: q) work)
      | true =>
          have hs := (run_succ P source start v0 accept
            (step_carry_true P source start v0 accept S v b q work)
              (2 * carryCount q + (false :: work).length + 2)).trans
                (ih (some true) (false :: work))
          have ht : 2 * carryCount (true :: q) + work.length + 2 =
              (2 * carryCount q + (false :: work).length + 2) + 1 := by
            simp only [carryCount, List.length_cons]
            omega
          rw [ht]
          simpa only [increment, List.reverse_cons, List.append_assoc,
            List.singleton_append] using hs

private theorem step_reject (v : V) (q : List Bool) (h : accept v = false) :
    TM2.step (program P source start v0 accept)
      (cfg source S (some (.inr .check)) (v, false, none) q []) =
      some (cfg source S (some (.inr .scan)) (v, true, none) q []) := by
  simp only [TM2.step, TM2.stepAux, program, cfg, h, Bool.cond_false]

private theorem step_accept (v : V) (q : List Bool) (h : accept v = true) :
    TM2.step (program P source start v0 accept)
      (cfg source S (some (.inr .check)) (v, false, none) q []) =
      some (cfg source S none (v, false, none) q []) := by
  simp only [TM2.step, TM2.stepAux, program, cfg, h, Bool.cond_true]

/-- Rejection advances the fixed-width counter, preserving every other stack.
The all-ones test itself is charged and proved operationally. -/
theorem reject_run (v : V) (q : List Bool)
    (ha : accept v = false) (ho : q.all id = false) :
    ∃ t ≤ 4 * q.length + 5,
      run P source start v0 accept t
        (cfg source S (some (.inr .check)) (v, false, none) q []) =
        cfg source S (some (.inl start)) (v0, false, none) (increment q) [] := by
  have hs := scan_run P source start v0 accept S v true none q []
  simp only [Bool.true_and, ho, List.append_nil] at hs
  have hr := restore_run P source start v0 accept S v none [] q.reverse
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hr
  have hc := carry_run P source start v0 accept S v none q []
  simp only [List.length_nil, Nat.add_zero, List.reverse_nil, List.nil_append] at hc
  refine ⟨(2 * carryCount q + 2) + (q.length + 1) + (q.length + 1) + 1, ?_, ?_⟩
  · have := carryCount_le_length q
    omega
  · rw [run_succ P source start v0 accept (step_reject P source start v0 accept S v q ha)]
    rw [run_add, hs, run_add, hr]
    exact hc

/-- Invocation of the actual predicate, with no transition surcharge.
The predicate contract says that its work bank is restored before return. -/
theorem predicate_call (q : List Bool) (v : V) (t : ℕ)
    (h : ((advance P)^[t]) ⟨some start, v0, Function.update S source q⟩ =
      ⟨none, v, Function.update S source q⟩) :
    ∃ t' ≤ t,
      run P source start v0 accept t'
        (cfg source S (some (.inl start)) (v0, false, none) q []) =
        cfg source S (some (.inr .check)) (v, false, none) q [] := by
  have hh : (((advance P)^[t]) ⟨some start, v0, Function.update S source q⟩).l = none := by
    rw [h]
  obtain ⟨t', ht', hr⟩ := BitMachineSubroutine.lift_outputs P
    (program P source start v0 accept) (some .check) (fun _ => rfl)
    (false, (none : Option Bool)) (fun _ : Unit => [])
    ⟨some start, v0, Function.update S source q⟩ t hh
  rw [h] at hr
  exact ⟨t', ht', hr⟩

/-- First-success correctness for a suffix of the exact binary enumeration.
The sole predicate premise is a bounded run of the supplied *actual* finite
program on every width-`n` input, restoring its bank and returning the stated
Boolean value in finite control. This reusable lemma is not itself a claim
that irreducibility has been implemented. -/
theorem search_run (n T : ℕ) (pred : List Bool → Bool)
    (hP : ∀ q : List Bool, q.length = n →
      ∃ (t : ℕ) (v : V), t ≤ T ∧
        ((advance P)^[t]) ⟨some start, v0, Function.update S source q⟩ =
          ⟨none, v, Function.update S source q⟩ ∧ accept v = pred q)
    (r : ℕ) (q found : List Bool) (hlen : q.length = n)
    (hcount : EncodedCommunication.bitsValue q + r + 1 = 2 ^ n)
    (hfind : (List.iterate increment q (r + 1)).find? pred = some found) :
    ∃ (t : ℕ) (v : V), t ≤ (r + 1) * (T + 4 * n + 6) ∧ accept v = true ∧
      run P source start v0 accept t
        (cfg source S (some (.inl start)) (v0, false, none) q []) =
        cfg source S none (v, false, none) found [] := by
  induction r generalizing q with
  | zero =>
      have hp : pred q = true := by
        cases he : pred q <;> simp_all [List.iterate]
      have hf : found = q := by simpa [List.iterate, hp] using hfind.symm
      subst found
      obtain ⟨t, v, ht, hr, hv⟩ := hP q hlen
      obtain ⟨tp, htp, hcall⟩ := predicate_call P source start v0 accept S q v t hr
      have ha : accept v = true := hv.trans hp
      refine ⟨1 + tp, v, by omega, ha, ?_⟩
      simp only [run, Function.iterate_add_apply]
      change run P source start v0 accept 1 (run P source start v0 accept tp _) = _
      rw [hcall]
      exact run_succ P source start v0 accept (step_accept P source start v0 accept S v q ha) 0
  | succ r ih =>
      obtain ⟨t, v, ht, hr, hv⟩ := hP q hlen
      obtain ⟨tp, htp, hcall⟩ := predicate_call P source start v0 accept S q v t hr
      cases hp : pred q with
      | true =>
          have hf : found = q := by simpa [List.iterate, hp] using hfind.symm
          subst found
          have ha : accept v = true := hv.trans hp
          refine ⟨1 + tp, v, ?_, ha, ?_⟩
          · nlinarith
          · simp only [run, Function.iterate_add_apply]
            change run P source start v0 accept 1 (run P source start v0 accept tp _) = _
            rw [hcall]
            exact run_succ P source start v0 accept
              (step_accept P source start v0 accept S v q ha) 0
      | false =>
          have ho : q.all id = false := by
            cases he : q.all id with
            | false => rfl
            | true =>
                have hm := (SamplerMachineEnumeration.overflow_iff_max q).mp he
                rw [hlen] at hm
                omega
          have hnlen : (increment q).length = n := by rw [increment_length, hlen]
          have hncount : EncodedCommunication.bitsValue (increment q) + r + 1 = 2 ^ n := by
            rw [SamplerMachineEnumeration.increment_value_of_not_overflow q ho]
            omega
          have hnfind : (List.iterate increment (increment q) (r + 1)).find? pred =
              some found := by simpa [List.iterate, hp] using hfind
          obtain ⟨tr, vr, htr, hva, hrr⟩ := ih (increment q) hnlen hncount hnfind
          obtain ⟨ts, hts, hs⟩ := reject_run P source start v0 accept S v q (hv.trans hp) ho
          refine ⟨tr + ts + tp, vr, ?_, hva, ?_⟩
          · rw [hlen] at hts
            nlinarith
          · simp only [run, Function.iterate_add_apply]
            change run P source start v0 accept tr
              (run P source start v0 accept ts (run P source start v0 accept tp _)) = _
            rw [hcall, hs, hrr]

/-- The first accepted coefficient word in the complete, exact enumeration.
The bound is polynomial in the field cardinality `2^n` provided the concrete
predicate bound is; neither this implication nor the program's existence
asserts that a not-yet-installed predicate is efficient. -/
theorem search_allWords (n T : ℕ) (pred : List Bool → Bool)
    (hP : ∀ q : List Bool, q.length = n →
      ∃ (t : ℕ) (v : V), t ≤ T ∧
        ((advance P)^[t]) ⟨some start, v0, Function.update S source q⟩ =
          ⟨none, v, Function.update S source q⟩ ∧ accept v = pred q)
    (found : List Bool) (hfind : (counterWords n).find? pred = some found) :
    ∃ (t : ℕ) (v : V), t ≤ 2 ^ n * (T + 4 * n + 6) ∧ accept v = true ∧
      run P source start v0 accept t
        (cfg source S (some (.inl start)) (v0, false, none) (List.replicate n false) []) =
        cfg source S none (v, false, none) found [] := by
  have hpos : 0 < 2 ^ n := by positivity
  have hc : 2 ^ n - 1 + 1 = 2 ^ n := by omega
  have hzall : ∀ m, EncodedCommunication.bitsValue (List.replicate m false) = 0 := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => simp [EncodedCommunication.bitsValue, List.replicate_succ, ih, Nat.bit_val]
  have hz := hzall n
  have hr := search_run P source start v0 accept S n T pred hP (2 ^ n - 1)
    (List.replicate n false) found (by simp) (by rw [hz]; omega) (by
      simpa only [hc] using hfind)
  simpa only [hc] using hr

private theorem step_restore_done (v : V) (b : Option Bool) (q : List Bool) :
    TM2.step (program P source start v0 accept)
      (cfg source S (some (.inr .restore)) (v, true, b) q []) =
      some (cfg source S none (v, true, none) q []) := by
  simp only [TM2.step, program, TM2.stepAux, cfg, Sum.elim_inr,
    List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false,
    Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  rcases k with k | k <;> rfl

theorem restore_done_run (v : V) (b : Option Bool) (q work : List Bool) :
    run P source start v0 accept (work.length + 1)
      (cfg source S (some (.inr .restore)) (v, true, b) q work) =
      cfg source S none (v, true, none) (work.reverse ++ q) [] := by
  induction work generalizing b q with
  | nil =>
      simpa using run_succ P source start v0 accept
        (step_restore_done P source start v0 accept S v b q) 0
  | cons x work ih =>
      rw [List.length_cons, run_succ P source start v0 accept
        (step_restore_cons P source start v0 accept S v true b x q work)]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
        ih (some x) (x :: q)

theorem exhausted_run (v : V) (q : List Bool)
    (ha : accept v = false) (ho : q.all id = true) :
    run P source start v0 accept (2 * q.length + 3)
      (cfg source S (some (.inr .check)) (v, false, none) q []) =
      cfg source S none (v, true, none) q [] := by
  have hs := scan_run P source start v0 accept S v true none q []
  simp only [Bool.true_and, ho, List.append_nil] at hs
  have hr := restore_done_run P source start v0 accept S v none [] q.reverse
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hr
  have ht : 2 * q.length + 3 = ((q.length + 1) + (q.length + 1)) + 1 := by omega
  rw [ht, run_succ P source start v0 accept (step_reject P source start v0 accept S v q ha)]
  rw [run_add, hs, hr]

/-- If no counter value is accepted, the same actual program exhausts the
enumeration and halts with its separate finite overflow flag set to true. -/
theorem search_none (n T : ℕ) (pred : List Bool → Bool)
    (hP : ∀ q : List Bool, q.length = n →
      ∃ (t : ℕ) (v : V), t ≤ T ∧
        ((advance P)^[t]) ⟨some start, v0, Function.update S source q⟩ =
          ⟨none, v, Function.update S source q⟩ ∧ accept v = pred q)
    (r : ℕ) (q : List Bool) (hlen : q.length = n)
    (hcount : EncodedCommunication.bitsValue q + r + 1 = 2 ^ n)
    (hfind : (List.iterate increment q (r + 1)).find? pred = none) :
    ∃ (t : ℕ) (v : V), t ≤ (r + 1) * (T + 4 * n + 6) ∧ accept v = false ∧
      run P source start v0 accept t
        (cfg source S (some (.inl start)) (v0, false, none) q []) =
        cfg source S none (v, true, none) ((increment^[r]) q) [] := by
  induction r generalizing q with
  | zero =>
      have hp : pred q = false := by
        cases he : pred q <;> simp_all [List.iterate]
      obtain ⟨t, v, ht, hr, hv⟩ := hP q hlen
      obtain ⟨tp, htp, hcall⟩ := predicate_call P source start v0 accept S q v t hr
      have ha : accept v = false := hv.trans hp
      have ho : q.all id = true := (SamplerMachineEnumeration.overflow_iff_max q).mpr (by
        rw [hlen]
        simpa using hcount)
      refine ⟨(2 * q.length + 3) + tp, v, by rw [hlen]; omega, ha, ?_⟩
      simp only [run, Function.iterate_add_apply]
      change run P source start v0 accept (2 * q.length + 3)
        (run P source start v0 accept tp _) = _
      rw [hcall]
      exact exhausted_run P source start v0 accept S v q ha ho
  | succ r ih =>
      obtain ⟨t, v, ht, hr, hv⟩ := hP q hlen
      obtain ⟨tp, htp, hcall⟩ := predicate_call P source start v0 accept S q v t hr
      have hp : pred q = false := by
        cases he : pred q <;> simp_all [List.iterate]
      have ho : q.all id = false := by
        cases he : q.all id with
        | false => rfl
        | true =>
            have hm := (SamplerMachineEnumeration.overflow_iff_max q).mp he
            rw [hlen] at hm
            omega
      have hnlen : (increment q).length = n := by rw [increment_length, hlen]
      have hncount : EncodedCommunication.bitsValue (increment q) + r + 1 = 2 ^ n := by
        rw [SamplerMachineEnumeration.increment_value_of_not_overflow q ho]
        omega
      have hnfind : (List.iterate increment (increment q) (r + 1)).find? pred = none := by
        simpa [List.iterate, hp] using hfind
      obtain ⟨tr, vr, htr, hva, hrr⟩ := ih (increment q) hnlen hncount hnfind
      obtain ⟨ts, hts, hs⟩ := reject_run P source start v0 accept S v q (hv.trans hp) ho
      refine ⟨tr + ts + tp, vr, ?_, hva, ?_⟩
      · rw [hlen] at hts
        nlinarith
      · simp only [run, Function.iterate_add_apply]
        change run P source start v0 accept tr
          (run P source start v0 accept ts (run P source start v0 accept tp _)) = _
        rw [hcall, hs, hrr]
        simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]

end EthInapproximability.CurrentPaper.SamplerMachineSearch
