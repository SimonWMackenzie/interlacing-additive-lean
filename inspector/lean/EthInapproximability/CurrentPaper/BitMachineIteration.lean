import EthInapproximability.CurrentPaper.BitMachineSubroutine
import EthInapproximability.CurrentPaper.BitMachineClearBank

/-!
# Budgeted iteration of a finite Boolean-stack program

Source: locked v8 `B-effectivity-details.tex`, concrete bounded loops in the
sampler and materializer. The counter is a literal stack. Each call is followed
by two charged data transfers and complete local-bank cleanup. The program
never carries an unbounded numeric register or a host-language callback.
-/

namespace EthInapproximability.CurrentPaper.BitMachineIteration

open Turing Turing.TM2.Stmt
open BitMachine BitMachineEncoding BitMachineComposition BitMachineSubroutine
open scoped BigOperators

variable (M : Machine)

inductive Admin (n : ℕ) where
  | testFuel | moveOut | clear (i : Fin (n + 1)) | moveIn
  deriving DecidableEq, Fintype

abbrev Stack := Fin M.stackCount ⊕ Fin 2
abbrev Label := Fin M.labelCount ⊕ Admin M.stackCount
abbrev Control := Fin M.controlCount × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack M => Bool) (Label M) (Control M)

def program : Label M → TM2.Stmt (fun _ : Stack M => Bool) (Label M) (Control M)
  | .inl l => liftStmt (some (.moveOut : Admin M.stackCount)) (M.program l)
  | .inr .testFuel => pop (.inr 0) (fun v b => (v.1, b))
      (branch (fun v => v.2.isSome)
        (load (fun _ => (M.initial, none)) (goto (fun _ => .inl M.start))) halt)
  | .inr .moveOut => pop (.inl M.output) (fun v b => (v.1, b))
      (branch (fun v => v.2.isSome)
        (push (.inr 1) (fun v => v.2.getD false) (goto (fun _ => .inr .moveOut)))
        (load (fun v => (v.1, none)) (goto (fun _ => .inr (.clear 0)))))
  | .inr (.clear i) =>
      if h : i.val < M.stackCount then
        pop (.inl ⟨i.val, h⟩) (fun v b => (v.1, b))
          (branch (fun v => v.2.isSome)
            (load (fun v => (v.1, none)) (goto (fun _ => .inr (.clear i))))
            (load (fun v => (v.1, none))
              (goto (fun _ => .inr (.clear ⟨i.val + 1, by omega⟩)))))
      else load (fun _ => (M.initial, none)) (goto (fun _ => .inr .moveIn))
  | .inr .moveIn => pop (.inr 1) (fun v b => (v.1, b))
      (branch (fun v => v.2.isSome)
        (push (.inl M.input) (fun v => v.2.getD false) (goto (fun _ => .inr .moveIn)))
        (load (fun _ => (M.initial, none)) (goto (fun _ => .inr .testFuel))))

def foreign (fuel saved : List Bool) : Fin 2 → List Bool :=
  fun k => if k = 0 then fuel else saved

@[simp] theorem foreign_zero (fuel saved : List Bool) : foreign fuel saved 0 = fuel := rfl
@[simp] theorem foreign_one (fuel saved : List Bool) : foreign fuel saved 1 = saved := rfl

@[simp] theorem foreign_update_zero (fuel saved q : List Bool) :
    Function.update (foreign fuel saved) 0 q = foreign q saved := by
  funext k
  fin_cases k <;> simp [foreign]

@[simp] theorem foreign_update_one (fuel saved q : List Bool) :
    Function.update (foreign fuel saved) 1 q = foreign fuel q := by
  funext k
  fin_cases k <;> simp [foreign]

theorem sum_update_right {K J : Type*} [DecidableEq K] [DecidableEq J]
    (S : K → List Bool) (T : J → List Bool) (k : J) (q : List Bool) :
    Function.update (Sum.elim S T) (.inr k) q = Sum.elim S (Function.update T k q) := by
  funext j
  cases j with
  | inl j => simp
  | inr j =>
      by_cases h : j = k
      · subst j; simp
      · simp [h]

def adminCfg (label : Admin M.stackCount) (v : Fin M.controlCount) (s : Option Bool)
    (bank : Fin M.stackCount → List Bool) (fuel saved : List Bool) : Config M :=
  ⟨some (.inr label), (v, s), Sum.elim bank (foreign fuel saved)⟩

def ready (data fuel : List Bool) : Config M :=
  adminCfg M .testFuel M.initial none (M.init data).stk fuel []

def run (t : ℕ) (c : Config M) : Config M := ((advance (program M))^[t]) c

private theorem run_succ {c d : Config M} (h : advance (program M) c = d) (t : ℕ) :
    run M (t + 1) c = run M t d := by
  simp only [run, Function.iterate_succ_apply, h]

private theorem run_add {c d : Config M} {t : ℕ} (h : run M t c = d) (u : ℕ) :
    run M (t + u) c = run M u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

theorem moveOut_step_cons (v : Fin M.controlCount) (s : Option Bool)
    (S : Fin M.stackCount → List Bool) (b : Bool) (q fuel saved : List Bool)
    (hS : S M.output = b :: q) :
    advance (program M) (adminCfg M .moveOut v s S fuel saved) =
      adminCfg M .moveOut v (some b) (Function.update S M.output q) fuel (b :: saved) := by
  simp only [advance, adminCfg, TM2.step, program, TM2.stepAux,
    Sum.elim_inl, hS, List.head?_cons, List.tail_cons, Option.isSome_some,
    cond_true, Option.getD_some]
  congr 1
  funext k
  rcases k with k | k
  · simp only [Function.update_apply, Sum.elim_inl, Sum.elim_inr,
      Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl,
      ↓reduceIte, foreign_one]
  · fin_cases k <;> simp only [Function.update_apply, Sum.elim_inl, Sum.elim_inr,
      Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl,
      ↓reduceIte, foreign_zero, foreign_one] <;> rfl

theorem moveOut_step_nil (v : Fin M.controlCount) (s : Option Bool)
    (S : Fin M.stackCount → List Bool) (fuel saved : List Bool) (hS : S M.output = []) :
    advance (program M) (adminCfg M .moveOut v s S fuel saved) =
      adminCfg M (.clear 0) v none S fuel saved := by
  simp only [advance, adminCfg, TM2.step, program, TM2.stepAux,
    Sum.elim_inl, hS, List.head?_nil, List.tail_nil, Option.isSome_none,
    cond_false, Option.getD_some]
  congr 1
  funext k
  rcases k with k | k
  · by_cases h : k = M.output
    · subst k; simp [hS]
    · simp [h]
  · simp

theorem moveOut_run (v : Fin M.controlCount) (s : Option Bool)
    (S : Fin M.stackCount → List Bool) (q fuel saved : List Bool) (hS : S M.output = q) :
    run M (q.length + 1) (adminCfg M .moveOut v s S fuel saved) =
      adminCfg M (.clear 0) v none (Function.update S M.output []) fuel (q.reverse ++ saved) := by
  induction q generalizing S s saved with
  | nil =>
      rw [show ([] : List Bool).length + 1 = 0 + 1 by rfl,
        run_succ M (moveOut_step_nil M v s S fuel saved hS)]
      have hu : Function.update S M.output [] = S := by
        rw [← hS, Function.update_eq_self]
      simp [run, hu]
  | cons b q ih =>
      rw [List.length_cons, run_succ M (moveOut_step_cons M v s S b q fuel saved hS),
        ih _ _ _ (Function.update_self _ _ _)]
      simp [List.reverse_cons, List.append_assoc, Function.update_idem]

theorem component_run {input output fuel : List Bool} {bound : ℕ}
    (h : M.OutputsWithin input output bound) :
    ∃ (t : ℕ) (c : M.Config), t ≤ bound ∧ c.l = none ∧ c.stk M.output = output ∧
      run M t (liftCfg (some (.moveOut : Admin M.stackCount)) none
        (foreign fuel []) (M.init input)) =
        adminCfg M .moveOut c.var none c.stk fuel [] ∧
      ∀ k, (c.stk k).length ≤ input.length + bound * M.pushBound := by
  obtain ⟨t, ht, hhalt, hout, hfirst⟩ := BitMachineCompositionArithmetic.first_halt M h
  refine ⟨t, M.run t (M.init input), ht, hhalt, hout, ?_, ?_⟩
  · have hr := lift_run_until M.program (program M) (some (.moveOut : Admin M.stackCount))
      (fun _ => rfl) none (foreign fuel []) (M.init input) t hfirst
    change run M t _ = liftCfg (some (.moveOut : Admin M.stackCount)) none
      (foreign fuel []) (M.run t (M.init input)) at hr
    rw [show liftCfg (some (.moveOut : Admin M.stackCount)) none (foreign fuel [])
        (M.run t (M.init input)) =
        adminCfg M .moveOut (M.run t (M.init input)).var none
          (M.run t (M.init input)).stk fuel [] by
        simp only [liftCfg, adminCfg, hhalt, Option.map_some]] at hr
    exact hr
  · intro k
    have hk := run_length M (M.init input) k t
    have hi : ((M.init input).stk k).length ≤ input.length := by
      simp only [Machine.init]
      split_ifs <;> simp
    nlinarith

theorem clear_run (v : Fin M.controlCount) (S : Fin M.stackCount → List Bool)
    (fuel saved : List Bool) :
    run M ((∑ i, (S i).length) + M.stackCount + 1)
      (adminCfg M (.clear 0) v none S fuel saved) =
      adminCfg M .moveIn M.initial none (fun _ => []) fuel saved := by
  have hc := BitMachineClearBank.clear_bank_run (program M) (fun _ => M.initial)
    (.inr .moveIn) M.stackCount (fun i => (Sum.inl i : Stack M)) Sum.inl_injective
    (fun i => (.inr (.clear i) : Label M))
    (fun i => by simp only [program, Fin.val_castSucc, i.isLt, ↓reduceDIte]; rfl)
    (by simp only [program, Fin.val_last, lt_self_iff_false, ↓reduceDIte]; rfl)
    v (Sum.elim S (foreign fuel saved))
  have he : BitMachineClearBank.cleared (fun i => (Sum.inl i : Stack M))
      (Sum.elim S (foreign fuel saved)) = Sum.elim (fun _ => []) (foreign fuel saved) := by
    funext k
    cases k with
    | inl k => simp [BitMachineClearBank.cleared]
    | inr k => simp [BitMachineClearBank.cleared]
  simpa only [run, adminCfg, Sum.elim_inl, he] using hc

theorem moveIn_step_cons (v : Fin M.controlCount) (s : Option Bool)
    (S : Fin M.stackCount → List Bool) (b : Bool) (fuel saved : List Bool) :
    advance (program M) (adminCfg M .moveIn v s S fuel (b :: saved)) =
      adminCfg M .moveIn v (some b) (Function.update S M.input (b :: S M.input)) fuel saved := by
  simp only [advance, adminCfg, TM2.step, program, TM2.stepAux,
    Sum.elim_inl, Sum.elim_inr, foreign_one, List.head?_cons, List.tail_cons,
    Option.isSome_some, cond_true, Option.getD_some]
  congr 1
  funext k
  rcases k with k | k
  · simp only [Function.update_apply, Sum.elim_inl, Sum.elim_inr,
      Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl, ↓reduceIte]
  · fin_cases k <;> simp only [Function.update_apply, Sum.elim_inl, Sum.elim_inr,
      Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl,
      ↓reduceIte, foreign_zero, foreign_one] <;> rfl

theorem moveIn_step_nil (v : Fin M.controlCount) (s : Option Bool)
    (S : Fin M.stackCount → List Bool) (fuel : List Bool) :
    advance (program M) (adminCfg M .moveIn v s S fuel []) =
      adminCfg M .testFuel M.initial none S fuel [] := by
  simp only [advance, adminCfg, TM2.step, program, TM2.stepAux,
    Sum.elim_inr, foreign_one, List.head?_nil, List.tail_nil,
    Option.isSome_none, cond_false, Option.getD_some]
  congr 1
  funext k
  rcases k with k | k
  · simp
  · fin_cases k <;> simp [foreign]

theorem moveIn_run (v : Fin M.controlCount) (s : Option Bool)
    (S : Fin M.stackCount → List Bool) (fuel saved : List Bool) :
    run M (saved.length + 1) (adminCfg M .moveIn v s S fuel saved) =
      adminCfg M .testFuel M.initial none
        (Function.update S M.input (saved.reverse ++ S M.input)) fuel [] := by
  induction saved generalizing S s with
  | nil =>
      rw [show ([] : List Bool).length + 1 = 0 + 1 by rfl,
        run_succ M (moveIn_step_nil M v s S fuel)]
      simp [run]
  | cons b saved ih =>
      rw [List.length_cons, run_succ M (moveIn_step_cons M v s S b fuel saved), ih]
      simp only [Function.update_self, Function.update_idem,
        List.reverse_cons, List.append_assoc, List.singleton_append]

def resetTime (S : Fin M.stackCount → List Bool) : ℕ :=
  (S M.output).length + 1 +
    ((∑ i, ((Function.update S M.output []) i).length) + M.stackCount + 1) +
    ((S M.output).length + 1)

theorem reset_run (v : Fin M.controlCount) (S : Fin M.stackCount → List Bool)
    (fuel : List Bool) :
    run M (resetTime M S) (adminCfg M .moveOut v none S fuel []) =
      ready M (S M.output) fuel := by
  have ho := moveOut_run M v none S (S M.output) fuel [] rfl
  simp only [List.append_nil] at ho
  have hc := clear_run M v (Function.update S M.output []) fuel (S M.output).reverse
  have hi := moveIn_run M M.initial none (fun _ => []) fuel (S M.output).reverse
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hi
  have h := (run_add M ((run_add M ho _).trans hc) _).trans hi
  have he : Function.update (fun _ : Fin M.stackCount => ([] : List Bool)) M.input
      (S M.output) = (M.init (S M.output)).stk := by
    funext k
    simp only [Function.update_apply, Machine.init]
  simpa only [resetTime, ready, he] using h

theorem resetTime_le (S : Fin M.stackCount → List Bool) (L : ℕ)
    (hL : ∀ i, (S i).length ≤ L) :
    resetTime M S ≤ (M.stackCount + 2) * L + M.stackCount + 3 := by
  have hs : (∑ i, ((Function.update S M.output []) i).length) ≤ M.stackCount * L := by
    calc
      _ ≤ ∑ _ : Fin M.stackCount, L := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : i = M.output
        · subst i; simp
        · simpa [hi] using hL i
      _ = _ := by simp
  have ho := hL M.output
  unfold resetTime
  nlinarith

def finished (data : List Bool) : Config M :=
  ⟨none, (M.initial, none), Sum.elim (M.init data).stk (foreign [] [])⟩

theorem fuel_nil (data : List Bool) :
    advance (program M) (ready M data []) = finished M data := by
  simp only [advance, ready, adminCfg, finished, TM2.step, program, TM2.stepAux,
    Sum.elim_inr, foreign_zero, List.head?_nil, List.tail_nil,
    Option.isSome_none, cond_false, Option.getD_some]
  congr 1
  funext k
  rcases k with k | k
  · simp
  · fin_cases k <;> simp [foreign]

theorem fuel_cons (data : List Bool) (b : Bool) (fuel : List Bool) :
    advance (program M) (ready M data (b :: fuel)) =
      liftCfg (some (.moveOut : Admin M.stackCount)) none (foreign fuel []) (M.init data) := by
  simp only [advance, ready, adminCfg, TM2.step, program, TM2.stepAux,
    Sum.elim_inr, foreign_zero, List.head?_cons, List.tail_cons,
    Option.isSome_some, cond_true, Option.getD_some, liftCfg, Machine.init]
  congr 1
  funext k
  rcases k with k | k
  · simp
  · fin_cases k <;> simp [foreign]

def roundBound (inputLength time : ℕ) : ℕ :=
  time + (M.stackCount + 2) * (inputLength + time * M.pushBound) + M.stackCount + 4

/-- One literal call, including its fuel test, output movement, cleanup and
reset. The subroutine may halt earlier than its supplied time bound. -/
theorem round_run {input output : List Bool} (b : Bool) (fuel : List Bool) {bound : ℕ}
    (h : M.OutputsWithin input output bound) :
    ∃ t ≤ roundBound M input.length bound,
      run M t (ready M input (b :: fuel)) = ready M output fuel := by
  obtain ⟨t, c, ht, _, hout, hrun, hlen⟩ := component_run M (fuel := fuel) h
  have hstart := (run_succ M (fuel_cons M input b fuel) t).trans hrun
  have hreset := reset_run M c.var c.stk fuel
  rw [hout] at hreset
  refine ⟨(t + 1) + resetTime M c.stk, ?_, (run_add M hstart _).trans hreset⟩
  have hcost := resetTime_le M c.stk (input.length + bound * M.pushBound) hlen
  unfold roundBound
  omega

/-- Budgeted iteration on a displayed sequence of actual component outputs.
The uniform intermediate length bound is essential: arbitrary iteration of
a polynomial-time function need not have polynomial output size. -/
theorem iteration_run (states : ℕ → List Bool) (fuel : List Bool) (L T : ℕ)
    (hstep : ∀ j < fuel.length, M.OutputsWithin (states j) (states (j + 1)) T)
    (hlen : ∀ j < fuel.length, (states j).length ≤ L) :
    ∃ t ≤ fuel.length * roundBound M L T + 1,
      run M t (ready M (states 0) fuel) = finished M (states fuel.length) := by
  induction fuel generalizing states with
  | nil =>
      refine ⟨1, by simp, ?_⟩
      simpa only [List.length_nil] using run_succ M (fuel_nil M (states 0)) 0
  | cons b fuel ih =>
      obtain ⟨t, ht, hr⟩ := round_run M b fuel (hstep 0 (by simp))
      obtain ⟨u, hu, hur⟩ := ih (fun j => states (j + 1))
        (fun j hj => hstep (j + 1) (by simp only [List.length_cons]; omega))
        (fun j hj => hlen (j + 1) (by simp only [List.length_cons]; omega))
      refine ⟨t + u, ?_, (run_add M hr u).trans hur⟩
      have hs := hlen 0 (by simp)
      have hb : roundBound M (states 0).length T ≤ roundBound M L T := by
        unfold roundBound
        gcongr
      simp only [List.length_cons]
      nlinarith

theorem iteration_output (states : ℕ → List Bool) (fuel : List Bool) (L T : ℕ)
    (hstep : ∀ j < fuel.length, M.OutputsWithin (states j) (states (j + 1)) T)
    (hlen : ∀ j < fuel.length, (states j).length ≤ L) :
    ∃ t ≤ fuel.length * roundBound M L T + 1,
      (run M t (ready M (states 0) fuel)).l = none ∧
      (run M t (ready M (states 0) fuel)).stk (.inl M.input) = states fuel.length := by
  obtain ⟨t, ht, hr⟩ := iteration_run M states fuel L T hstep hlen
  refine ⟨t, ht, ?_, ?_⟩ <;> rw [hr]
  · rfl
  · simp [finished, Machine.init]

end EthInapproximability.CurrentPaper.BitMachineIteration
