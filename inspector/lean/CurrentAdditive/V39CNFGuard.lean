import EthInapproximability.CurrentPaper.BitMachineSubroutine

/-! A concrete finite copy/test wrapper. It preserves the entire original
word if the called machine's output begins with true, and returns [false]
otherwise. The only unbounded data are Boolean stacks. -/
namespace CurrentAdditive.V39CNFGuard

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

open EthInapproximability.CurrentPaper
open Turing TM2.Stmt BitMachineEncoding BitMachineComposition

variable (M : BitMachine.Machine)
abbrev Stack := Fin M.stackCount ⊕ Fin 2
inductive Outer where | scan | restore | gate | reject
  deriving DecidableEq, Fintype
abbrev Label := Fin M.labelCount ⊕ Outer
abbrev Control := Fin M.controlCount × Option Bool

def setLast (v : Control M) (b : Option Bool) : Control M := (v.1, b)
def program : Label M → TM2.Stmt (fun _ : Stack M => Bool) (Label M) (Control M)
  | .inl l => liftStmt (some Outer.gate) (M.program l)
  | .inr .scan => pop (.inr 0) (setLast M)
      (branch (fun v => v.2.isSome)
        (push (.inr 1) (fun v => v.2.getD false) (goto (fun _ => .inr Outer.scan)))
        (goto (fun _ => .inr Outer.restore)))
  | .inr .restore => pop (.inr 1) (setLast M)
      (branch (fun v => v.2.isSome)
        (push (.inr 0) (fun v => v.2.getD false)
          (push (.inl M.input) (fun v => v.2.getD false) (goto (fun _ => .inr Outer.restore))))
        (load (fun _ => (M.initial, none)) (goto (fun _ => .inl M.start))))
  | .inr .gate => peek (.inl M.output) (setLast M)
      (branch (fun v => v.2.getD false) halt (goto (fun _ => .inr Outer.reject)))
  | .inr .reject => pop (.inr 0) (setLast M)
      (branch (fun v => v.2.isSome) (goto (fun _ => .inr Outer.reject))
        (push (.inr 0) (fun _ => false) halt))

noncomputable def machine : BitMachine.Machine :=
  ofFinite (.inr 0 : Stack M) (.inr 0) (.inr Outer.scan) (M.initial, none) (program M)

def contents (S : Fin M.stackCount → List Bool) (source saved : List Bool) :
    Stack M → List Bool := Sum.elim S (fun j => if j = 0 then source else saved)
def cfg (l : Option (Label M)) (v : Control M)
    (S : Fin M.stackCount → List Bool) (source saved : List Bool) :
    TM2.Cfg (fun _ : Stack M => Bool) (Label M) (Control M) :=
  ⟨l, v, contents M S source saved⟩
def run (t : ℕ) (c : TM2.Cfg (fun _ : Stack M => Bool) (Label M) (Control M)) :=
  ((advance (program M))^[t]) c

theorem scan_cons (v : Control M) (S : Fin M.stackCount → List Bool)
    (b : Bool) (source saved : List Bool) :
    advance (program M) (cfg M (some (.inr Outer.scan)) v S (b :: source) saved) =
      cfg M (some (.inr Outer.scan)) (setLast M v (some b)) S source (b :: saved) := by
  simp only [advance, cfg, contents, program, TM2.step, TM2.stepAux, setLast,
    Option.getD_some, Sum.elim_inr, Sum.elim_inl, ite_true, ite_false,
    List.head?_cons, List.tail_cons, List.head?_nil, List.tail_nil,
    Option.isSome_some, Option.isSome_none, Option.getD_some, Bool.cond_true,
    Bool.cond_false, show (1 : Fin 2) ≠ 0 by decide, if_neg]
  congr 1
  funext k
  cases k with
  | inl k => rfl
  | inr k => fin_cases k <;> rfl

theorem scan_nil (v : Control M) (S : Fin M.stackCount → List Bool) (saved : List Bool) :
    advance (program M) (cfg M (some (.inr Outer.scan)) v S [] saved) =
      cfg M (some (.inr Outer.restore)) (setLast M v none) S [] saved := by
  simp only [advance, cfg, contents, program, TM2.step, TM2.stepAux, setLast,
    Option.getD_some, Sum.elim_inr, Sum.elim_inl, ite_true, ite_false,
    List.head?_cons, List.tail_cons, List.head?_nil, List.tail_nil,
    Option.isSome_some, Option.isSome_none, Option.getD_some, Bool.cond_true,
    Bool.cond_false, show (1 : Fin 2) ≠ 0 by decide, if_neg]
  congr 1
  funext k
  cases k with
  | inl k => rfl
  | inr k => fin_cases k <;> rfl

theorem scan_correct (v : Control M) (S : Fin M.stackCount → List Bool)
    (source saved : List Bool) :
    run M (source.length + 1) (cfg M (some (.inr Outer.scan)) v S source saved) =
      cfg M (some (.inr Outer.restore)) (setLast M v none) S [] (source.reverse ++ saved) := by
  induction source generalizing v saved with
  | nil => simpa [run] using scan_nil M v S saved
  | cons b source ih =>
    rw [List.length_cons, run, Function.iterate_succ_apply, scan_cons]
    change run M (source.length + 1) _ = _
    rw [ih]
    simp [List.reverse_cons, List.append_assoc, setLast]

theorem restore_cons (v : Control M) (S : Fin M.stackCount → List Bool)
    (b : Bool) (source saved : List Bool) :
    advance (program M) (cfg M (some (.inr Outer.restore)) v S source (b :: saved)) =
      cfg M (some (.inr Outer.restore)) (setLast M v (some b))
        (Function.update S M.input (b :: S M.input)) (b :: source) saved := by
  simp only [advance, cfg, contents, program, TM2.step, TM2.stepAux, setLast,
    Option.getD_some, Sum.elim_inr, Sum.elim_inl, ite_true, ite_false,
    List.head?_cons, List.tail_cons, List.head?_nil, List.tail_nil,
    Option.isSome_some, Option.isSome_none, Option.getD_some, Bool.cond_true,
    Bool.cond_false, show (1 : Fin 2) ≠ 0 by decide, if_neg]
  congr 1
  funext k
  cases k with
  | inl k =>
    simp only [Function.update_apply, Sum.inl_ne_inr, Sum.inr_ne_inl,
      Sum.inl.injEq, ↓reduceIte, Sum.elim_inl]
  | inr k => fin_cases k <;> rfl

theorem restore_nil (v : Control M) (S : Fin M.stackCount → List Bool) (source : List Bool) :
    advance (program M) (cfg M (some (.inr Outer.restore)) v S source []) =
      cfg M (some (.inl M.start)) (M.initial, none) S source [] := by
  simp only [advance, cfg, contents, program, TM2.step, TM2.stepAux, setLast,
    Option.getD_some, Sum.elim_inr, Sum.elim_inl, ite_true, ite_false,
    List.head?_cons, List.tail_cons, List.head?_nil, List.tail_nil,
    Option.isSome_some, Option.isSome_none, Option.getD_some, Bool.cond_true,
    Bool.cond_false, show (1 : Fin 2) ≠ 0 by decide, if_neg]
  congr 1
  funext k
  cases k with
  | inl k => rfl
  | inr k => fin_cases k <;> rfl

theorem restore_correct (v : Control M) (S : Fin M.stackCount → List Bool)
    (source saved : List Bool) :
    run M (saved.length + 1) (cfg M (some (.inr Outer.restore)) v S source saved) =
      cfg M (some (.inl M.start)) (M.initial, none)
        (Function.update S M.input (saved.reverse ++ S M.input))
        (saved.reverse ++ source) [] := by
  induction saved generalizing v S source with
  | nil =>
    rw [run, List.length_nil, Nat.zero_add, Function.iterate_one, restore_nil]
    simp
  | cons b saved ih =>
    rw [List.length_cons, run, Function.iterate_succ_apply, restore_cons]
    change run M (saved.length + 1) _ = _
    rw [ih]
    simp [List.reverse_cons, List.append_assoc]

theorem initial_copy (code : List Bool) :
    run M (2 * code.length + 2)
      (rawInit (.inr 0 : Stack M) (.inr Outer.scan) (M.initial, none) code) =
      liftCfg (some Outer.gate) none (fun j : Fin 2 => if j = 0 then code else [])
        (M.init code) := by
  have hi : rawInit (.inr 0 : Stack M) (.inr Outer.scan) (M.initial, none) code =
      cfg M (some (.inr Outer.scan)) (M.initial, none) (fun _ => []) code [] := by
    unfold rawInit cfg contents
    congr 1
    funext k
    cases k with
    | inl k => rfl
    | inr k => fin_cases k <;> rfl
  rw [hi, show 2 * code.length + 2 = (code.length + 1) + (code.length + 1) by omega,
    run, Function.iterate_add_apply]
  change run M (code.length + 1) (run M (code.length + 1) _) = _
  rw [scan_correct]
  simp only [List.append_nil]
  rw [show code.length + 1 = code.reverse.length + 1 by simp, restore_correct]
  simp only [List.reverse_reverse, List.append_nil]
  unfold cfg contents liftCfg BitMachine.Machine.init
  congr 1
  funext k
  cases k with
  | inl k => simp only [Sum.elim_inl, Function.update_apply]
  | inr k => fin_cases k <;> rfl

theorem reject_correct (v : Control M) (S : Fin M.stackCount → List Bool)
    (source saved : List Bool) :
    ∃ w : Control M,
      run M (source.length + 1) (cfg M (some (.inr Outer.reject)) v S source saved) =
        cfg M none w S [false] saved := by
  induction source generalizing v with
  | nil =>
    refine ⟨setLast M v none, ?_⟩
    simp only [run, List.length_nil, Nat.zero_add, Function.iterate_one,
      advance, cfg, contents, program, TM2.step, TM2.stepAux, setLast,
      Option.getD_some, Sum.elim_inr, ite_true, List.head?_nil,
      List.tail_nil, Option.isSome_none, Bool.cond_false]
    congr 1
    funext k
    cases k with
    | inl k => rfl
    | inr k => fin_cases k <;> rfl
  | cons b source ih =>
    obtain ⟨w, hw⟩ := ih (setLast M v (some b))
    refine ⟨w, ?_⟩
    rw [List.length_cons, run, Function.iterate_succ_apply]
    convert hw using 1
    congr 1
    simp only [advance, cfg, contents, program, TM2.step, TM2.stepAux, setLast,
    Option.getD_some, Sum.elim_inr, Sum.elim_inl, ite_true, ite_false,
    List.head?_cons, List.tail_cons, List.head?_nil, List.tail_nil,
    Option.isSome_some, Option.isSome_none, Option.getD_some, Bool.cond_true,
    Bool.cond_false, show (1 : Fin 2) ≠ 0 by decide, if_neg]
    congr 1
    funext k
    cases k with
    | inl k => rfl
    | inr k => fin_cases k <;> rfl

def result (test : List Bool → List Bool) (code : List Bool) : List Bool :=
  if (test code).headD false then code else [false]

theorem outputs (test : List Bool → List Bool) (code : List Bool) (time : ℕ)
    (h : M.OutputsWithin code (test code) time) :
    (machine M).OutputsWithin code (result test code) (time + 3 * code.length + 4) := by
  have hm := BitMachine.outputsWithin_at_bound M h
  let c := M.run time (M.init code)
  obtain ⟨t, ht, hr⟩ := BitMachineSubroutine.lift_outputs M.program (program M)
    (some Outer.gate) (fun _ => rfl) none
    (fun j : Fin 2 => if j = 0 then code else []) (M.init code) time hm.1
  have hp : run M (2 * code.length + 2 + t)
      (rawInit (.inr 0 : Stack M) (.inr Outer.scan) (M.initial, none) code) =
      cfg M (some (.inr Outer.gate)) (c.var, none) c.stk code [] := by
    rw [run, show 2 * code.length + 2 + t = t + (2 * code.length + 2) by omega,
      Function.iterate_add_apply]
    change ((advance (program M))^[t]) (run M (2 * code.length + 2) _) = _
    rw [initial_copy, hr]
    change liftCfg (some Outer.gate) none _ c = _
    simp only [liftCfg, show c.l = none from hm.1, Option.map_some]
    rfl
  have hout : c.stk M.output = test code := hm.2
  have hg : advance (program M) (cfg M (some (.inr Outer.gate)) (c.var, none) c.stk code []) =
      cfg M (if (test code).headD false then none else some (.inr Outer.reject))
        (c.var, (test code).head?) c.stk code [] := by
    simp [advance, cfg, contents, program, TM2.step, TM2.stepAux, setLast, hout,
      List.headD]
    cases hh : test code with
    | nil => rfl
    | cons b bs => cases b <;> rfl
  cases hb : (test code).headD false with
  | true =>
    apply outputsWithin_of_raw_run (.inr 0 : Stack M) (.inr 0) (.inr Outer.scan)
      (M.initial, none) (program M) code (result test code)
      (2 * code.length + 2 + t + 1) _ (by omega)
    · change (run M (2 * code.length + 2 + t + 1) _).l = none
      rw [run, Function.iterate_succ_apply']
      change (advance (program M) (run M (2 * code.length + 2 + t) _)).l = none
      rw [hp, hg]
      simp only [hb, ↓reduceIte, cfg]
    · change (run M (2 * code.length + 2 + t + 1) _).stk (.inr 0) = _
      rw [run, Function.iterate_succ_apply']
      change (advance (program M) (run M (2 * code.length + 2 + t) _)).stk (.inr 0) = _
      rw [hp, hg]
      simp only [hb, ↓reduceIte, cfg, contents, Sum.elim_inr, ite_true, result]
  | false =>
    obtain ⟨w, hw⟩ := reject_correct M (c.var, (test code).head?) c.stk code []
    have hf : run M (2 * code.length + 2 + t + 1 + (code.length + 1))
        (rawInit (.inr 0 : Stack M) (.inr Outer.scan) (M.initial, none) code) =
        cfg M none w c.stk [false] [] := by
      rw [run, show 2 * code.length + 2 + t + 1 + (code.length + 1) =
        (code.length + 1) + (2 * code.length + 2 + t + 1) by omega,
        Function.iterate_add_apply]
      change run M (code.length + 1) (run M (2 * code.length + 2 + t + 1) _) = _
      conv_lhs => arg 3; rw [run, Function.iterate_succ_apply']
      change run M (code.length + 1) (advance (program M)
        (run M (2 * code.length + 2 + t) _)) = _
      rw [hp, hg]
      simpa only [hb, Bool.cond_false] using hw
    apply outputsWithin_of_raw_run (.inr 0 : Stack M) (.inr 0) (.inr Outer.scan)
      (M.initial, none) (program M) code (result test code)
      (2 * code.length + 2 + t + 1 + (code.length + 1)) _ (by omega)
    · exact congrArg (fun q => q.l) hf
    · simpa only [result, hb, Bool.false_eq_true, ↓reduceIte] using
        congrArg (fun q => q.stk (.inr 0)) hf

theorem polytime (test : List Bool → List Bool) (h : BitMachine.Polytime test) :
    BitMachine.Polytime (result test) := by
  obtain ⟨M, c, d, h⟩ := h
  refine ⟨machine M, c + 4, d + 1, ?_⟩
  intro code
  apply BitMachine.outputsWithin_mono _ (outputs M test code _ (h code))
  have hpow : (code.length + 1) ^ d ≤ (code.length + 1) ^ (d + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hlin : code.length + 1 ≤ (code.length + 1) ^ (d + 1) := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ code.length + 1)
      (show 1 ≤ d + 1 by omega)
  nlinarith

end CurrentAdditive.V39CNFGuard
