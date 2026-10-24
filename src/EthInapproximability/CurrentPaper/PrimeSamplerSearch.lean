import EthInapproximability.CurrentPaper.BitMachineIteration
import EthInapproximability.CurrentPaper.PrimeSamplerTrial

/-!
# A bounded physical search using a unary primality tester

Source: frozen v8 `B-effectivity-details.tex`, explicit balanced-family
prime search. Every candidate and the remaining search budget are Boolean
stacks. A fixed tester is called on a freshly copied candidate and all its
work stacks are cleared before the next call. Runtime assumptions here are
the explicit local tester interface; the prime-sampler endpoint instantiates
that interface with its proved trial-division program.
-/

namespace EthInapproximability.CurrentPaper.PrimeSamplerSearch

open Turing TM2.Stmt BitMachine BitMachineEncoding BitMachineComposition BitMachineSubroutine
open scoped BigOperators

variable (M : Machine)

inductive Admin (k : ℕ) where
  | initialize | restoreInitial | loop | copy | restore | tested
  | clear (i : Fin (k+1)) | increment | emit
  deriving DecidableEq, Fintype

abbrev Stack := Fin M.stackCount ⊕ Fin 4
abbrev Label := Fin M.labelCount ⊕ Admin M.stackCount
abbrev Control := Fin M.controlCount × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack M => Bool) (Label M) (Control M)

def program : Label M → TM2.Stmt (fun _ : Stack M => Bool) (Label M) (Control M)
  | .inl l => liftStmt (some (.tested : Admin M.stackCount)) (M.program l)
  | .inr .initialize => pop (.inr 0) (fun v b => (v.1,b))
      (branch (fun v => v.2.isSome)
        (push (.inr 1) (fun _ => true) (push (.inr 2) (fun _ => true)
          (goto (fun _ => .inr .initialize))))
        (load (fun _ => (M.initial,none)) (goto (fun _ => .inr .restoreInitial))))
  | .inr .restoreInitial => pop (.inr 1) (fun v b => (v.1,b))
      (branch (fun v => v.2.isSome)
        (push (.inr 0) (fun _ => true) (goto (fun _ => .inr .restoreInitial)))
        (load (fun _ => (M.initial,none)) (goto (fun _ => .inr .loop))))
  | .inr .loop => pop (.inr 2) (fun v b => (v.1,b))
      (branch (fun v => v.2.isSome)
        (load (fun _ => (M.initial,none)) (goto (fun _ => .inr .copy))) halt)
  | .inr .copy => pop (.inr 0) (fun v b => (v.1,b))
      (branch (fun v => v.2.isSome)
        (push (.inl M.input) (fun _ => true) (push (.inr 1) (fun _ => true)
          (goto (fun _ => .inr .copy))))
        (load (fun _ => (M.initial,none)) (goto (fun _ => .inr .restore))))
  | .inr .restore => pop (.inr 1) (fun v b => (v.1,b))
      (branch (fun v => v.2.isSome)
        (push (.inr 0) (fun _ => true) (goto (fun _ => .inr .restore)))
        (load (fun _ => (M.initial,none)) (goto (fun _ => .inl M.start))))
  | .inr .tested => pop (.inl M.output) (fun v b => (v.1,b))
      (branch (fun v => v.2.getD false)
        (load (fun v => (v.1,none)) (goto (fun _ => .inr .emit)))
        (load (fun v => (v.1,none)) (goto (fun _ => .inr (.clear 0)))))
  | .inr (.clear i) =>
      if h : i.val < M.stackCount then
        BitMachineClearBank.clearStep (.inl ⟨i.val,h⟩) (.inr (.clear i))
          (.inr (.clear ⟨i.val+1,by omega⟩))
      else BitMachineClearBank.finishStep (fun _ => M.initial) (.inr .increment)
  | .inr .increment => push (.inr 0) (fun _ => true)
      (load (fun _ => (M.initial,none)) (goto (fun _ => .inr .loop)))
  | .inr .emit => pop (.inr 0) (fun v b => (v.1,b))
      (branch (fun v => v.2.isSome)
        (push (.inr 3) (fun _ => true) (goto (fun _ => .inr .emit))) halt)

def foreign (candidate saved fuel output : List Bool) : Fin 4 → List Bool :=
  fun j => if j=0 then candidate else if j=1 then saved else if j=2 then fuel else output

@[simp] theorem foreign_zero (c s f o : List Bool) : foreign c s f o 0 = c := rfl
@[simp] theorem foreign_one (c s f o : List Bool) : foreign c s f o 1 = s := rfl
@[simp] theorem foreign_two (c s f o : List Bool) : foreign c s f o 2 = f := rfl
@[simp] theorem foreign_three (c s f o : List Bool) : foreign c s f o 3 = o := rfl

def cfg (l : Option (Label M)) (v : Control M) (S : Fin M.stackCount → List Bool)
    (candidate saved fuel output : List Bool) : Config M :=
  ⟨l,v,Sum.elim S (foreign candidate saved fuel output)⟩

def adminCfg (l : Admin M.stackCount) (v : Control M) (S : Fin M.stackCount → List Bool)
    (candidate saved fuel output : List Bool) : Config M :=
  cfg M (some (.inr l)) v S candidate saved fuel output

def ready (n fuel : ℕ) : Config M :=
  adminCfg M .loop (M.initial,none) (fun _ => []) (List.replicate n true) []
    (List.replicate fuel true) []

def run (t : ℕ) (c : Config M) : Config M := ((advance (program M))^[t]) c

theorem run_add {c d : Config M} {t : ℕ} (h : run M t c = d) (u : ℕ) :
    run M (t+u) c = run M u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

theorem run_step {c d : Config M} (h : advance (program M) c = d) (t : ℕ) :
    run M (t+1) c = run M t d := by
  simp only [run, Function.iterate_succ_apply, h]

theorem clear_run (v : Fin M.controlCount) (S : Fin M.stackCount → List Bool)
    (candidate saved fuel output : List Bool) :
    run M ((∑ i, (S i).length)+M.stackCount+1)
      (adminCfg M (.clear 0) (v,none) S candidate saved fuel output) =
      adminCfg M .increment (M.initial,none) (fun _ => []) candidate saved fuel output := by
  have hc := BitMachineClearBank.clear_bank_run (program M) (fun _ => M.initial)
    (.inr .increment) M.stackCount (fun i => (Sum.inl i : Stack M)) Sum.inl_injective
    (fun i => (.inr (.clear i) : Label M))
    (fun i => by simp only [program, Fin.val_castSucc, i.isLt, ↓reduceDIte]; rfl)
    (by simp only [program, Fin.val_last, lt_self_iff_false, ↓reduceDIte])
    v (Sum.elim S (foreign candidate saved fuel output))
  have he : BitMachineClearBank.cleared (fun i => (Sum.inl i : Stack M))
      (Sum.elim S (foreign candidate saved fuel output)) =
      Sum.elim (fun _ => []) (foreign candidate saved fuel output) := by
    funext k
    cases k <;> simp [BitMachineClearBank.cleared]
  simpa only [run, adminCfg, cfg, Sum.elim_inl, he] using hc

theorem tester_run {n : ℕ} {result : Bool} {bound : ℕ} (fuel : List Bool)
    (h : M.OutputsWithin (List.replicate n true) [result] bound) :
    ∃ (t : ℕ) (c : M.Config), t ≤ bound ∧ c.l=none ∧ c.stk M.output=[result] ∧
      run M t (liftCfg (some (.tested : Admin M.stackCount)) none
        (foreign (List.replicate n true) [] fuel []) (M.init (List.replicate n true))) =
        adminCfg M .tested (c.var,none) c.stk (List.replicate n true) [] fuel [] ∧
      ∀ k, (c.stk k).length ≤ n+bound*M.pushBound := by
  obtain ⟨t, ht, hh, ho, hf⟩ := BitMachineCompositionArithmetic.first_halt M h
  refine ⟨t,M.run t (M.init (List.replicate n true)),ht,hh,ho,?_,?_⟩
  · have hr := lift_run_until M.program (program M) (some (.tested : Admin M.stackCount))
      (fun _ => rfl) none (foreign (List.replicate n true) [] fuel [])
      (M.init (List.replicate n true)) t hf
    change run M t _ = liftCfg _ _ _ (M.run t (M.init (List.replicate n true))) at hr
    simpa only [liftCfg, hh, Option.map_some, adminCfg, cfg] using hr
  · intro k
    have hk := BitMachine.run_length M (M.init (List.replicate n true)) k t
    have hi : ((M.init (List.replicate n true)).stk k).length ≤ n := by
      simp only [Machine.init]
      split_ifs <;> simp
    nlinarith

theorem emit_run (n m : ℕ) (v : Control M) (S : Fin M.stackCount → List Bool)
    (saved fuel : List Bool) :
    run M (n+1) (adminCfg M .emit v S (List.replicate n true) saved fuel
      (List.replicate m true)) =
      cfg M none (v.1,none) S [] saved fuel (List.replicate (m+n) true) := by
  induction n generalizing m v with
  | zero =>
      simp only [Nat.zero_add, Nat.add_zero, List.replicate_zero, run, Function.iterate_one]
      simp only [advance, adminCfg, cfg, TM2.step, program, TM2.stepAux,
        Sum.elim_inr, foreign, ↓reduceIte, List.head?_nil, List.tail_nil,
        Option.isSome_none, cond_false, Option.getD_some]
      congr 1
      funext j
      cases j with
      | inl j => rfl
      | inr j => fin_cases j <;> rfl
  | succ n ih =>
      have hs : advance (program M)
          (adminCfg M .emit v S (List.replicate (n+1) true) saved fuel (List.replicate m true)) =
          adminCfg M .emit (v.1,some true) S (List.replicate n true) saved fuel
            (List.replicate (m+1) true) := by
        simp only [List.replicate_succ, advance, adminCfg, cfg, TM2.step, program, TM2.stepAux,
          Sum.elim_inr, foreign, ↓reduceIte, List.head?_cons, List.tail_cons,
          Option.isSome_some, cond_true, Option.getD_some]
        congr 1
        funext j
        cases j with
        | inl j => rfl
        | inr j => fin_cases j <;> rfl
      rw [run_step M hs, ih]
      congr 2
      omega

def inputBank (n : ℕ) : Fin M.stackCount → List Bool := (M.init (List.replicate n true)).stk

theorem copy_run (n a b : ℕ) (v : Control M) (fuel : List Bool) :
    run M (n+1) (adminCfg M .copy v (inputBank M a) (List.replicate n true)
      (List.replicate b true) fuel []) =
      adminCfg M .restore (M.initial,none) (inputBank M (a+n)) []
        (List.replicate (b+n) true) fuel [] := by
  induction n generalizing a b v with
  | zero =>
      simp only [Nat.zero_add, Nat.add_zero, List.replicate_zero, run, Function.iterate_one]
      simp only [advance, adminCfg, cfg, TM2.step, program, TM2.stepAux,
        Sum.elim_inr, foreign, ↓reduceIte, List.head?_nil, List.tail_nil,
        Option.isSome_none, cond_false, Option.getD_some]
      congr 1
      funext j
      cases j with
      | inl j => rfl
      | inr j => fin_cases j <;> rfl
  | succ n ih =>
      have hs : advance (program M)
          (adminCfg M .copy v (inputBank M a) (List.replicate (n+1) true)
            (List.replicate b true) fuel []) =
          adminCfg M .copy (v.1,some true) (inputBank M (a+1)) (List.replicate n true)
            (List.replicate (b+1) true) fuel [] := by
        simp only [List.replicate_succ, advance, adminCfg, cfg, TM2.step, program, TM2.stepAux,
          Sum.elim_inr, foreign, ↓reduceIte, List.head?_cons, List.tail_cons,
          Option.isSome_some, cond_true, Option.getD_some]
        congr 1
        funext j
        cases j with
        | inl j =>
            by_cases hj : j=M.input
            · subst j
              simp only [Function.update_apply, Sum.inl_ne_inr, Sum.inl.injEq,
                Sum.elim_inl, inputBank, Machine.init, ite_self, ↓reduceIte, List.replicate_succ]
            · simp only [Function.update_apply, Sum.inl_ne_inr, Sum.inl.injEq,
                Sum.elim_inl, inputBank, Machine.init, hj, ↓reduceIte, List.replicate_succ]
        | inr j => fin_cases j <;> rfl
      rw [run_step M hs, ih]
      congr 2 <;> omega

theorem restore_run (n a : ℕ) (v : Control M) (S : Fin M.stackCount → List Bool)
    (fuel : List Bool) :
    run M (n+1) (adminCfg M .restore v S (List.replicate a true)
      (List.replicate n true) fuel []) =
      cfg M (some (.inl M.start)) (M.initial,none) S (List.replicate (a+n) true) [] fuel [] := by
  induction n generalizing a v with
  | zero =>
      simp only [Nat.zero_add, Nat.add_zero, List.replicate_zero, run, Function.iterate_one]
      simp only [advance, adminCfg, cfg, TM2.step, program, TM2.stepAux,
        Sum.elim_inr, foreign_one, List.head?_nil, List.tail_nil,
        Option.isSome_none, cond_false, Option.getD_some]
      congr 1
      funext j
      cases j with
      | inl j => rfl
      | inr j => fin_cases j <;> rfl
  | succ n ih =>
      have hs : advance (program M)
          (adminCfg M .restore v S (List.replicate a true) (List.replicate (n+1) true) fuel []) =
          adminCfg M .restore (v.1,some true) S (List.replicate (a+1) true)
            (List.replicate n true) fuel [] := by
        simp only [List.replicate_succ, advance, adminCfg, cfg, TM2.step, program, TM2.stepAux,
          Sum.elim_inr, foreign_one, List.head?_cons, List.tail_cons,
          Option.isSome_some, cond_true, Option.getD_some]
        congr 1
        funext j
        cases j with
        | inl j => rfl
        | inr j => fin_cases j <;> rfl
      rw [run_step M hs, ih]
      congr 2
      omega

theorem prepare_run (n : ℕ) (fuel : List Bool) :
    run M (2*n+2) (adminCfg M .copy (M.initial,none) (fun _ => [])
      (List.replicate n true) [] fuel []) =
      liftCfg (some (.tested : Admin M.stackCount)) none
        (foreign (List.replicate n true) [] fuel []) (M.init (List.replicate n true)) := by
  have hl : inputBank M 0 = (fun _ => []) := by simp [inputBank, Machine.init]
  have hc := copy_run M n 0 0 (M.initial,none) fuel
  simp only [Nat.zero_add, hl, List.replicate_zero] at hc
  have hr := restore_run M n 0 (M.initial,none) (inputBank M n) fuel
  simp only [Nat.zero_add, List.replicate_zero] at hr
  rw [show 2*n+2=(n+1)+(n+1) by omega, run_add M hc, hr]
  simp [cfg, inputBank, liftCfg, Machine.init]

theorem loop_step (n fuel : ℕ) :
    advance (program M) (ready M n (fuel+1)) =
      adminCfg M .copy (M.initial,none) (fun _ => []) (List.replicate n true) []
        (List.replicate fuel true) [] := by
  simp only [ready, List.replicate_succ, advance, adminCfg, cfg, TM2.step, program,
    TM2.stepAux, Sum.elim_inr, foreign_two, List.head?_cons, List.tail_cons,
    Option.isSome_some, cond_true, Option.getD_some]
  congr 1
  funext j
  cases j with
  | inl j => rfl
  | inr j => fin_cases j <;> rfl

theorem tested_step (v : Fin M.controlCount) (S : Fin M.stackCount → List Bool)
    (n : ℕ) (fuel : List Bool) (result : Bool) (hS : S M.output=[result]) :
    advance (program M)
      (adminCfg M .tested (v,none) S (List.replicate n true) [] fuel []) =
      adminCfg M (if result then .emit else .clear 0) (v,none)
        (Function.update S M.output []) (List.replicate n true) [] fuel [] := by
  cases result <;>
    simp only [advance, adminCfg, cfg, TM2.step, program, TM2.stepAux, Sum.elim_inl, hS,
      List.head?_cons, List.tail_cons, Option.getD_some, cond_false, cond_true,
      Bool.false_eq_true, Bool.true_eq, ↓reduceIte] <;>
    congr 1 <;> funext j <;> cases j with
    | inl j =>
        by_cases hj : j=M.output
        · subst j; simp
        · simp [hj]
    | inr j => rfl

theorem increment_step (n fuel : ℕ) :
    advance (program M)
      (adminCfg M .increment (M.initial,none) (fun _ => [])
        (List.replicate n true) [] (List.replicate fuel true) []) =
      ready M (n+1) fuel := by
  simp only [ready, List.replicate_succ, advance, adminCfg, cfg, TM2.step, program,
    TM2.stepAux, Sum.elim_inr, foreign, ↓reduceIte, Option.getD_some]
  congr 1
  funext j
  cases j with
  | inl j => rfl
  | inr j => fin_cases j <;> rfl

def stepBound (N B : ℕ) : ℕ :=
  2*N+B+M.stackCount*(N+B*M.pushBound)+M.stackCount+6

/-- A bounded search with genuine tester calls, input copying, bank cleanup,
candidate incrementing, and output writing. The tester premise is local:
it is discharged by the independent unary trial-division implementation. -/
theorem scan_run (n fuel N B : ℕ) (hcap : n+fuel ≤ N+1)
    (htest : ∀ a ≤ N, M.OutputsWithin (List.replicate a true)
      [PrimeSamplerTrial.trialPrime a] B) :
    ∃ t ≤ fuel*stepBound M N B+N+1,
      let c := run M t (ready M n fuel)
      c.l=none ∧ c.stk (.inr 3)=
        List.replicate ((PrimeSamplerTrial.scan n fuel).getD 0) true := by
  induction fuel generalizing n with
  | zero =>
      refine ⟨1, by omega, ?_⟩
      dsimp only
      have hs : advance (program M) (ready M n 0) =
          cfg M none (M.initial,none) (fun _ => []) (List.replicate n true) [] [] [] := by
        simp only [ready, List.replicate_zero, advance, adminCfg, cfg, TM2.step,
          program, TM2.stepAux, Sum.elim_inr, foreign_two, List.head?_nil,
          List.tail_nil, Option.isSome_none, cond_false, Option.getD_some]
        congr 1
        funext j
        cases j with
        | inl j => rfl
        | inr j => fin_cases j <;> rfl
      simp only [run, Function.iterate_one, hs, cfg, Sum.elim_inr, foreign_three,
        PrimeSamplerTrial.scan, Option.getD_none, List.replicate_zero, and_self]
  | succ fuel ih =>
      have hn : n ≤ N := by omega
      obtain ⟨tt,c,htt,hh,hout,hr,hsize⟩ := tester_run M (List.replicate fuel true) (htest n hn)
      have hp : run M (2*n+3+tt) (ready M n (fuel+1)) =
          adminCfg M .tested (c.var,none) c.stk (List.replicate n true) []
            (List.replicate fuel true) [] := by
        rw [show 2*n+3+tt=((2*n+2)+tt)+1 by omega, run_step M (loop_step M n fuel),
          run_add M (prepare_run M n (List.replicate fuel true)), hr]
      let S := Function.update c.stk M.output []
      have htested := tested_step M c.var c.stk n (List.replicate fuel true)
        (PrimeSamplerTrial.trialPrime n) hout
      change advance (program M) _ = adminCfg M _ _ S _ _ _ _ at htested
      by_cases hprime : PrimeSamplerTrial.trialPrime n = true
      · rw [hprime, if_pos rfl] at htested
        have he := emit_run M n 0 (c.var,none) S [] (List.replicate fuel true)
        simp only [List.replicate_zero, Nat.zero_add] at he
        refine ⟨(2*n+3+tt)+(1+(n+1)), ?_, ?_⟩
        · have hb : 2*N+B+6 ≤ stepBound M N B := by simp [stepBound]; omega
          have hmult : stepBound M N B ≤ (fuel+1)*stepBound M N B := by nlinarith
          nlinarith
        · dsimp only
          rw [run_add M hp]
          rw [show 1+(n+1)=(n+1)+1 by omega, run_step M htested, he]
          simp [cfg, foreign_three, PrimeSamplerTrial.scan, hprime]
      · have hfalse : PrimeSamplerTrial.trialPrime n = false := by
          cases h : PrimeSamplerTrial.trialPrime n <;> simp_all
        rw [hfalse, if_neg Bool.false_ne_true] at htested
        have hS : ∀ j, (S j).length ≤ N+B*M.pushBound := by
          intro j
          by_cases hj : j=M.output
          · simp [S, hj]
          · have hj' := hsize j
            simpa [S, hj] using hj'.trans (Nat.add_le_add_right hn _)
        have hsum : (∑ j, (S j).length) ≤ M.stackCount*(N+B*M.pushBound) := by
          calc
            (∑ j, (S j).length) ≤ ∑ _j : Fin M.stackCount, (N+B*M.pushBound) :=
              Finset.sum_le_sum (fun j _ => hS j)
            _ = _ := by simp
        let clearing := (∑ j, (S j).length)+M.stackCount+1
        have hc := clear_run M c.var S (List.replicate n true) [] (List.replicate fuel true) []
        have hround : run M ((2*n+3+tt)+(1+(clearing+1))) (ready M n (fuel+1)) =
            ready M (n+1) fuel := by
          rw [run_add M hp, show 1+(clearing+1)=(clearing+1)+1 by omega,
            run_step M htested]
          change run M (clearing+1) _ = _
          rw [run_add M hc]
          exact increment_step M n fuel
        have hroundBound : (2*n+3+tt)+(1+(clearing+1)) ≤ stepBound M N B := by
          dsimp [clearing, stepBound]
          omega
        obtain ⟨u,hu,hresult⟩ := ih (n+1) (by omega)
        refine ⟨((2*n+3+tt)+(1+(clearing+1)))+u, ?_, ?_⟩
        · nlinarith
        · dsimp only at hresult ⊢
          rw [run_add M hround]
          simpa only [PrimeSamplerTrial.scan, hfalse, Bool.false_eq_true, ↓reduceIte] using hresult

theorem initialize_run (input : List Bool) (a b : ℕ) (v : Control M) :
    run M (input.length+1) (adminCfg M .initialize v (fun _ => []) input
      (List.replicate a true) (List.replicate b true) []) =
      adminCfg M .restoreInitial (M.initial,none) (fun _ => []) []
        (List.replicate (a+input.length) true) (List.replicate (b+input.length) true) [] := by
  induction input generalizing a b v with
  | nil =>
      simp only [List.length_nil, Nat.zero_add, Nat.add_zero, run, Function.iterate_one]
      simp only [advance, adminCfg, cfg, TM2.step, program, TM2.stepAux, Sum.elim_inr,
        foreign_zero, List.head?_nil, List.tail_nil, Option.isSome_none, cond_false, Option.getD_some]
      congr 1
      funext j
      cases j with
      | inl j => rfl
      | inr j => fin_cases j <;> rfl
  | cons bit input ih =>
      have hs : advance (program M)
          (adminCfg M .initialize v (fun _ => []) (bit::input)
            (List.replicate a true) (List.replicate b true) []) =
          adminCfg M .initialize (v.1,some bit) (fun _ => []) input
            (List.replicate (a+1) true) (List.replicate (b+1) true) [] := by
        simp only [List.replicate_succ, advance, adminCfg, cfg, TM2.step, program, TM2.stepAux,
          Sum.elim_inr, foreign_zero, List.head?_cons, List.tail_cons,
          Option.isSome_some, cond_true, Option.getD_some]
        congr 1
        funext j
        cases j with
        | inl j => rfl
        | inr j => fin_cases j <;> rfl
      rw [List.length_cons, run_step M hs, ih]
      congr 2 <;> omega

theorem restore_initial_run (n a : ℕ) (v : Control M) (fuel : List Bool) :
    run M (n+1) (adminCfg M .restoreInitial v (fun _ => []) (List.replicate a true)
      (List.replicate n true) fuel []) =
      adminCfg M .loop (M.initial,none) (fun _ => []) (List.replicate (a+n) true) [] fuel [] := by
  induction n generalizing a v with
  | zero =>
      simp only [Nat.zero_add, Nat.add_zero, List.replicate_zero, run, Function.iterate_one]
      simp only [advance, adminCfg, cfg, TM2.step, program, TM2.stepAux,
        Sum.elim_inr, foreign_one, List.head?_nil, List.tail_nil,
        Option.isSome_none, cond_false, Option.getD_some]
      congr 1
      funext j
      cases j with
      | inl j => rfl
      | inr j => fin_cases j <;> rfl
  | succ n ih =>
      have hs : advance (program M)
          (adminCfg M .restoreInitial v (fun _ => []) (List.replicate a true)
            (List.replicate (n+1) true) fuel []) =
          adminCfg M .restoreInitial (v.1,some true) (fun _ => []) (List.replicate (a+1) true)
            (List.replicate n true) fuel [] := by
        simp only [List.replicate_succ, advance, adminCfg, cfg, TM2.step, program, TM2.stepAux,
          Sum.elim_inr, foreign_one, List.head?_cons, List.tail_cons,
          Option.isSome_some, cond_true, Option.getD_some]
        congr 1
        funext j
        cases j with
        | inl j => rfl
        | inr j => fin_cases j <;> rfl
      rw [run_step M hs, ih]
      congr 2
      omega

theorem initial_run (input : List Bool) :
    run M (2*input.length+2)
      (adminCfg M .initialize (M.initial,none) (fun _ => []) input [] [] []) =
      ready M input.length input.length := by
  have hi := initialize_run M input 0 0 (M.initial,none)
  simp only [Nat.zero_add, List.replicate_zero] at hi
  have hr := restore_initial_run M input.length 0 (M.initial,none)
    (List.replicate input.length true)
  simp only [Nat.zero_add, List.replicate_zero] at hr
  rw [show 2*input.length+2=(input.length+1)+(input.length+1) by omega, run_add M hi, hr]
  rfl

noncomputable def machine : Machine :=
  ofFinite (Sum.inr (0 : Fin 4) : Stack M) (.inr 3) (.inr .initialize)
    (M.initial,none) (program M)

theorem initial_cfg (input : List Bool) :
    rawInit (Sum.inr (0 : Fin 4) : Stack M) (Sum.inr .initialize : Label M)
      (M.initial,none) input =
      adminCfg M .initialize (M.initial,none) (fun _ => []) input [] [] [] := by
  simp only [rawInit, adminCfg, cfg]
  congr 1
  funext j
  cases j with
  | inl j => rfl
  | inr j => fin_cases j <;> rfl

theorem outputs (input : List Bool) (B : ℕ)
    (htest : ∀ a ≤ 2*input.length, M.OutputsWithin (List.replicate a true)
      [PrimeSamplerTrial.trialPrime a] B) :
    (machine M).OutputsWithin input
      (List.replicate (PrimeSamplerTrial.firstPrime input.length) true)
      ((2*input.length+2)+input.length*stepBound M (2*input.length) B+2*input.length+1) := by
  obtain ⟨t,ht,hh,ho⟩ := scan_run M input.length input.length (2*input.length) B (by omega) htest
  apply outputsWithin_of_raw_run (.inr 0) (.inr 3) (.inr .initialize)
    (M.initial,none) (program M) input _ ((2*input.length+2)+t) _ (by omega)
  · change (run M ((2*input.length+2)+t) _).l=none
    rw [initial_cfg, run_add M (initial_run M input)]
    exact hh
  · change (run M ((2*input.length+2)+t) _).stk (.inr 3)=_
    rw [initial_cfg, run_add M (initial_run M input)]
    exact ho

def coefficient (C : ℕ) : ℕ := 17+3*M.stackCount+C*(1+M.stackCount*M.pushBound)

theorem polynomial_bound (n C d : ℕ) :
    ((2*n+2)+n*stepBound M (2*n) (C*(2*n+1)^d)+2*n+1) ≤
      coefficient M C*2^(d+2)*(n+1)^(d+2) := by
  let z := 2*n+1
  let P := z^(d+2)
  have hz : 1 ≤ z := by dsimp [z]; omega
  have hn : n ≤ z := by dsimp [z]; omega
  have hP : 1 ≤ P := Nat.one_le_pow _ _ hz
  have hnP : n ≤ P := hn.trans (by
    simpa only [pow_one] using Nat.pow_le_pow_right hz (show 1 ≤ d+2 by omega))
  have hnn : n*n ≤ P := by
    calc
      n*n ≤ z*z := Nat.mul_self_le_mul_self hn
      _ = z^2 := by ring
      _ ≤ _ := Nat.pow_le_pow_right hz (by omega)
  have hnd : n*z^d ≤ P := by
    calc
      n*z^d ≤ z*z^d := Nat.mul_le_mul_right _ hn
      _ = z^(d+1) := by rw [pow_succ]; ring
      _ ≤ _ := Nat.pow_le_pow_right hz (by omega)
  have hmain : ((2*n+2)+n*stepBound M (2*n) (C*(2*n+1)^d)+2*n+1) ≤
      coefficient M C*P := by
    calc
      _ = (4+2*M.stackCount)*(n*n)+(M.stackCount+10)*n+
          C*(1+M.stackCount*M.pushBound)*(n*z^d)+3 := by
        dsimp [stepBound, z]
        ring
      _ ≤ (4+2*M.stackCount)*P+(M.stackCount+10)*P+
          C*(1+M.stackCount*M.pushBound)*P+3*P := by
        gcongr
        omega
      _ = coefficient M C*P := by dsimp [coefficient]; ring
  apply hmain.trans
  have hp : P ≤ (2*(n+1))^(d+2) := by
    apply Nat.pow_le_pow_left
    dsimp [z]
    omega
  calc
    coefficient M C*P ≤ coefficient M C*(2*(n+1))^(d+2) := Nat.mul_le_mul_left _ hp
    _ = _ := by rw [mul_pow]; ring

/-- A polynomial unary tester gives a polynomial bounded least-prime search.
All words are admitted: the input's length is the unary threshold. -/
theorem polytime (C d : ℕ)
    (htest : ∀ n, M.OutputsWithin (List.replicate n true)
      [PrimeSamplerTrial.trialPrime n] (C*(n+1)^d)) :
    BitMachine.Polytime (fun input => List.replicate (PrimeSamplerTrial.firstPrime input.length) true) := by
  refine ⟨machine M, coefficient M C*2^(d+2), d+2, ?_⟩
  intro input
  have h := outputs M input (C*(2*input.length+1)^d) (by
    intro n hn
    apply BitMachine.outputsWithin_mono M (htest n)
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    omega)
  exact BitMachine.outputsWithin_mono _ h (polynomial_bound M input.length C d)

end EthInapproximability.CurrentPaper.PrimeSamplerSearch
