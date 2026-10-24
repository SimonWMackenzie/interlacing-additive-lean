import EthInapproximability.CurrentPaper.BitMachineEncoding

/-! A fixed five-bank first-hit selector. Bank 0 contains one Boolean flag per
row, bank 1 is the unary lower threshold, bank 2 accumulates the unary row,
bank 3 is the found tag, and bank 4 retains the original Gauss state packet.
It halts after at most one pass over the flags on every input. -/

namespace CurrentAdditive.GaussFlagSearch

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

abbrev Stack := Fin 5

inductive Label where
  | skip | scan
  deriving DecidableEq, Fintype

abbrev Control := Option Bool × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .skip =>
      pop 1 (fun v b => (b, v.2))
        (branch (fun v => v.1.isSome)
          (pop 0 (fun v b => (v.1, b))
            (branch (fun v => v.2.isSome)
              (push 2 (fun _ => true)
                (load (fun _ => (none, none)) (goto (fun _ => .skip))))
              (push 3 (fun _ => false) halt)))
          (load (fun _ => (none, none)) (goto (fun _ => .scan))))
  | .scan =>
      pop 0 (fun v b => (v.1, b))
        (branch (fun v => v.2.isSome)
          (branch (fun v => v.2.getD false)
            (push 3 (fun _ => true) halt)
            (push 2 (fun _ => true)
              (load (fun _ => (none, none)) (goto (fun _ => .scan)))))
          (push 3 (fun _ => false) halt))

def bank (flags threshold row tag saved : List Bool) : Stack → List Bool :=
  ![flags, threshold, row, tag, saved]

def cfg (l : Option Label) (v : Control)
    (flags threshold row tag saved : List Bool) : Config :=
  ⟨l, v, bank flags threshold row tag saved⟩

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

theorem run_succ {c c' : Config} (h : advance program c = c') (t : Nat) :
    run (t+1) c = run t c' := by
  exact (Function.iterate_succ_apply _ _ _).trans (congrArg (run t) h)

theorem skip_cons (b : Bool) (flags : List Bool) (r i : Nat)
    (saved : List Bool) :
    advance program
      (cfg (some .skip) (none, none) (b :: flags)
        (List.replicate (r+1) true) (List.replicate i true) [] saved) =
      cfg (some .skip) (none, none) flags
        (List.replicate r true) (List.replicate (i+1) true) [] saved := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, bank,
    List.replicate_succ, Function.update_apply]
  funext j
  fin_cases j <;> rfl

theorem skip_nil (r i : Nat) (saved : List Bool) :
    advance program
      (cfg (some .skip) (none, none) []
        (List.replicate (r+1) true) (List.replicate i true) [] saved) =
      cfg none (some true, none) []
        (List.replicate r true) (List.replicate i true) [false] saved := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, bank,
    List.replicate_succ, Function.update_apply]
  funext j
  fin_cases j <;> rfl

theorem skip_done (flags : List Bool) (i : Nat) (saved : List Bool) :
    advance program
      (cfg (some .skip) (none, none) flags []
        (List.replicate i true) [] saved) =
      cfg (some .scan) (none, none) flags []
        (List.replicate i true) [] saved := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, bank,
    Function.update_apply]

theorem scan_true (flags : List Bool) (i : Nat) (saved : List Bool) :
    advance program
      (cfg (some .scan) (none, none) (true :: flags) []
        (List.replicate i true) [] saved) =
      cfg none (none, some true) flags []
        (List.replicate i true) [true] saved := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, bank,
    Function.update_apply]
  funext j
  fin_cases j <;> rfl

theorem scan_false (flags : List Bool) (i : Nat) (saved : List Bool) :
    advance program
      (cfg (some .scan) (none, none) (false :: flags) []
        (List.replicate i true) [] saved) =
      cfg (some .scan) (none, none) flags []
        (List.replicate (i+1) true) [] saved := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, bank,
    List.replicate_succ, Function.update_apply]
  funext j
  fin_cases j <;> rfl

theorem scan_nil (i : Nat) (saved : List Bool) :
    advance program
      (cfg (some .scan) (none, none) [] []
        (List.replicate i true) [] saved) =
      cfg none (none, none) [] []
        (List.replicate i true) [false] saved := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, bank,
    Function.update_apply]
  funext j
  fin_cases j <;> rfl

def firstHit : List Bool → Nat → Bool × Nat
  | [], _ => (false, 0)
  | _ :: xs, r + 1 =>
      let p := firstHit xs r
      (p.1, p.2 + 1)
  | true :: _, 0 => (true, 0)
  | false :: xs, 0 =>
      let p := firstHit xs 0
      (p.1, p.2 + 1)

def initial (flags : List Bool) (r : Nat) (saved : List Bool) : Config :=
  cfg (some .skip) (none, none) flags (List.replicate r true) [] [] saved

theorem scan_from (flags : List Bool) (i : Nat) (saved : List Bool) :
    ∃ t ≤ flags.length + 1,
      (run t (cfg (some .scan) (none, none) flags []
        (List.replicate i true) [] saved)).l = none ∧
      (run t (cfg (some .scan) (none, none) flags []
        (List.replicate i true) [] saved)).stk 2 =
        List.replicate (i + (firstHit flags 0).2) true ∧
      (run t (cfg (some .scan) (none, none) flags []
        (List.replicate i true) [] saved)).stk 3 =
        [(firstHit flags 0).1] ∧
      (run t (cfg (some .scan) (none, none) flags []
        (List.replicate i true) [] saved)).stk 4 = saved := by
  induction flags generalizing i with
  | nil =>
      refine ⟨1, by omega, ?_, ?_, ?_, ?_⟩
      all_goals rw [run_succ (scan_nil i saved) 0]
      all_goals rfl
  | cons b xs ih =>
      cases b with
      | true =>
          refine ⟨1, by omega, ?_, ?_, ?_, ?_⟩
          all_goals rw [run_succ (scan_true xs i saved) 0]
          all_goals rfl
      | false =>
          obtain ⟨t, ht, hh, hi, hf, hs⟩ := ih (i+1)
          refine ⟨t+1, by simp only [List.length_cons]; omega, ?_, ?_, ?_, ?_⟩
          · rw [run_succ (scan_false xs i saved) t]
            exact hh
          · rw [run_succ (scan_false xs i saved) t, hi]
            simp only [firstHit]
            congr 1
            omega
          · rw [run_succ (scan_false xs i saved) t, hf]
            rfl
          · rw [run_succ (scan_false xs i saved) t]
            exact hs

theorem skip_from (flags : List Bool) (r i : Nat) (saved : List Bool) :
    ∃ t ≤ flags.length + 2,
      (run t (cfg (some .skip) (none, none) flags
        (List.replicate r true) (List.replicate i true) [] saved)).l = none ∧
      (run t (cfg (some .skip) (none, none) flags
        (List.replicate r true) (List.replicate i true) [] saved)).stk 2 =
        List.replicate (i + (firstHit flags r).2) true ∧
      (run t (cfg (some .skip) (none, none) flags
        (List.replicate r true) (List.replicate i true) [] saved)).stk 3 =
        [(firstHit flags r).1] ∧
      (run t (cfg (some .skip) (none, none) flags
        (List.replicate r true) (List.replicate i true) [] saved)).stk 4 = saved := by
  induction r generalizing flags i with
  | zero =>
      obtain ⟨t, ht, hh, hi, hf, hs⟩ := scan_from flags i saved
      refine ⟨t+1, by omega, ?_, ?_, ?_, ?_⟩
      · simp only [List.replicate_zero]
        rw [run_succ (skip_done flags i saved) t]
        exact hh
      · simp only [List.replicate_zero]
        rw [run_succ (skip_done flags i saved) t]
        exact hi
      · simp only [List.replicate_zero]
        rw [run_succ (skip_done flags i saved) t]
        exact hf
      · simp only [List.replicate_zero]
        rw [run_succ (skip_done flags i saved) t]
        exact hs
  | succ r ih =>
      cases flags with
      | nil =>
          refine ⟨1, by omega, ?_, ?_, ?_, ?_⟩
          all_goals rw [run_succ (skip_nil r i saved) 0]
          all_goals rfl
      | cons b xs =>
          obtain ⟨t, ht, hh, hi, hf, hs⟩ := ih xs (i+1)
          refine ⟨t+1, by simp only [List.length_cons]; omega, ?_, ?_, ?_, ?_⟩
          · rw [run_succ (skip_cons b xs r i saved) t]
            exact hh
          · rw [run_succ (skip_cons b xs r i saved) t, hi]
            simp only [firstHit]
            congr 1
            omega
          · rw [run_succ (skip_cons b xs r i saved) t, hf]
            rfl
          · rw [run_succ (skip_cons b xs r i saved) t]
            exact hs

theorem outputs (flags : List Bool) (r : Nat) (saved : List Bool) :
    ∃ t ≤ flags.length + 2,
      (run t (initial flags r saved)).l = none ∧
      (run t (initial flags r saved)).stk 2 =
        List.replicate (firstHit flags r).2 true ∧
      (run t (initial flags r saved)).stk 3 = [(firstHit flags r).1] ∧
      (run t (initial flags r saved)).stk 4 = saved := by
  simpa [initial] using skip_from flags r 0 saved

def selected (flags : List Bool) (r : Nat) : Option Nat :=
  let p := firstHit flags r
  if p.1 then some p.2 else none

theorem selected_zero (flags : List Bool) :
    selected flags 0 = flags.findIdx? id := by
  induction flags with
  | nil => rfl
  | cons b xs ih =>
      cases b with
      | true => rfl
      | false =>
          simp only [selected, firstHit, List.findIdx?_cons,
            Bool.false_eq_true, ↓reduceIte, Function.comp_def]
          rw [← ih]
          simp [selected]

theorem selected_drop (flags : List Bool) (r : Nat) :
    selected flags r = ((flags.drop r).findIdx? id).map (r + ·) := by
  induction r generalizing flags with
  | zero => simpa using selected_zero flags
  | succ r ih =>
      cases flags with
      | nil => simp [selected, firstHit]
      | cons b xs =>
          have h := ih xs
          simp only [selected, firstHit, List.drop_succ_cons]
          cases p : firstHit xs r with
          | mk found offset =>
              cases found <;>
                cases q : (xs.drop r).findIdx? id <;>
                simp [selected, p, q] at h ⊢
              all_goals omega

#print axioms selected_drop

#print axioms outputs

end CurrentAdditive.GaussFlagSearch
