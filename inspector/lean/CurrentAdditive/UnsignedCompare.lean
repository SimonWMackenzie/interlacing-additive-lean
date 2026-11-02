import EthInapproximability.CurrentPaper.BitMachineBinaryDivision
import EthInapproximability.CurrentPaper.BitMachineBankWrapper
import EthInapproximability.CurrentPaper.BitMachineBinarySubtract

/-!
Variable-width little-endian unsigned subtraction and comparison.  The program
is fixed; it consumes two bit stacks, produces their zero-extended difference
modulo the word width, and records the final borrow in a one-bit stack.
-/

namespace EthInapproximability.CurrentPaper.UnsignedCompare

open Turing Turing.TM2.Stmt BitMachineEncoding
open BitMachineBinaryDivision (subAny subAny_spec)
open BitMachineBinarySubtract (outBit nextBorrow)

inductive Label where
  | scan | restore
  deriving DecidableEq, Fintype

structure Control where
  borrow : Bool
  a : Option Bool
  b : Option Bool
  deriving DecidableEq, Fintype

def initial : Control := ⟨false, none, none⟩

def program : Label → TM2.Stmt (fun _ : Fin 3 => Bool) Label Control
  | .scan =>
      pop 0 (fun s a => ⟨s.borrow, a, none⟩)
        (pop 1 (fun s b => ⟨s.borrow, s.a, b⟩)
          (branch (fun s => s.a.isSome || s.b.isSome)
            (push 2 (fun s => outBit (s.a.getD false) (s.b.getD false) s.borrow)
              (load (fun s => ⟨nextBorrow (s.a.getD false) (s.b.getD false)
                  s.borrow, none, none⟩)
                (goto (fun _ => .scan))))
            (goto (fun _ => .restore))))
  | .restore =>
      pop 2 (fun s a => ⟨s.borrow, a, none⟩)
        (branch (fun s => s.a.isSome)
          (push 0 (fun s => s.a.getD false) (goto (fun _ => .restore)))
          (push 1 (fun s => s.borrow) (load (fun _ => initial) halt)))

def bank (a b saved : List Bool) : Fin 3 → List Bool :=
  ![a,b,saved]

def cfg (l : Option Label) (s : Control) (a b saved : List Bool) :
    TM2.Cfg (fun _ : Fin 3 => Bool) Label Control :=
  ⟨l, s, bank a b saved⟩

def run (t : ℕ) (c : TM2.Cfg (fun _ : Fin 3 => Bool) Label Control) :=
  ((advance program)^[t]) c

private theorem run_step {c d : TM2.Cfg (fun _ : Fin 3 => Bool) Label Control}
    (h : TM2.step program c = some d) (t : ℕ) :
    run (t + 1) c = run t d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem scan_both (s : Control) (a b : Bool)
    (as bs saved : List Bool) :
    TM2.step program (cfg (some .scan) s (a :: as) (b :: bs) saved) =
      some (cfg (some .scan) ⟨nextBorrow a b s.borrow, none, none⟩
        as bs (outBit a b s.borrow :: saved)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k; fin_cases k <;> simp [bank]

private theorem scan_left (s : Control) (a : Bool)
    (as saved : List Bool) :
    TM2.step program (cfg (some .scan) s (a :: as) [] saved) =
      some (cfg (some .scan) ⟨nextBorrow a false s.borrow, none, none⟩
        as [] (outBit a false s.borrow :: saved)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k; fin_cases k <;> simp [bank]

private theorem scan_right (s : Control) (b : Bool)
    (bs saved : List Bool) :
    TM2.step program (cfg (some .scan) s [] (b :: bs) saved) =
      some (cfg (some .scan) ⟨nextBorrow false b s.borrow, none, none⟩
        [] bs (outBit false b s.borrow :: saved)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k; fin_cases k <;> simp [bank]

private theorem scan_nil (s : Control) (saved : List Bool) :
    TM2.step program (cfg (some .scan) s [] [] saved) =
      some (cfg (some .restore) ⟨s.borrow, none, none⟩ [] [] saved) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k; fin_cases k <;> simp [bank]

private theorem restore_cons (s : Control) (a b : List Bool) (x : Bool)
    (saved : List Bool) :
    TM2.step program (cfg (some .restore) s a b (x :: saved)) =
      some (cfg (some .restore) ⟨s.borrow, some x, none⟩ (x :: a) b saved) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k; fin_cases k <;> simp [bank]

private theorem restore_nil (s : Control) (a b : List Bool) :
    TM2.step program (cfg (some .restore) s a b []) =
      some (cfg none initial a (s.borrow :: b) []) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k; fin_cases k <;> simp [bank]

theorem restore_correct (s : Control) (a b saved : List Bool) :
    run (saved.length + 1) (cfg (some .restore) s a b saved) =
      cfg none initial (saved.reverse ++ a) (s.borrow :: b) [] := by
  induction saved generalizing s a with
  | nil => simpa using run_step (restore_nil s a b) 0
  | cons x saved ih =>
      rw [List.length_cons, run_step (restore_cons s a b x saved)]
      simpa [List.reverse_cons, List.append_assoc] using
        ih ⟨s.borrow, some x, none⟩ (x :: a)

theorem scan_correct (a b : List Bool) (borrow : Bool) (saved : List Bool) :
    run (2 * max a.length b.length + saved.length + 2)
      (cfg (some .scan) ⟨borrow, none, none⟩ a b saved) =
      cfg none initial (saved.reverse ++ (subAny a b borrow).1)
        [(subAny a b borrow).2] [] := by
  induction a, b, borrow using subAny.induct generalizing saved with
  | case1 borrow =>
      have h := run_step (scan_nil ⟨borrow, none, none⟩ saved) (saved.length + 1)
      simpa [subAny] using h.trans
        (restore_correct ⟨borrow, none, none⟩ [] [] saved)
  | case2 x xs borrow ih =>
      have h := run_step (scan_left ⟨borrow, none, none⟩ x xs saved)
        (2 * xs.length + (outBit x false borrow :: saved).length + 2)
      rw [show 2 * max (x :: xs).length ([] : List Bool).length + saved.length + 2 =
          (2 * xs.length + (outBit x false borrow :: saved).length + 2) + 1 by simp; omega]
      simpa [subAny, List.reverse_cons, List.append_assoc] using
        h.trans (by simpa using ih (outBit x false borrow :: saved))
  | case3 y ys borrow ih =>
      have h := run_step (scan_right ⟨borrow, none, none⟩ y ys saved)
        (2 * ys.length + (outBit false y borrow :: saved).length + 2)
      rw [show 2 * max ([] : List Bool).length (y :: ys).length + saved.length + 2 =
          (2 * ys.length + (outBit false y borrow :: saved).length + 2) + 1 by simp; omega]
      simpa [subAny, List.reverse_cons, List.append_assoc] using
        h.trans (by simpa using ih (outBit false y borrow :: saved))
  | case4 x xs y ys borrow ih =>
      have h := run_step (scan_both ⟨borrow, none, none⟩ x y xs ys saved)
        (2 * max xs.length ys.length +
          (outBit x y borrow :: saved).length + 2)
      rw [show 2 * max (x :: xs).length (y :: ys).length + saved.length + 2 =
          (2 * max xs.length ys.length +
            (outBit x y borrow :: saved).length + 2) + 1 by simp [Nat.succ_max_succ]; omega]
      simpa [subAny, List.reverse_cons, List.append_assoc] using
        h.trans (by simpa using ih (outBit x y borrow :: saved))

theorem run_correct (a b : List Bool) :
    run (2 * max a.length b.length + 2)
      (cfg (some .scan) initial a b []) =
      cfg none initial (subAny a b false).1 [(subAny a b false).2] [] := by
  simpa [initial] using scan_correct a b false []

theorem compare_correct (a b : List Bool) :
    (run (2 * max a.length b.length + 2)
      (cfg (some .scan) initial a b [])).stk 1 =
      [decide (EncodedCommunication.bitsValue a < EncodedCommunication.bitsValue b)] := by
  rw [run_correct]
  simp [cfg, bank, (subAny_spec a b).1]

#print axioms run_correct
#print axioms compare_correct

end EthInapproximability.CurrentPaper.UnsignedCompare
