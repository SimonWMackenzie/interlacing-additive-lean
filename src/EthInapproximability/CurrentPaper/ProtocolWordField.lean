import EthInapproximability.CurrentPaper.EncodedCommunication
import EthInapproximability.CurrentPaper.BitMachineEncoding

/-!
# Unrestricted word-field decoding

Source: locked v8 NP membership and its fixed bit-machine convention.
The outer instance/witness framing in EncodedComplexity uses arbitrary bit
words, not natural-number encodings. This finite machine therefore implements
readField without imposing the canonical-number check of ProtocolBinaryHeader.
A successful raw run preserves the suffix on its source stack.
-/

namespace EthInapproximability.CurrentPaper.ProtocolWordField

open Turing TM2.Stmt BitMachineEncoding EncodedCommunication

inductive Label where
  | scan | payload | restore
  deriving DecidableEq, Fintype

abbrev Control := Option Bool × Option Bool

def failure : TM2.Stmt (fun _ : Fin 3 => Bool) Label Control :=
  push 2 (fun _ => false) halt

def program : Label → TM2.Stmt (fun _ : Fin 3 => Bool) Label Control
  | .scan =>
      pop 0 (fun s b => (s.1, b))
        (branch (fun s => s.2.isSome)
          (branch (fun s => s.2.getD false) (goto (fun _ => .payload))
            (goto (fun _ => .restore))) failure)
  | .payload =>
      pop 0 (fun _ b => (b, b))
        (branch (fun s => s.2.isSome)
          (push 1 (fun s => s.2.getD false) (goto (fun _ => .scan))) failure)
  | .restore =>
      pop 1 (fun s b => (s.1, b))
        (branch (fun s => s.2.isSome)
          (push 2 (fun s => s.2.getD false) (goto (fun _ => .restore)))
          (push 2 (fun _ => true) halt))

def stackContents (source saved target : List Bool) : Fin 3 → List Bool :=
  fun k => if k = 0 then source else if k = 1 then saved else target

def cfg (l : Option Label) (s : Control) (source saved target : List Bool) :
    TM2.Cfg (fun _ : Fin 3 => Bool) Label Control :=
  ⟨l, s, stackContents source saved target⟩

def run (n : Nat) (c : TM2.Cfg (fun _ : Fin 3 => Bool) Label Control) :=
  ((advance program)^[n]) c

theorem run_succ_first (n : Nat) (c : TM2.Cfg (fun _ : Fin 3 => Bool) Label Control) :
    run (n + 1) c = run n (advance program c) := by
  exact Function.iterate_succ_apply _ _ _

theorem scan_nil (seen popped : Option Bool) (saved target : List Bool) :
    advance program (cfg (some .scan) (seen, popped) [] saved target) =
      cfg none (seen, none) [] saved (false :: target) := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, stackContents, failure]
  funext k
  fin_cases k <;> rfl

theorem scan_false (seen popped : Option Bool) (source saved target : List Bool) :
    advance program (cfg (some .scan) (seen, popped) (false :: source) saved target) =
      cfg (some .restore) (seen, some false) source saved target := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, stackContents, failure]
  funext k
  fin_cases k <;> rfl

theorem scan_true (seen popped : Option Bool) (source saved target : List Bool) :
    advance program (cfg (some .scan) (seen, popped) (true :: source) saved target) =
      cfg (some .payload) (seen, some true) source saved target := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, stackContents]
  funext k
  fin_cases k <;> rfl

theorem payload_nil (seen popped : Option Bool) (saved target : List Bool) :
    advance program (cfg (some .payload) (seen, popped) [] saved target) =
      cfg none (none, none) [] saved (false :: target) := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, stackContents, failure]
  funext k
  fin_cases k <;> rfl

theorem payload_cons (seen popped : Option Bool) (b : Bool) (source saved target : List Bool) :
    advance program (cfg (some .payload) (seen, popped) (b :: source) saved target) =
      cfg (some .scan) (some b, some b) source (b :: saved) target := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, stackContents, failure]
  funext k
  fin_cases k <;> rfl

theorem restore_nil (seen popped : Option Bool) (source target : List Bool) :
    advance program (cfg (some .restore) (seen, popped) source [] target) =
      cfg none (seen, none) source [] (true :: target) := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, stackContents]
  funext k
  fin_cases k <;> rfl

theorem restore_cons (seen popped : Option Bool) (b : Bool) (source saved target : List Bool) :
    advance program (cfg (some .restore) (seen, popped) source (b :: saved) target) =
      cfg (some .restore) (seen, some b) source saved (b :: target) := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, stackContents]
  funext k
  fin_cases k <;> rfl

theorem restore_correct (seen popped : Option Bool) (source saved target : List Bool) :
    run (saved.length + 1) (cfg (some .restore) (seen, popped) source saved target) =
      cfg none (seen, none) source [] (true :: (saved.reverse ++ target)) := by
  induction saved generalizing popped target with
  | nil => simp [restore_nil, run]
  | cons b saved ih =>
      rw [List.length_cons, run_succ_first, restore_cons, ih]
      simp

def Post (_seen : Option Bool) (input saved target : List Bool)
    (c : TM2.Cfg (fun _ : Fin 3 => Bool) Label Control) : Prop :=
  c.l = none ∧ match readField input with
    | none => c.stk 2 = false :: target
    | some (bs, rest) => c.stk 0 = rest ∧ c.stk 1 = [] ∧
        c.stk 2 = true :: (saved.reverse ++ bs ++ target)

/-- Total correctness and a linear transition bound, including truncated
fields. Successful reads preserve the unused suffix. -/
theorem scan_correct (input : List Bool) (seen popped : Option Bool)
    (saved target : List Bool) :
    ∃ t ≤ 2 * input.length + saved.length + 2,
      Post seen input saved target
        (run t (cfg (some .scan) (seen, popped) input saved target)) := by
  induction input using readField.induct generalizing seen popped saved target with
  | case1 =>
      refine ⟨1, by simp, ?_⟩
      rw [show 1 = 0 + 1 from rfl, run_succ_first, scan_nil]
      simp [Post, readField, run, cfg, stackContents]
  | case2 rest =>
      refine ⟨saved.length + 2, by simp, ?_⟩
      rw [show saved.length + 2 = (saved.length + 1) + 1 by omega,
        run_succ_first, scan_false, restore_correct]
      simp [Post, readField, cfg, stackContents]
  | case3 =>
      refine ⟨2, by simp, ?_⟩
      rw [show 2 = (0 + 1) + 1 from rfl, run_succ_first, scan_true,
        run_succ_first, payload_nil]
      simp [Post, readField, run, cfg, stackContents]
  | case4 b rest ih =>
      obtain ⟨t, ht, hpost⟩ := ih (some b) (some b) (b :: saved) target
      refine ⟨t + 2, by simp at ht ⊢; omega, ?_⟩
      rw [show t + 2 = (t + 1) + 1 by omega, run_succ_first, scan_true,
        run_succ_first, payload_cons]
      unfold Post at hpost ⊢
      refine ⟨hpost.1, ?_⟩
      cases hp : readField rest with
      | none => simpa [readField, hp] using hpost.2
      | some pair =>
          rcases pair with ⟨bs, suffix⟩
          simpa [readField, hp, List.reverse_cons, List.append_assoc] using hpost.2

/-- One flag bit distinguishes failure from a successfully decoded zero. -/
def result (input : List Bool) : List Bool :=
  match readField input with
  | none => [false]
  | some (bs, _) => true :: bs

noncomputable def machine : BitMachine.Machine :=
  ofFinite (0 : Fin 3) 2 .scan ((none, none) : Control) program

theorem rawInit_eq (input : List Bool) :
    rawInit (0 : Fin 3) .scan ((none, none) : Control) input =
      cfg (some .scan) (none, none) input [] [] := by
  unfold rawInit cfg
  congr 1
  funext k
  fin_cases k <;> rfl

theorem outputs (input : List Bool) :
    machine.OutputsWithin input (result input) (2 * input.length + 2) := by
  obtain ⟨t, ht, hpost⟩ := scan_correct input none none [] []
  apply outputsWithin_of_raw_run (0 : Fin 3) 2 .scan ((none, none) : Control)
    program input (result input) t (2 * input.length + 2) (by simpa using ht)
  · rw [rawInit_eq]
    exact hpost.1
  · rw [rawInit_eq]
    have h := hpost.2
    cases hp : readField input with
    | none => simpa [Post, result, hp] using h
    | some p =>
        rcases p with ⟨bs, suffix⟩
        have hout := h
        simp only [hp] at hout
        simpa [result, hp] using hout.2.2

theorem polytime : BitMachine.Polytime result := by
  refine ⟨machine, 2, 1, ?_⟩
  intro input
  simpa [Nat.mul_add] using outputs input


theorem field_regressions :
    result [] = [false] ∧ result [false] = [true] ∧
      result [true] = [false] ∧ result [true, false, false] = [true, false] ∧
      result [true, true, false, true] = [true, true] := by decide

end EthInapproximability.CurrentPaper.ProtocolWordField
