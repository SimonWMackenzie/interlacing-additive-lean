import EthInapproximability.CurrentPaper.ExecutableSmallBiasSampler
import EthInapproximability.CurrentPaper.BitMachineCopy

/-!
# Operational binary coefficient arithmetic for the sampler

Source: locked v8 `E-exact-details.tex`, the explicit finite-field sampler
in `lem:exact-families`. These are actual uniform finite Boolean-stack
programs. Every stated time is a proved number of `TM2.step` transitions.
The complete irreducible search and trace-table controller is separate from
the arithmetic components already proved here.
-/

namespace EthInapproximability.CurrentPaper.SamplerMachine

open Turing Turing.TM2.Stmt BitMachineEncoding
open ExecutableSmallBiasSampler

/-- Interleaved coefficient pairs. A final unpaired bit is paired with zero;
the sampler only uses equal-length vectors. -/
def packedXor : List Bool → List Bool
  | [] => []
  | [a] => [a]
  | a :: b :: xs => Bool.xor a b :: packedXor xs

theorem packedXor_length_le (xs : List Bool) : (packedXor xs).length ≤ xs.length := by
  fun_induction packedXor xs <;> simp_all
  omega

def packWords : List Bool → List Bool → List Bool
  | [], _ => []
  | _, [] => []
  | a :: u, b :: v => a :: b :: packWords u v

theorem packedXor_packWords (u v : List Bool) :
    packedXor (packWords u v) = List.zipWith Bool.xor u v := by
  induction u generalizing v with
  | nil => simp [packWords, packedXor]
  | cons a u ih => cases v <;> simp [packWords, packedXor, ih]

theorem packWords_length (u v : List Bool) (h : u.length = v.length) :
    (packWords u v).length = 2 * u.length := by
  induction u generalizing v with
  | nil => simp [packWords]
  | cons a u ih =>
      cases v with
      | nil => simp at h
      | cons b v =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at h
          simp [packWords, ih v h]
          omega

/-- The literal Boolean encoding of one binary-field coefficient. -/
def encodeBit (a : ZMod 2) : Bool := decide (a = 1)

theorem encodeBit_add (a b : ZMod 2) :
    encodeBit (a + b) = Bool.xor (encodeBit a) (encodeBit b) := by
  fin_cases a <;> fin_cases b <;> decide

/-- Little-endian polynomial coefficient encoding. -/
def encodeWord {n : ℕ} (u : BinaryWord n) : List Bool :=
  List.ofFn (fun i => encodeBit (u i))

@[simp] theorem encodeWord_length {n : ℕ} (u : BinaryWord n) :
    (encodeWord u).length = n := List.length_ofFn

theorem packedXor_encodeWord {n : ℕ} (u v : BinaryWord n) :
    packedXor (packWords (encodeWord u) (encodeWord v)) = encodeWord (wordAdd u v) := by
  rw [packedXor_packWords]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [encodeWord, wordAdd, encodeBit_add]

namespace Xor

inductive Label where
  | scan | restore
  deriving DecidableEq, Fintype

abbrev Control := Option Bool × Option Bool

/-- A transition reads at most two input bits; both bits live in finite control. -/
def program : Label → TM2.Stmt (fun _ : Fin 3 => Bool) Label Control
  | .scan => pop 0 (fun _ b => (b, none))
      (branch (fun s => s.1.isSome)
        (pop 0 (fun s b => (s.1, b))
          (push 2 (fun s => Bool.xor (s.1.getD false) (s.2.getD false))
            (goto (fun _ => .scan))))
        (goto (fun _ => .restore)))
  | .restore => pop 2 (fun _ b => (b, none))
      (branch (fun s => s.1.isSome)
        (push 1 (fun s => s.1.getD false) (goto (fun _ => .restore)))
        (load (fun _ => (none, none)) halt))

def stackContents (input output saved : List Bool) : Fin 3 → List Bool :=
  fun k => if k = 0 then input else if k = 1 then output else saved

@[simp] private theorem stack_zero (q t b : List Bool) : stackContents q t b 0 = q := rfl
@[simp] private theorem stack_one (q t b : List Bool) : stackContents q t b 1 = t := rfl
@[simp] private theorem stack_two (q t b : List Bool) : stackContents q t b 2 = b := rfl

def cfg (l : Option Label) (s : Control) (input output saved : List Bool) :
    TM2.Cfg (fun _ : Fin 3 => Bool) Label Control :=
  ⟨l, s, stackContents input output saved⟩

def run (n : ℕ) (c : TM2.Cfg (fun _ : Fin 3 => Bool) Label Control) :=
  ((advance program)^[n]) c

private theorem run_succ {c d : TM2.Cfg (fun _ : Fin 3 => Bool) Label Control}
    (h : TM2.step program c = some d) (n : ℕ) : run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : TM2.Cfg (fun _ : Fin 3 => Bool) Label Control}
    {m : ℕ} (h : run m c = d) (n : ℕ) : run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem step_scan_pair (s : Control) (a b : Bool) (xs out saved : List Bool) :
    TM2.step program (cfg (some .scan) s (a :: b :: xs) out saved) =
      some (cfg (some .scan) (some a, some b) xs out (Bool.xor a b :: saved)) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

private theorem step_scan_single (s : Control) (a : Bool) (out saved : List Bool) :
    TM2.step program (cfg (some .scan) s [a] out saved) =
      some (cfg (some .scan) (some a, none) [] out (a :: saved)) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> simp [stackContents]

private theorem step_scan_nil (s : Control) (out saved : List Bool) :
    TM2.step program (cfg (some .scan) s [] out saved) =
      some (cfg (some .restore) (none, none) [] out saved) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

private theorem step_restore_cons (s : Control) (a : Bool) (xs out saved : List Bool) :
    TM2.step program (cfg (some .restore) s xs out (a :: saved)) =
      some (cfg (some .restore) (some a, none) xs (a :: out) saved) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

private theorem step_restore_nil (s : Control) (xs out : List Bool) :
    TM2.step program (cfg (some .restore) s xs out []) =
      some (cfg none (none, none) xs out []) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

theorem scan_correct (s : Control) (xs out saved : List Bool) :
    run ((packedXor xs).length + 1) (cfg (some .scan) s xs out saved) =
      cfg (some .restore) (none, none) [] out ((packedXor xs).reverse ++ saved) := by
  fun_induction packedXor xs generalizing s saved with
  | case1 => simpa [packedXor] using run_succ (step_scan_nil s out saved) 0
  | case2 a =>
      change run (1 + 1) (cfg (some .scan) s [a] out saved) =
        cfg (some .restore) (none, none) [] out (a :: saved)
      rw [run_succ (step_scan_single s a out saved)]
      simpa using run_succ (step_scan_nil (some a, none) out (a :: saved)) 0
  | case3 a b xs ih =>
      change run ((packedXor xs).length + 1 + 1)
        (cfg (some .scan) s (a :: b :: xs) out saved) = _
      rw [run_succ (step_scan_pair s a b xs out saved)]
      simpa [List.reverse_cons, List.append_assoc] using
        ih (some a, some b) (Bool.xor a b :: saved)

theorem restore_correct (s : Control) (xs out saved : List Bool) :
    run (saved.length + 1) (cfg (some .restore) s xs out saved) =
      cfg none (none, none) xs (saved.reverse ++ out) [] := by
  induction saved generalizing s out with
  | nil => simpa using run_succ (step_restore_nil s xs out) 0
  | cons a saved ih =>
      rw [List.length_cons, run_succ (step_restore_cons s a xs out saved)]
      simpa [List.reverse_cons, List.append_assoc] using ih (some a, none) (a :: out)

/-- Exact transition count for all input words, including malformed odd lengths. -/
theorem run_correct (s : Control) (xs out : List Bool) :
    run (2 * (packedXor xs).length + 2) (cfg (some .scan) s xs out []) =
      cfg none (none, none) [] (packedXor xs ++ out) [] := by
  have hs := scan_correct s xs out []
  simp only [List.append_nil] at hs
  have hr := restore_correct (none, none) [] out (packedXor xs).reverse
  simp only [List.length_reverse, List.reverse_reverse] at hr
  have h := (run_add hs ((packedXor xs).length + 1)).trans hr
  have htime : (packedXor xs).length + 1 + ((packedXor xs).length + 1) =
      2 * (packedXor xs).length + 2 := by omega
  rw [htime] at h
  exact h

noncomputable def bitMachine : BitMachine.Machine :=
  ofFinite (0 : Fin 3) 1 .scan ((none, none) : Control) program

private theorem initial_eq (xs : List Bool) :
    rawInit (0 : Fin 3) .scan ((none, none) : Control) xs =
      cfg (some .scan) (none, none) xs [] [] := by
  unfold rawInit cfg
  congr 1
  funext k
  fin_cases k <;> rfl

theorem bitMachine_outputs (xs : List Bool) :
    bitMachine.OutputsWithin xs (packedXor xs) (2 * (packedXor xs).length + 2) := by
  apply outputsWithin_of_raw_run (0 : Fin 3) 1 .scan ((none, none) : Control) program
    xs (packedXor xs) (2 * (packedXor xs).length + 2) _ le_rfl
  · change (run (2 * (packedXor xs).length + 2) _).l = none
    rw [initial_eq, run_correct]
    rfl
  · change (run (2 * (packedXor xs).length + 2) _).stk 1 = packedXor xs
    rw [initial_eq, run_correct]
    simp [cfg, stackContents]

theorem polytime_packedXor : BitMachine.Polytime packedXor := by
  refine ⟨bitMachine, 2, 1, ?_⟩
  intro xs
  apply BitMachine.outputsWithin_mono bitMachine (bitMachine_outputs xs)
  have h := packedXor_length_le xs
  simp only [pow_one]
  omega

/-- The literal finite program implements the coefficient addition used by
the certified finite-field sampler, with its actual transition bound. -/
theorem bitMachine_wordAdd {n : ℕ} (u v : BinaryWord n) :
    bitMachine.OutputsWithin (packWords (encodeWord u) (encodeWord v))
      (encodeWord (wordAdd u v)) (2 * n + 2) := by
  simpa only [packedXor_encodeWord, encodeWord_length] using
    bitMachine_outputs (packWords (encodeWord u) (encodeWord v))

end Xor

end EthInapproximability.CurrentPaper.SamplerMachine
