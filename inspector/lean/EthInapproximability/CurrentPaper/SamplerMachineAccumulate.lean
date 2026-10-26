import EthInapproximability.CurrentPaper.SamplerMachine

/-!
# Stored coefficient addition with a preserved source

Source: v8 `E-exact-details.tex`, binary polynomial arithmetic in
`lem:exact-families`. This uniform finite program replaces `u` by
`u + b*v` and restores `v`, for one Boolean coefficient `b`. Its four
stacks store only bits; both input words have the same length.
-/

namespace EthInapproximability.CurrentPaper.SamplerMachineAccumulate

open Turing Turing.TM2.Stmt BitMachineEncoding
open SamplerMachine ExecutableSmallBiasSampler

def addScaled (b : Bool) (u v : List Bool) : List Bool :=
  List.zipWith (fun x y => Bool.xor x (b && y)) u v

inductive Label where
  | scan | restore
  deriving DecidableEq, Fintype

abbrev Control := Bool × Option Bool × Option Bool

def program : Label → TM2.Stmt (fun _ : Fin 4 => Bool) Label Control
  | .scan => pop 0 (fun s x => (s.1, x, none))
      (pop 1 (fun s y => (s.1, s.2.1, y))
        (branch (fun s => s.2.1.isSome)
          (push 2 (fun s => Bool.xor (s.2.1.getD false) (s.1 && s.2.2.getD false))
            (push 3 (fun s => s.2.2.getD false) (goto (fun _ => .scan))))
          (goto (fun _ => .restore))))
  | .restore => pop 2 (fun s x => (s.1, x, none))
      (pop 3 (fun s y => (s.1, s.2.1, y))
        (branch (fun s => s.2.1.isSome)
          (push 0 (fun s => s.2.1.getD false)
            (push 1 (fun s => s.2.2.getD false) (goto (fun _ => .restore))))
          (load (fun s => (s.1, none, none)) halt)))

def stackContents (u v su sv : List Bool) : Fin 4 → List Bool :=
  fun k => if k = 0 then u else if k = 1 then v else if k = 2 then su else sv

@[simp] private theorem stack_zero (u v su sv : List Bool) : stackContents u v su sv 0 = u := rfl
@[simp] private theorem stack_one (u v su sv : List Bool) : stackContents u v su sv 1 = v := rfl
@[simp] private theorem stack_two (u v su sv : List Bool) : stackContents u v su sv 2 = su := rfl
@[simp] private theorem stack_three (u v su sv : List Bool) : stackContents u v su sv 3 = sv := rfl

def cfg (l : Option Label) (s : Control) (u v su sv : List Bool) :
    TM2.Cfg (fun _ : Fin 4 => Bool) Label Control :=
  ⟨l, s, stackContents u v su sv⟩

def run (n : ℕ) (c : TM2.Cfg (fun _ : Fin 4 => Bool) Label Control) :=
  ((advance program)^[n]) c

private theorem run_succ {c d : TM2.Cfg (fun _ : Fin 4 => Bool) Label Control}
    (h : TM2.step program c = some d) (n : ℕ) : run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : TM2.Cfg (fun _ : Fin 4 => Bool) Label Control}
    {m : ℕ} (h : run m c = d) (n : ℕ) : run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem step_scan_cons (b : Bool) (p q : Option Bool)
    (x y : Bool) (u v su sv : List Bool) :
    TM2.step program (cfg (some .scan) (b, p, q) (x :: u) (y :: v) su sv) =
      some (cfg (some .scan) (b, some x, some y) u v
        (Bool.xor x (b && y) :: su) (y :: sv)) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

private theorem step_scan_nil (b : Bool) (p q : Option Bool) (su sv : List Bool) :
    TM2.step program (cfg (some .scan) (b, p, q) [] [] su sv) =
      some (cfg (some .restore) (b, none, none) [] [] su sv) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

private theorem step_restore_cons (b : Bool) (p q : Option Bool)
    (x y : Bool) (u v su sv : List Bool) :
    TM2.step program (cfg (some .restore) (b, p, q) u v (x :: su) (y :: sv)) =
      some (cfg (some .restore) (b, some x, some y) (x :: u) (y :: v) su sv) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

private theorem step_restore_nil (b : Bool) (p q : Option Bool) (u v : List Bool) :
    TM2.step program (cfg (some .restore) (b, p, q) u v [] []) =
      some (cfg none (b, none, none) u v [] []) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

theorem scan_correct (b : Bool) (p q : Option Bool) (u v su sv : List Bool)
    (hlen : u.length = v.length) :
    run (u.length + 1) (cfg (some .scan) (b, p, q) u v su sv) =
      cfg (some .restore) (b, none, none) [] []
        ((addScaled b u v).reverse ++ su) (v.reverse ++ sv) := by
  induction u generalizing v p q su sv with
  | nil =>
      have hv : v = [] := List.length_eq_zero_iff.mp hlen.symm
      subst v
      simpa [addScaled] using run_succ (step_scan_nil b p q su sv) 0
  | cons x u ih =>
      cases v with
      | nil => simp at hlen
      | cons y v =>
          have hl : u.length = v.length := by simpa using hlen
          rw [List.length_cons, run_succ (step_scan_cons b p q x y u v su sv)]
          simpa [addScaled, List.reverse_cons, List.append_assoc] using
            ih (some x) (some y) v (Bool.xor x (b && y) :: su) (y :: sv) hl

theorem restore_correct (b : Bool) (p q : Option Bool) (u v su sv : List Bool)
    (hlen : su.length = sv.length) :
    run (su.length + 1) (cfg (some .restore) (b, p, q) u v su sv) =
      cfg none (b, none, none) (su.reverse ++ u) (sv.reverse ++ v) [] [] := by
  induction su generalizing sv p q u v with
  | nil =>
      have hv : sv = [] := List.length_eq_zero_iff.mp hlen.symm
      subst sv
      simpa using run_succ (step_restore_nil b p q u v) 0
  | cons x su ih =>
      cases sv with
      | nil => simp at hlen
      | cons y sv =>
          have hl : su.length = sv.length := by simpa using hlen
          rw [List.length_cons, run_succ (step_restore_cons b p q x y u v su sv)]
          simpa [List.reverse_cons, List.append_assoc] using
            ih (some x) (some y) (x :: u) (y :: v) sv hl

/-- Actual complete configuration after the uniform four-stack program.
The input source is restored and both scratch stacks are cleared. -/
theorem run_correct (b : Bool) (p q : Option Bool) (u v : List Bool)
    (hlen : u.length = v.length) :
    run (2 * u.length + 2) (cfg (some .scan) (b, p, q) u v [] []) =
      cfg none (b, none, none) (addScaled b u v) v [] [] := by
  have hl : (addScaled b u v).length = u.length := by simp [addScaled, hlen]
  have hs := scan_correct b p q u v [] [] hlen
  simp only [List.append_nil] at hs
  have hr := restore_correct b none none [] [] (addScaled b u v).reverse v.reverse (by
    simp only [List.length_reverse, hl, hlen])
  simp only [List.length_reverse, hl, List.reverse_reverse, List.append_nil] at hr
  have h := (run_add hs (u.length + 1)).trans hr
  have ht : u.length + 1 + (u.length + 1) = 2 * u.length + 2 := by omega
  rwa [ht] at h

theorem encodeBit_mul (a b : ZMod 2) :
    encodeBit (a * b) = (encodeBit a && encodeBit b) := by
  fin_cases a <;> fin_cases b <;> decide

theorem addScaled_encodeWord {n : ℕ} (b : ZMod 2) (u v : BinaryWord n) :
    addScaled (encodeBit b) (encodeWord u) (encodeWord v) =
      encodeWord (wordAdd u (wordScale b v)) := by
  apply List.ext_getElem
  · simp [addScaled]
  · intro i hi hj
    simp [addScaled, encodeWord, wordAdd, wordScale, encodeBit_add, encodeBit_mul]

/-- Operational correctness for the exact coefficient operation used by
shift-and-add field multiplication. The scalar stays a single control bit. -/
theorem run_wordAddScale {n : ℕ} (b : ZMod 2) (u v : BinaryWord n) :
    run (2 * n + 2)
      (cfg (some .scan) (encodeBit b, none, none) (encodeWord u) (encodeWord v) [] []) =
      cfg none (encodeBit b, none, none)
        (encodeWord (wordAdd u (wordScale b v))) (encodeWord v) [] [] := by
  simpa only [encodeWord_length, addScaled_encodeWord] using
    run_correct (encodeBit b) none none (encodeWord u) (encodeWord v) (by simp)

end EthInapproximability.CurrentPaper.SamplerMachineAccumulate
