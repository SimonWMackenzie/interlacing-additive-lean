import EthInapproximability.CurrentPaper.SamplerMachine

/-!
# Modulus-preserving binary coefficient shift on Boolean stacks

Source: locked v8 `E-exact-details.tex`, the coefficient presentation in the
explicit finite-field sampler of `lem:exact-families`. The modulus coefficients
are input data, never a program parameter or an unbounded control register.
Stack 0 stores the modulus, stack 1 the word, and stack 2 temporary paired bits.
The two passes use exactly `2*n+2` transitions on equal-width inputs.
-/

namespace EthInapproximability.CurrentPaper.SamplerMachineShift

open Turing Turing.TM2.Stmt BitMachineEncoding
open SamplerMachine ExecutableSmallBiasSampler

abbrev Pair := Bool × Bool

/-- Low-to-high coefficient pairs packed in the order modulus, word. -/
def pairBits : List Pair → List Bool
  | [] => []
  | (c, u) :: q => c :: u :: pairBits q

/-- High-to-low scratch representation, word bit first in each pair. -/
def savedBits : List Pair → List Bool
  | [] => []
  | (c, u) :: q => u :: c :: savedBits q

theorem pairBits_reverse (q : List Pair) :
    (pairBits q).reverse = savedBits q.reverse := by
  have happ (a b : List Pair) : savedBits (a ++ b) = savedBits a ++ savedBits b := by
    induction a with
    | nil => rfl
    | cons p a ih => rcases p with ⟨c, u⟩; simp [savedBits, ih]
  induction q with
  | nil => rfl
  | cons p q ih =>
      rcases p with ⟨c, u⟩
      simp [pairBits, savedBits, List.reverse_cons, happ, ih, List.append_assoc]

def finalBit (initial : Bool) : List Pair → Bool
  | [] => initial
  | (_, u) :: q => finalBit u q

theorem finalBit_eq (initial : Bool) (q : List Pair) :
    finalBit initial q = ((q.map Prod.snd).getLast?).getD initial := by
  induction q generalizing initial with
  | nil => rfl
  | cons p q ih =>
      rcases p with ⟨c, u⟩
      simp [finalBit, List.getLast?_cons, ih]

/-- What the restore pass writes, listed in its high-to-low visitation order. -/
def highShift (top : Bool) : List Pair → List Bool
  | [] => []
  | (c, _) :: q =>
      Bool.xor ((q.head?.map Prod.snd).getD false) (top && c) :: highShift top q

theorem highShift_length (top : Bool) (q : List Pair) :
    (highShift top q).length = q.length := by
  induction q with
  | nil => rfl
  | cons p q ih => rcases p with ⟨c, u⟩; simp [highShift, ih]

/-- Ordinary low-to-high coefficient specification of one modular shift. -/
def shiftLists (c u : List Bool) : List Bool :=
  List.zipWith (fun ci lo => Bool.xor lo (u.getLast?.getD false && ci))
    c (false :: u.dropLast)

theorem highShift_eq_zip (top : Bool) (q : List Pair) :
    highShift top q = List.zipWith (fun c lo => Bool.xor lo (top && c))
      (q.map Prod.fst) ((q.map Prod.snd).tail ++ [false]) := by
  induction q with
  | nil => rfl
  | cons p q ih =>
      rcases p with ⟨c, u⟩
      cases q with
      | nil => rfl
      | cons p q =>
          rcases p with ⟨c', u'⟩
          simpa [highShift] using congrArg (Bool.xor u' (top && c) :: ·) ih

theorem highShift_reverse (q : List Pair) :
    (highShift (finalBit false q) q.reverse).reverse =
      shiftLists (q.map Prod.fst) (q.map Prod.snd) := by
  cases q with
  | nil => rfl
  | cons p q =>
      rw [highShift_eq_zip, List.reverse_zipWith]
      · simp only [List.map_reverse, List.reverse_reverse, List.reverse_append,
          List.reverse_singleton, ← List.dropLast_reverse, List.singleton_append,
          finalBit_eq, shiftLists]
      · simp

inductive Label where
  | scan | restore
  deriving DecidableEq, Fintype

structure Control where
  top : Bool
  c : Option Bool
  u : Option Bool
  deriving DecidableEq, Fintype

def initial : Control := ⟨false, none, none⟩

/-- Only three bits/options are held in control. Each statement handles one pair. -/
def program : Label → TM2.Stmt (fun _ : Fin 3 => Bool) Label Control
  | .scan => pop 0 (fun s c => ⟨s.top, c, none⟩)
      (pop 1 (fun s u => ⟨u.getD s.top, s.c, u⟩)
        (branch (fun s => s.c.isSome && s.u.isSome)
          (push 2 (fun s => s.c.getD false)
            (push 2 (fun s => s.u.getD false) (goto (fun _ => .scan))))
          (goto (fun _ => .restore))))
  | .restore => pop 2 (fun s u => ⟨s.top, none, u⟩)
      (branch (fun s => s.u.isSome)
        (pop 2 (fun s c => ⟨s.top, c, s.u⟩)
          (peek 2 (fun s lo => ⟨s.top, s.c, lo⟩)
            (push 0 (fun s => s.c.getD false)
              (push 1 (fun s => Bool.xor (s.u.getD false) (s.top && s.c.getD false))
                (goto (fun _ => .restore))))))
        (load (fun _ => initial) halt))

def stackContents (c u saved : List Bool) : Fin 3 → List Bool :=
  fun k => if k = 0 then c else if k = 1 then u else saved

@[simp] private theorem stack_zero (c u b : List Bool) : stackContents c u b 0 = c := rfl
@[simp] private theorem stack_one (c u b : List Bool) : stackContents c u b 1 = u := rfl
@[simp] private theorem stack_two (c u b : List Bool) : stackContents c u b 2 = b := rfl

def cfg (l : Option Label) (s : Control) (c u saved : List Bool) :
    TM2.Cfg (fun _ : Fin 3 => Bool) Label Control :=
  ⟨l, s, stackContents c u saved⟩

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

private theorem step_scan_cons (s : Control) (a b : Bool) (c u saved : List Bool) :
    TM2.step program (cfg (some .scan) s (a :: c) (b :: u) saved) =
      some (cfg (some .scan) ⟨b, some a, some b⟩ c u (b :: a :: saved)) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

private theorem step_scan_nil (s : Control) (saved : List Bool) :
    TM2.step program (cfg (some .scan) s [] [] saved) =
      some (cfg (some .restore) ⟨s.top, none, none⟩ [] [] saved) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

private theorem savedBits_head (q : List Pair) :
    (savedBits q).head? = q.head?.map Prod.snd := by
  cases q with
  | nil => rfl
  | cons p q => cases p; rfl

private theorem step_restore_cons (s : Control) (a b : Bool)
    (q : List Pair) (c u : List Bool) :
    TM2.step program (cfg (some .restore) s c u (savedBits ((a, b) :: q))) =
      some (cfg (some .restore) ⟨s.top, some a, q.head?.map Prod.snd⟩
        (a :: c) (Bool.xor ((q.head?.map Prod.snd).getD false) (s.top && a) :: u)
        (savedBits q)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, savedBits, savedBits_head]
  funext k
  fin_cases k <;> rfl

private theorem step_restore_nil (s : Control) (c u : List Bool) :
    TM2.step program (cfg (some .restore) s c u []) =
      some (cfg none initial c u []) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

theorem scan_correct (s : Control) (q : List Pair) (saved : List Bool) :
    run (q.length + 1) (cfg (some .scan) s (q.map Prod.fst) (q.map Prod.snd) saved) =
      cfg (some .restore) ⟨finalBit s.top q, none, none⟩ [] []
        ((pairBits q).reverse ++ saved) := by
  induction q generalizing s saved with
  | nil => simpa [pairBits, finalBit] using run_succ (step_scan_nil s saved) 0
  | cons p q ih =>
      rcases p with ⟨a, b⟩
      rw [List.length_cons, List.map_cons, List.map_cons,
        run_succ (step_scan_cons s a b _ _ saved)]
      simpa [pairBits, finalBit, List.reverse_cons, List.append_assoc] using
        ih ⟨b, some a, some b⟩ (b :: a :: saved)

theorem restore_correct (s : Control) (q : List Pair) (c u : List Bool) :
    run (q.length + 1) (cfg (some .restore) s c u (savedBits q)) =
      cfg none initial ((q.map Prod.fst).reverse ++ c)
        ((highShift s.top q).reverse ++ u) [] := by
  induction q generalizing s c u with
  | nil => simpa [savedBits, highShift] using run_succ (step_restore_nil s c u) 0
  | cons p q ih =>
      rcases p with ⟨a, b⟩
      rw [List.length_cons, run_succ (step_restore_cons s a b q c u)]
      simpa [highShift, List.reverse_cons, List.append_assoc] using
        ih ⟨s.top, some a, q.head?.map Prod.snd⟩ (a :: c)
          (Bool.xor ((q.head?.map Prod.snd).getD false) (s.top && a) :: u)

/-- Exact uniform controller result: restore every modulus bit, replace only
the word, clear scratch, and halt in `2*n+2` literal transitions. -/
theorem run_correct (q : List Pair) :
    run (2 * q.length + 2)
        (cfg (some .scan) initial (q.map Prod.fst) (q.map Prod.snd) []) =
      cfg none initial (q.map Prod.fst)
        (shiftLists (q.map Prod.fst) (q.map Prod.snd)) [] := by
  have hs := scan_correct initial q []
  simp only [List.append_nil, initial, pairBits_reverse] at hs
  have hr := restore_correct ⟨finalBit false q, none, none⟩ q.reverse [] []
  simp only [List.length_reverse, List.map_reverse, List.reverse_reverse,
    List.append_nil, highShift_reverse] at hr
  have h := (run_add hs (q.length + 1)).trans hr
  simpa only [Nat.two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- Equal-width inputs can be supplied separately, without a prepacked list. -/
theorem run_lists (c u : List Bool) (hlen : c.length = u.length) :
    run (2 * c.length + 2) (cfg (some .scan) initial c u []) =
      cfg none initial c (shiftLists c u) [] := by
  have hc := List.map_fst_zip (l₁ := c) (l₂ := u) hlen.le
  have hu := List.map_snd_zip (l₁ := c) (l₂ := u) hlen.ge
  simpa [hc, hu, List.length_zip, hlen] using run_correct (c.zip u)

theorem encodeBit_sub_mul (a b c : ZMod 2) :
    encodeBit (a - b * c) = Bool.xor (encodeBit a) (encodeBit b && encodeBit c) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> decide

/-- Coefficient shift modulo the monic polynomial whose lower coefficients are
`c`. No irreducibility or selected-modulus assumption is involved. -/
def shiftWith : {n : ℕ} → BinaryWord n → BinaryWord n → BinaryWord n
  | 0, _, u => u
  | k + 1, c, u =>
      let low : BinaryWord (k + 1) := Fin.cons 0 (fun j : Fin k => u j.castSucc)
      fun i => low i - u (Fin.last k) * c i

@[simp] theorem shiftWith_chosenWord {n : ℕ} (u : BinaryWord n) :
    shiftWith (chosenWord n) u = wordShift n u := by
  cases n <;> rfl

/-- The controller's list-level shift is correct for any supplied modulus. -/
theorem shiftLists_encodeWordWith {n : ℕ} (c u : BinaryWord n) :
    shiftLists (encodeWord c) (encodeWord u) = encodeWord (shiftWith c u) := by
  cases n with
  | zero => simp [shiftLists, encodeWord, shiftWith]
  | succ k =>
      let low : BinaryWord (k + 1) := Fin.cons 0 (fun j : Fin k => u j.castSucc)
      have hlast : (encodeWord u).getLast?.getD false = encodeBit (u (Fin.last k)) := by
        unfold encodeWord
        rw [List.ofFn_succ_last]
        simp
      have hlow : false :: (encodeWord u).dropLast = encodeWord low := by
        unfold encodeWord
        rw [List.ofFn_succ_last]
        simp [low, encodeBit]
      unfold shiftLists
      rw [hlast, hlow]
      apply List.ext_getElem
      · simp [encodeWord]
      · intro i hi hj
        simp only [List.getElem_zipWith, encodeWord, List.getElem_ofFn,
          shiftWith, low, encodeBit_sub_mul]

/-- The list-level shift is exactly the existing chosen-modulus word shift. -/
theorem shiftLists_encodeWord {n : ℕ} (u : BinaryWord n) :
    shiftLists (encodeWord (chosenWord n)) (encodeWord u) =
      encodeWord (wordShift n u) := by
  simpa using shiftLists_encodeWordWith (chosenWord n) u

/-- The same fixed controller works with arbitrary monic-modulus coefficients. -/
theorem run_wordShiftWith {n : ℕ} (c u : BinaryWord n) :
    run (2 * n + 2) (cfg (some .scan) initial (encodeWord c) (encodeWord u) []) =
      cfg none initial (encodeWord c) (encodeWord (shiftWith c u)) [] := by
  simpa [shiftLists_encodeWordWith] using
    run_lists (encodeWord c) (encodeWord u) (by simp)

/-- Literal uniform machine execution implements `wordShift`, keeping the
chosen modulus and clearing its scratch stack. Selection of that modulus is
not included in this component's transition count. -/
theorem run_wordShift {n : ℕ} (u : BinaryWord n) :
    run (2 * n + 2)
        (cfg (some .scan) initial (encodeWord (chosenWord n)) (encodeWord u) []) =
      cfg none initial (encodeWord (chosenWord n)) (encodeWord (wordShift n u)) [] := by
  simpa [shiftLists_encodeWord] using
    run_lists (encodeWord (chosenWord n)) (encodeWord u) (by simp)

end EthInapproximability.CurrentPaper.SamplerMachineShift
