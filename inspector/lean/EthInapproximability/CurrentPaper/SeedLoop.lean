import EthInapproximability.CurrentPaper.BitMachineEncoding

/-!
# The level-0 matrix word: a counting loop (generic cells)

Lane owner:b-stage4-entry-program-6 (Paper B, unit 2, map item 3).

ONE fixed program `program C T O` on an arbitrary bank with three distinct cells:
counter `C` (least significant bit on top), temporary `T`, output `O`.
From `C = bitsLE w x`, `T = []` it pushes, for `y = x, x-1, …, 0`, the row
`(bitsLE w y).reverse` onto `O` (emit + restore + decrement per row), then clears.
Final bank: `C = T = []`, `O = rows w x ++ O₀` (`loop_run`), in at most
`(x + 1) * (4 * w + 4)` steps. Every cell other than `C, T, O` is untouched.
-/

namespace EthInapproximability.CurrentPaper.SeedLoop

open Turing BitMachineEncoding

variable {K : Type*} [DecidableEq K]

inductive Lab where
  | emit | restore | dec | back | clr
  deriving DecidableEq

/-- The fixed counting program. -/
def program (C T O : K) : Lab → TM2.Stmt (fun _ : K => Bool) Lab (Option Bool)
  | .emit => .pop C (fun _ b => b) (.branch (fun v => v.isSome)
      (.push O (fun v => v.getD false) (.push T (fun v => v.getD false) (.goto fun _ => .emit)))
      (.goto fun _ => .restore))
  | .restore => .pop T (fun _ b => b) (.branch (fun v => v.isSome)
      (.push C (fun v => v.getD false) (.goto fun _ => .restore))
      (.goto fun _ => .dec))
  | .dec => .pop C (fun _ b => b) (.branch (fun v => v.isSome)
      (.branch (fun v => v.getD false)
        (.push C (fun _ => false) (.goto fun _ => .back))
        (.push T (fun _ => true) (.goto fun _ => .dec)))
      (.goto fun _ => .clr))
  | .back => .pop T (fun _ b => b) (.branch (fun v => v.isSome)
      (.push C (fun v => v.getD false) (.goto fun _ => .back))
      (.goto fun _ => .emit))
  | .clr => .pop T (fun _ b => b) (.branch (fun v => v.isSome)
      (.goto fun _ => .clr) .halt)

/-- Little-endian bits of `x`, `w` of them. -/
def bitsLE : ℕ → ℕ → List Bool
  | 0, _ => []
  | w + 1, x => decide (x % 2 = 1) :: bitsLE w (x / 2)

/-- The bank with the three cells set. -/
def upd3 (C T O : K) (S : K → List Bool) (c t o : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update S C c) T t) O o

variable (C T O : K)

abbrev Cfg := TM2.Cfg (fun _ : K => Bool) Lab (Option Bool)

section
variable {C T O} (hCT : C ≠ T) (hCO : C ≠ O) (hTO : T ≠ O)
include hCT hCO hTO

theorem upd3_C (S : K → List Bool) (c t o : List Bool) : upd3 C T O S c t o C = c := by
  simp [upd3, Function.update_apply, hCT, hCO]

theorem upd3_T (S : K → List Bool) (c t o : List Bool) : upd3 C T O S c t o T = t := by
  simp [upd3, Function.update_apply, hTO]

theorem upd3_O (S : K → List Bool) (c t o : List Bool) : upd3 C T O S c t o O = o := by
  simp [upd3, Function.update_apply]

theorem upd3_setC (S : K → List Bool) (c t o c' : List Bool) :
    Function.update (upd3 C T O S c t o) C c' = upd3 C T O S c' t o := by
  funext k
  by_cases h1 : k = C
  · subst h1; simp [upd3, Function.update_apply, hCT, hCO]
  · simp [upd3, Function.update_apply, h1]

theorem upd3_setT (S : K → List Bool) (c t o t' : List Bool) :
    Function.update (upd3 C T O S c t o) T t' = upd3 C T O S c t' o := by
  funext k
  by_cases h1 : k = T
  · subst h1; simp [upd3, Function.update_apply, hCT, hTO, Ne.symm hCT]
  · simp [upd3, Function.update_apply, h1]

theorem upd3_setO (S : K → List Bool) (c t o o' : List Bool) :
    Function.update (upd3 C T O S c t o) O o' = upd3 C T O S c t o' := by
  funext k
  by_cases h1 : k = O
  · subst h1; simp [upd3, Function.update_apply]
  · simp [upd3, Function.update_apply, h1]

/-! ## One-step lemmas -/

theorem step_emit_cons (S : K → List Bool) (v : Option Bool) (b : Bool) (c t o : List Bool) :
    advance (program C T O) (⟨some .emit, v, upd3 C T O S (b :: c) t o⟩ : Cfg) =
      ⟨some .emit, some b, upd3 C T O S c (b :: t) (b :: o)⟩ := by
  simp only [advance, TM2.step, program, TM2.stepAux, Option.getD_some, Option.isSome_some,
    cond_true, upd3_C hCT hCO hTO, List.head?_cons, List.tail_cons]
  rw [upd3_setC hCT hCO hTO, upd3_O hCT hCO hTO, upd3_setO hCT hCO hTO,
    upd3_T hCT hCO hTO, upd3_setT hCT hCO hTO]

theorem step_emit_nil (S : K → List Bool) (v : Option Bool) (t o : List Bool) :
    advance (program C T O) (⟨some .emit, v, upd3 C T O S [] t o⟩ : Cfg) =
      ⟨some .restore, none, upd3 C T O S [] t o⟩ := by
  simp only [advance, TM2.step, program, TM2.stepAux, Option.getD_some, Option.isSome_none,
    cond_false, upd3_C hCT hCO hTO, List.head?_nil, List.tail_nil]
  rw [upd3_setC hCT hCO hTO]

theorem step_restore_cons (S : K → List Bool) (v : Option Bool) (b : Bool) (c t o : List Bool) :
    advance (program C T O) (⟨some .restore, v, upd3 C T O S c (b :: t) o⟩ : Cfg) =
      ⟨some .restore, some b, upd3 C T O S (b :: c) t o⟩ := by
  simp only [advance, TM2.step, program, TM2.stepAux, Option.getD_some, Option.isSome_some,
    cond_true, upd3_T hCT hCO hTO, List.head?_cons, List.tail_cons]
  rw [upd3_setT hCT hCO hTO, upd3_C hCT hCO hTO, upd3_setC hCT hCO hTO]

theorem step_restore_nil (S : K → List Bool) (v : Option Bool) (c o : List Bool) :
    advance (program C T O) (⟨some .restore, v, upd3 C T O S c [] o⟩ : Cfg) =
      ⟨some .dec, none, upd3 C T O S c [] o⟩ := by
  simp only [advance, TM2.step, program, TM2.stepAux, Option.getD_some, Option.isSome_none,
    cond_false, upd3_T hCT hCO hTO, List.head?_nil, List.tail_nil]
  rw [upd3_setT hCT hCO hTO]

theorem step_dec_true (S : K → List Bool) (v : Option Bool) (c t o : List Bool) :
    advance (program C T O) (⟨some .dec, v, upd3 C T O S (true :: c) t o⟩ : Cfg) =
      ⟨some .back, some true, upd3 C T O S (false :: c) t o⟩ := by
  simp only [advance, TM2.step, program, TM2.stepAux, Option.getD_some, Option.isSome_some,
    cond_true, upd3_C hCT hCO hTO, List.head?_cons, List.tail_cons]
  rw [upd3_setC hCT hCO hTO, upd3_C hCT hCO hTO, upd3_setC hCT hCO hTO]

theorem step_dec_false (S : K → List Bool) (v : Option Bool) (c t o : List Bool) :
    advance (program C T O) (⟨some .dec, v, upd3 C T O S (false :: c) t o⟩ : Cfg) =
      ⟨some .dec, some false, upd3 C T O S c (true :: t) o⟩ := by
  simp only [advance, TM2.step, program, TM2.stepAux, Option.getD_some, Option.isSome_some,
    cond_true, cond_false, upd3_C hCT hCO hTO, List.head?_cons, List.tail_cons]
  rw [upd3_setC hCT hCO hTO, upd3_T hCT hCO hTO, upd3_setT hCT hCO hTO]

theorem step_dec_nil (S : K → List Bool) (v : Option Bool) (t o : List Bool) :
    advance (program C T O) (⟨some .dec, v, upd3 C T O S [] t o⟩ : Cfg) =
      ⟨some .clr, none, upd3 C T O S [] t o⟩ := by
  simp only [advance, TM2.step, program, TM2.stepAux, Option.getD_some, Option.isSome_none,
    cond_false, upd3_C hCT hCO hTO, List.head?_nil, List.tail_nil]
  rw [upd3_setC hCT hCO hTO]

theorem step_back_cons (S : K → List Bool) (v : Option Bool) (b : Bool) (c t o : List Bool) :
    advance (program C T O) (⟨some .back, v, upd3 C T O S c (b :: t) o⟩ : Cfg) =
      ⟨some .back, some b, upd3 C T O S (b :: c) t o⟩ := by
  simp only [advance, TM2.step, program, TM2.stepAux, Option.getD_some, Option.isSome_some,
    cond_true, upd3_T hCT hCO hTO, List.head?_cons, List.tail_cons]
  rw [upd3_setT hCT hCO hTO, upd3_C hCT hCO hTO, upd3_setC hCT hCO hTO]

theorem step_back_nil (S : K → List Bool) (v : Option Bool) (c o : List Bool) :
    advance (program C T O) (⟨some .back, v, upd3 C T O S c [] o⟩ : Cfg) =
      ⟨some .emit, none, upd3 C T O S c [] o⟩ := by
  simp only [advance, TM2.step, program, TM2.stepAux, Option.getD_some, Option.isSome_none,
    cond_false, upd3_T hCT hCO hTO, List.head?_nil, List.tail_nil]
  rw [upd3_setT hCT hCO hTO]

theorem step_clr_cons (S : K → List Bool) (v : Option Bool) (b : Bool) (c t o : List Bool) :
    advance (program C T O) (⟨some .clr, v, upd3 C T O S c (b :: t) o⟩ : Cfg) =
      ⟨some .clr, some b, upd3 C T O S c t o⟩ := by
  simp only [advance, TM2.step, program, TM2.stepAux, Option.getD_some, Option.isSome_some,
    cond_true, upd3_T hCT hCO hTO, List.head?_cons, List.tail_cons]
  rw [upd3_setT hCT hCO hTO]

theorem step_clr_nil (S : K → List Bool) (v : Option Bool) (c o : List Bool) :
    advance (program C T O) (⟨some .clr, v, upd3 C T O S c [] o⟩ : Cfg) =
      ⟨none, none, upd3 C T O S c [] o⟩ := by
  simp only [advance, TM2.step, program, TM2.stepAux, Option.getD_some, Option.isSome_none,
    cond_false, upd3_T hCT hCO hTO, List.head?_nil, List.tail_nil]
  rw [upd3_setT hCT hCO hTO]

end

/-! ## Bits -/

theorem bitsLE_length (w x : ℕ) : (bitsLE w x).length = w := by
  induction w generalizing x with
  | zero => rfl
  | succ w ih => simp [bitsLE, ih]

theorem bitsLE_zero (w : ℕ) : bitsLE w 0 = List.replicate w false := by
  induction w with
  | zero => rfl
  | succ w ih => simp [bitsLE, ih, List.replicate_succ]

/-- The rows pushed for `y = 0, …, x` (row `y` is `(bitsLE w y).reverse`). -/
def rows (w x : ℕ) : List Bool :=
  (List.ofFn (fun y : Fin (x + 1) => (bitsLE w y.val).reverse)).flatten

theorem rows_zero (w : ℕ) : rows w 0 = (bitsLE w 0).reverse := by
  simp [rows]

theorem rows_succ (w x : ℕ) : rows w (x + 1) = rows w x ++ (bitsLE w (x + 1)).reverse := by
  unfold rows
  rw [List.ofFn_succ', List.concat_eq_append, List.flatten_append]
  simp

section
variable {C T O} (hCT : C ≠ T) (hCO : C ≠ O) (hTO : T ≠ O)
include hCT hCO hTO

/-! ## Phase runs -/

theorem emit_run (S : K → List Bool) (v : Option Bool) (c t o : List Bool) :
    ((advance (program C T O))^[c.length + 1]) (⟨some .emit, v, upd3 C T O S c t o⟩ : Cfg) =
      ⟨some .restore, none, upd3 C T O S [] (c.reverse ++ t) (c.reverse ++ o)⟩ := by
  induction c generalizing v t o with
  | nil => simpa using step_emit_nil hCT hCO hTO S v t o
  | cons b c ih =>
      rw [List.length_cons, Function.iterate_succ_apply, step_emit_cons hCT hCO hTO, ih]
      simp

theorem restore_run (S : K → List Bool) (v : Option Bool) (c t o : List Bool) :
    ((advance (program C T O))^[t.length + 1]) (⟨some .restore, v, upd3 C T O S c t o⟩ : Cfg) =
      ⟨some .dec, none, upd3 C T O S (t.reverse ++ c) [] o⟩ := by
  induction t generalizing v c with
  | nil => simpa using step_restore_nil hCT hCO hTO S v c o
  | cons b t ih =>
      rw [List.length_cons, Function.iterate_succ_apply, step_restore_cons hCT hCO hTO, ih]
      simp

theorem back_run (S : K → List Bool) (v : Option Bool) (c t o : List Bool) :
    ((advance (program C T O))^[t.length + 1]) (⟨some .back, v, upd3 C T O S c t o⟩ : Cfg) =
      ⟨some .emit, none, upd3 C T O S (t.reverse ++ c) [] o⟩ := by
  induction t generalizing v c with
  | nil => simpa using step_back_nil hCT hCO hTO S v c o
  | cons b t ih =>
      rw [List.length_cons, Function.iterate_succ_apply, step_back_cons hCT hCO hTO, ih]
      simp

theorem clr_run (S : K → List Bool) (v : Option Bool) (c t o : List Bool) :
    ((advance (program C T O))^[t.length + 1]) (⟨some .clr, v, upd3 C T O S c t o⟩ : Cfg) =
      ⟨none, none, upd3 C T O S c [] o⟩ := by
  induction t generalizing v with
  | nil => simpa using step_clr_nil hCT hCO hTO S v c o
  | cons b t ih =>
      rw [List.length_cons, Function.iterate_succ_apply, step_clr_cons hCT hCO hTO, ih]

theorem dec_zero_run (S : K → List Bool) (v : Option Bool) (w : ℕ) (t o : List Bool) :
    ((advance (program C T O))^[w + 1])
        (⟨some .dec, v, upd3 C T O S (List.replicate w false) t o⟩ : Cfg) =
      ⟨some .clr, none, upd3 C T O S [] (List.replicate w true ++ t) o⟩ := by
  induction w generalizing v t with
  | zero => simpa using step_dec_nil hCT hCO hTO S v t o
  | succ w ih =>
      rw [Function.iterate_succ_apply, List.replicate_succ, step_dec_false hCT hCO hTO, ih]
      simp [List.replicate_succ']

theorem dec_run (w : ℕ) : ∀ (x : ℕ), 0 < x → x < 2 ^ w → ∀ (j : ℕ) (S : K → List Bool)
    (v : Option Bool) (o : List Bool),
    ∃ t ≤ 2 * w + j + 2,
      ((advance (program C T O))^[t])
          (⟨some .dec, v, upd3 C T O S (bitsLE w x) (List.replicate j true) o⟩ : Cfg) =
        ⟨some .emit, none, upd3 C T O S (List.replicate j true ++ bitsLE w (x - 1)) [] o⟩ := by
  induction w with
  | zero => intro x h0 h1; simp at h1; omega
  | succ w ih =>
      intro x h0 h1 j S v o
      rcases Nat.mod_two_eq_zero_or_one x with hx | hx
      · have hx2 : 0 < x / 2 := by omega
        have hx3 : x / 2 < 2 ^ w := by rw [pow_succ] at h1; omega
        obtain ⟨t, ht, hr⟩ := ih (x / 2) hx2 hx3 (j + 1) S (some false) o
        refine ⟨t + 1, by omega, ?_⟩
        have hb : bitsLE (w + 1) x = false :: bitsLE w (x / 2) := by simp [bitsLE, hx]
        have hb' : bitsLE (w + 1) (x - 1) = true :: bitsLE w (x / 2 - 1) := by
          have h1' : (x - 1) % 2 = 1 := by omega
          have h2' : (x - 1) / 2 = x / 2 - 1 := by omega
          simp [bitsLE, h1', h2']
        rw [Function.iterate_succ_apply, hb, step_dec_false hCT hCO hTO,
          show true :: List.replicate j true = List.replicate (j + 1) true from rfl, hr, hb',
          List.replicate_succ', List.append_assoc]
        rfl
      · refine ⟨(j + 1) + 1, by omega, ?_⟩
        have hb : bitsLE (w + 1) x = true :: bitsLE w (x / 2) := by simp [bitsLE, hx]
        have hb' : bitsLE (w + 1) (x - 1) = false :: bitsLE w (x / 2) := by
          have h1' : (x - 1) % 2 = 0 := by omega
          have h2' : (x - 1) / 2 = x / 2 := by omega
          simp [bitsLE, h1', h2']
        rw [Function.iterate_add_apply, Function.iterate_one, hb, step_dec_true hCT hCO hTO,
          show j + 1 = (List.replicate j true).length + 1 by simp, back_run hCT hCO hTO, hb',
          List.reverse_replicate]

/-! ## The loop -/

theorem loop_run (w : ℕ) : ∀ (x : ℕ), x < 2 ^ w → ∀ (S : K → List Bool) (v : Option Bool)
    (o : List Bool),
    ∃ t ≤ (x + 1) * (4 * w + 4),
      ((advance (program C T O))^[t])
          (⟨some .emit, v, upd3 C T O S (bitsLE w x) [] o⟩ : Cfg) =
        ⟨none, none, upd3 C T O S [] [] (rows w x ++ o)⟩ := by
  intro x
  induction x with
  | zero =>
      intro _ S v o
      refine ⟨((List.replicate w true).length + 1) + ((w + 1) +
        (((bitsLE w 0).reverse.length + 1) + ((bitsLE w 0).length + 1))), ?_, ?_⟩
      · simp [bitsLE_length]; omega
      · rw [Function.iterate_add_apply _ ((List.replicate w true).length + 1),
          Function.iterate_add_apply _ (w + 1),
          Function.iterate_add_apply _ ((bitsLE w 0).reverse.length + 1),
          emit_run hCT hCO hTO, List.append_nil, restore_run hCT hCO hTO, List.append_nil,
          List.reverse_reverse, bitsLE_zero, dec_zero_run hCT hCO hTO, List.append_nil,
          clr_run hCT hCO hTO, rows_zero, bitsLE_zero]
  | succ x ih =>
      intro hx S v o
      obtain ⟨td, htd, hd⟩ := dec_run hCT hCO hTO w (x + 1) (by omega) hx 0 S none
        ((bitsLE w (x + 1)).reverse ++ o)
      obtain ⟨ti, hti, hi⟩ := ih (by omega) S none ((bitsLE w (x + 1)).reverse ++ o)
      refine ⟨ti + (td + (((bitsLE w (x + 1)).reverse.length + 1) +
        ((bitsLE w (x + 1)).length + 1))), ?_, ?_⟩
      · simp only [List.length_reverse, bitsLE_length]
        have : (x + 1 + 1) * (4 * w + 4) = (x + 1) * (4 * w + 4) + (4 * w + 4) := by ring
        omega
      · rw [Function.iterate_add_apply _ ti, Function.iterate_add_apply _ td,
          Function.iterate_add_apply _ ((bitsLE w (x + 1)).reverse.length + 1),
          emit_run hCT hCO hTO, List.append_nil, restore_run hCT hCO hTO, List.append_nil,
          List.reverse_reverse]
        simp only [List.replicate_zero, List.nil_append] at hd
        rw [hd]
        simp only [Nat.add_sub_cancel]
        rw [hi, rows_succ, List.append_assoc]

end

end EthInapproximability.CurrentPaper.SeedLoop
