import EthInapproximability.CurrentPaper.BitMachineBinaryMultiply
import EthInapproximability.CurrentPaper.BitMachineBinarySubtract
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding
import Mathlib.Tactic

/-!
Private physical implementation of the fixed-bit rounded draw in v38.
Bank 3 holds the public LSB-first alphabet size; bank 7 starts with one
LSB-first fresh block followed by an arbitrary unused suffix. Bank 6 holds
one public marker per bit. The program loads the block into the multiplier
in MSB order while copying its length into bank 8, invokes the actual binary
multiplication program on banks 0--5, then removes the low product bits using
bank 8. The returned bank 0 is LSB-first.
-/

namespace EthInapproximability.CurrentPaper.RoundedMachine

open Turing Turing.TM2.Stmt BitMachineEncoding
open BitMachineStackEmbedding
set_option maxRecDepth 16384
abbrev Stack := BitMachineBinaryMultiply.Stack ⊕ Fin 3

inductive Label where
  | load | multiply (l : BitMachineBinaryMultiply.Label) | handoff | shift
  deriving DecidableEq, Fintype

abbrev Control := BitMachineBinaryMultiply.Control × (Option Bool × Option Bool)
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def initial : Control := (BitMachineBinaryMultiply.initial, none, none)

def includeMul : BitMachineBinaryMultiply.Stack ↪ Stack :=
  ⟨Sum.inl, by intro x y h; exact Sum.inl_injective h⟩

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .load =>
      pop (.inr 0) (fun _ marker => (BitMachineBinaryMultiply.initial, marker, none))
        (branch (fun s => s.2.1.isSome)
          (pop (.inr 1) (fun s bit => (s.1, s.2.1, bit))
            (push (.inl (.inr 1)) (fun s => s.2.2.getD false)
              (push (.inr 2) (fun _ => true) (goto (fun _ => .load)))))
          (load (fun _ => initial) (goto (fun _ => .multiply (.inr (.inr ()))))))
  | .multiply l =>
      BitMachineStackEmbedding.stmt includeMul Label.multiply
        (fun v => (v, none, none)) Prod.fst (some .handoff) (BitMachineBinaryMultiply.program l)
  | .handoff => load (fun _ => initial) (goto (fun _ => .shift))
  | .shift =>
      pop (.inr 2) (fun _ marker => (BitMachineBinaryMultiply.initial, marker, none))
        (branch (fun s => s.2.1.isSome)
          (pop (.inl (.inl 0)) (fun s _ => s) (goto (fun _ => .shift)))
          (load (fun _ => initial) halt))

def rightBank (count tape shift : List Bool) : Fin 3 → List Bool :=
  fun i => if i = 0 then count else if i = 1 then tape else shift

def bank (left : BitMachineBinaryMultiply.Stack → List Bool) (count tape shift : List Bool) :
    Stack → List Bool := Sum.elim left (rightBank count tape shift)

def cfg (l : Option Label) (s : Control) (left : BitMachineBinaryMultiply.Stack → List Bool)
    (count tape shift : List Bool) : Config :=
  ⟨l, s, bank left count tape shift⟩

def mulStart (source multiplier : List Bool) : BitMachineBinaryMultiply.Stack → List Bool :=
  (BitMachineBinaryMultiply.cfg (some (.inr (.inr ()))) BitMachineBinaryMultiply.initial [] [] [] source multiplier []).stk

def mulFinish (source multiplier : List Bool) : BitMachineBinaryMultiply.Stack → List Bool :=
  (BitMachineBinaryMultiply.cfg none BitMachineBinaryMultiply.initial (BitMachineBinaryMultiply.multiplyFrom [] source multiplier) [] [] source [] []).stk

def run (n : ℕ) (c : Config) : Config := ((advance program)^[n]) c

private theorem run_succ (n : ℕ) (c : Config) :
    run (n + 1) c = run n (advance program c) := by
  simp only [run, Function.iterate_succ_apply]

private theorem step_load_cons (source multiplier shift tail : List Bool)
    (bit : Bool) (count : List Bool) (s : Control) :
    advance program (cfg (some .load) s (mulStart source multiplier)
      (true :: count) (bit :: tail) shift) =
    cfg (some .load) (BitMachineBinaryMultiply.initial, some true, some bit)
      (mulStart source (bit :: multiplier)) count tail (true :: shift) := by
  simp only [advance, TM2.step, TM2.stepAux, program, cfg]
  simp only [bank, rightBank, Sum.elim_inr, ↓reduceIte,
    List.head?_cons, List.tail_cons, Option.isSome_some, cond_true,
    Option.getD_some]
  congr 1
  funext k
  rcases k with k | k
  · rcases k with k | k <;> fin_cases k <;>
      simp [Function.update, rightBank, mulStart, BitMachineBinaryMultiply.cfg,
        BitMachineBinaryMultiply.rightBank]
  · fin_cases k <;> simp [Function.update, rightBank]

private theorem step_load_nil (source multiplier shift tape : List Bool)
    (s : Control) :
    advance program (cfg (some .load) s (mulStart source multiplier)
      [] tape shift) =
    cfg (some (.multiply (.inr (.inr ())))) initial
      (mulStart source multiplier) [] tape shift := by
  simp only [advance, TM2.step, TM2.stepAux, program, cfg]
  simp only [bank, rightBank, Sum.elim_inr, ↓reduceIte,
    List.head?_nil, List.tail_nil, Option.isSome_none, cond_false]
  simp only [Option.getD_some]
  congr 1
  funext k
  rcases k with k | k
  · simp
  · fin_cases k <;> simp [rightBank]

theorem load_run (source multiplier shift word suffix : List Bool)
    (s : Control) :
    run (word.length + 1)
      (cfg (some .load) s (mulStart source multiplier)
        (List.replicate word.length true) (word ++ suffix) shift) =
    cfg (some (.multiply (.inr (.inr ())))) initial
      (mulStart source (word.reverse ++ multiplier))
      [] suffix (List.replicate word.length true ++ shift) := by
  induction word generalizing multiplier shift s with
  | nil => simpa [run] using step_load_nil source multiplier shift suffix s
  | cons bit tail ih =>
      have hrep : ∀ n : ℕ, List.replicate n true ++ true :: shift =
          true :: (List.replicate n true ++ shift) := by
        intro n
        induction n with
        | zero => rfl
        | succ n hn => simpa [List.replicate_succ, List.cons_append] using hn
      simp only [List.length_cons, List.cons_append]
      rw [List.replicate_succ]
      rw [run_succ]
      rw [step_load_cons]
      simp only [List.cons_append]
      rw [← hrep]
      simpa [List.reverse_cons, List.append_assoc] using
        ih (bit :: multiplier) (true :: shift) (BitMachineBinaryMultiply.initial, some true, some bit)

private theorem embedded_bank (before after : BitMachineBinaryMultiply.Stack → List Bool)
    (count tape shift : List Bool) :
    BitMachineStackEmbedding.bank includeMul (bank before count tape shift) after =
      bank after count tape shift := by
  funext k
  rcases k with k | k
  · exact BitMachineStackEmbedding.bank_at includeMul
      (bank before count tape shift) after k
  · have h : ¬ ∃ j : BitMachineBinaryMultiply.Stack, includeMul j = Sum.inr k := by
      intro ⟨j, hj⟩
      cases hj
    rw [BitMachineStackEmbedding.bank_outside includeMul
      (bank before count tape shift) after (.inr k) h]
    rfl

theorem multiplication_run (source multiplier suffix markers : List Bool) :
    ∃ n ≤ (multiplier.length + 1) *
        (4 * (source.length + 2 * multiplier.length) + 7),
      run n (cfg (some (.multiply (.inr (.inr ())))) initial
        (mulStart source multiplier) [] suffix markers) =
      cfg (some .handoff) initial (mulFinish source multiplier) [] suffix markers := by
  obtain ⟨n, hn, hr⟩ := BitMachineBinaryMultiply.standard_run source multiplier
  let localStart := BitMachineBinaryMultiply.cfg
    (some (.inr (.inr ()))) BitMachineBinaryMultiply.initial
    [] [] [] source multiplier []
  let foreign := bank (mulStart source multiplier) [] suffix markers
  have hhalt : (((advance BitMachineBinaryMultiply.program)^[n]) localStart).l = none := by
    change (BitMachineBinaryMultiply.run n localStart).l = none
    rw [hr]
    rfl
  obtain ⟨t, ht, hrun⟩ := BitMachineStackEmbedding.outputs includeMul foreign
    Label.multiply (fun v => (v, none, none)) Prod.fst (by intro v; rfl)
    (some .handoff) BitMachineBinaryMultiply.program program (by intro l; rfl)
    localStart n hhalt
  refine ⟨t, ht.trans hn, ?_⟩
  change (((advance program)^[t])
    (BitMachineStackEmbedding.cfg includeMul foreign Label.multiply
      (fun v => (v, none, none)) (some .handoff) localStart)) = _ at hrun
  change (((advance BitMachineBinaryMultiply.program)^[n]) localStart) = _ at hr
  rw [hr] at hrun
  simpa [run, BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg, localStart, foreign, mulStart, mulFinish,
    embedded_bank, cfg] using hrun

def productBank (source product : List Bool) : BitMachineBinaryMultiply.Stack → List Bool :=
  (BitMachineBinaryMultiply.cfg none BitMachineBinaryMultiply.initial
    product [] [] source [] []).stk

private theorem step_handoff (source product suffix markers : List Bool) :
    advance program (cfg (some .handoff) initial (productBank source product)
      [] suffix markers) =
    cfg (some .shift) initial (productBank source product) [] suffix markers := by
  rfl

private theorem step_shift_cons (source product suffix : List Bool)
    (bit : Bool) (markers : List Bool) (s : Control) :
    advance program (cfg (some .shift) s (productBank source product)
      [] suffix (bit :: markers)) =
    cfg (some .shift) (BitMachineBinaryMultiply.initial, some bit, none)
      (productBank source product.tail) [] suffix markers := by
  simp only [advance, TM2.step, TM2.stepAux, program, cfg]
  have hread : rightBank [] suffix (bit :: markers) 2 = bit :: markers := rfl
  simp only [bank, Sum.elim_inr, hread,
    List.head?_cons, List.tail_cons, Option.isSome_some, cond_true,
    Option.getD_some]
  congr 1
  funext k
  rcases k with k | k
  · rcases k with k | k <;> fin_cases k <;>
      simp [Function.update, productBank, BitMachineBinaryMultiply.cfg,
        BitMachineBinaryMultiply.rightBank, BitMachineBinaryAddAny.bank,
        BitMachineBinaryAdd.bank]
  · fin_cases k <;> simp [Function.update, rightBank]

private theorem step_shift_nil (source product suffix : List Bool) (s : Control) :
    advance program (cfg (some .shift) s (productBank source product)
      [] suffix []) =
    cfg none initial (productBank source product) [] suffix [] := by
  simp only [advance, TM2.step, TM2.stepAux, program, cfg]
  have hread : rightBank [] suffix [] 2 = [] := rfl
  simp only [bank, Sum.elim_inr, hread,
    List.head?_nil, List.tail_nil, Option.isSome_none, cond_false,
    Option.getD_some]
  congr 1
  funext k
  rcases k with k | k
  · rfl
  · fin_cases k <;> simp [rightBank]

theorem shift_run (source product suffix markers : List Bool) (s : Control) :
    run (markers.length + 1)
      (cfg (some .shift) s (productBank source product) [] suffix markers) =
    cfg none initial (productBank source (product.drop markers.length)) [] suffix [] := by
  induction markers generalizing product s with
  | nil => simpa [run] using step_shift_nil source product suffix s
  | cons bit markers ih =>
      simp only [List.length_cons]
      rw [run_succ, step_shift_cons]
      have h := ih product.tail (BitMachineBinaryMultiply.initial, some bit, none)
      cases product <;> simpa [List.drop_succ_cons] using h

private theorem run_add {c d : Config} {m : ℕ} (h : run m c = d) (n : ℕ) :
    run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

def outputWord (source word : List Bool) : List Bool :=
  (BitMachineBinaryMultiply.multiplyFrom [] source word.reverse).drop word.length

def clock (source word : List Bool) : ℕ :=
  (word.length + 1) +
    ((word.length + 1) * (4 * (source.length + 2 * word.length) + 7)) +
    1 + (word.length + 1)

theorem clock_quadratic (source word : List Bool) :
    clock source word ≤ 100 * (source.length + word.length + 2) ^ 2 := by
  unfold clock
  nlinarith [Nat.zero_le (source.length * word.length),
    Nat.zero_le (source.length * source.length),
    Nat.zero_le (word.length * word.length)]

/-- One finite table executes every stage. It reads exactly `word.length` cells
from bank 7, leaves `suffix` unchanged there, and returns the LSB-first
zero-based rounded index in bank 0. The initial counter is public and the
number of transitions is quadratic in the charged input lengths. -/
theorem physical_run (source word suffix : List Bool) :
    ∃ t ≤ clock source word,
      run t (cfg (some .load) initial (mulStart source [])
        (List.replicate word.length true) (word ++ suffix) []) =
      cfg none initial (productBank source (outputWord source word)) [] suffix [] := by
  let product := BitMachineBinaryMultiply.multiplyFrom [] source word.reverse
  have hload := load_run source [] [] word suffix initial
  simp only [List.append_nil] at hload
  obtain ⟨tm, htm, hmul⟩ := multiplication_run source word.reverse suffix
    (List.replicate word.length true)
  simp only [List.length_reverse] at htm
  have hhandoff := step_handoff source product suffix
    (List.replicate word.length true)
  have hshift := shift_run source product suffix
    (List.replicate word.length true) initial
  simp only [List.length_replicate] at hshift
  have hmul' : run tm
      (cfg (some (.multiply (.inr (.inr ())))) initial
        (mulStart source word.reverse) [] suffix (List.replicate word.length true)) =
      cfg (some .handoff) initial (productBank source product)
        [] suffix (List.replicate word.length true) := by
    simpa [mulFinish, productBank, product] using hmul
  have h01 := run_add hload tm
  rw [hmul'] at h01
  have h02 := run_add h01 1
  simp only [run, Function.iterate_one] at h02
  rw [hhandoff] at h02
  have h03 := run_add h02 (word.length + 1)
  rw [hshift] at h03
  refine ⟨(word.length + 1) + tm + 1 + (word.length + 1), ?_, ?_⟩
  · unfold clock
    omega
  · simpa [outputWord, product, Nat.add_assoc] using h03

theorem msbValue_reverse (bits : List Bool) :
    BitMachineBinaryMultiply.msbValue bits.reverse =
      EncodedCommunication.bitsValue bits := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
      simp only [List.reverse_cons, BitMachineBinaryMultiply.msbValue,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        EncodedCommunication.bitsValue]
      rw [← BitMachineBinaryMultiply.msbValue, ih]

private theorem bitsValue_cons (a : Bool) (as : List Bool) :
    EncodedCommunication.bitsValue (a :: as) =
      2 * EncodedCommunication.bitsValue as + a.toNat := by
  simp [EncodedCommunication.bitsValue, Nat.bit_val]

theorem bitsValue_drop : ∀ (j : ℕ) (L : List Bool),
    EncodedCommunication.bitsValue (L.drop j) =
      EncodedCommunication.bitsValue L / 2 ^ j
  | 0, L => by simp
  | j + 1, [] => by simp [EncodedCommunication.bitsValue]
  | j + 1, a :: L => by
    rw [List.drop_succ_cons, bitsValue_drop j L, bitsValue_cons,
      pow_succ, Nat.mul_comm (2 ^ j) 2, ← Nat.div_div_eq_div_mul]
    congr 1
    cases a <;> simp <;> omega

theorem output_value (source word : List Bool) :
    EncodedCommunication.bitsValue (outputWord source word) =
      EncodedCommunication.bitsValue source *
        EncodedCommunication.bitsValue word / 2 ^ word.length := by
  rw [outputWord, bitsValue_drop,
    BitMachineBinaryMultiply.standard_value, msbValue_reverse]

theorem output_legal (source word : List Bool)
    (ha : 0 < EncodedCommunication.bitsValue source) :
    EncodedCommunication.bitsValue (outputWord source word) <
      EncodedCommunication.bitsValue source := by
  let a := EncodedCommunication.bitsValue source
  let u := EncodedCommunication.bitsValue word
  let M := 2 ^ word.length
  have hM : 0 < M := by positivity
  have hu : u < M := BitMachineBinarySubtract.bitsValue_lt_pow word
  have hmul : a * u < a * M := Nat.mul_lt_mul_of_pos_left hu ha
  rw [output_value]
  exact (Nat.div_lt_iff_lt_mul hM).2 (by simpa [Nat.mul_comm] using hmul)

end EthInapproximability.CurrentPaper.RoundedMachine
