import CurrentAdditive.DivisionBitStep

/-!
A literal one-stack TM2 scan for whether a fixed-width Boolean word is zero.
The result is held in one finite Boolean control register, and the input
word is consumed. It is suitable for testing the remainder after division.
-/

namespace CurrentAdditive.FieldMachineHelper.ZeroWordTest

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.FieldMachineHelper.DivisionBitStep (bitsBE)

inductive Label where
  | scan
  deriving DecidableEq, Fintype

abbrev Control := Bool × Option Bool
abbrev Config := TM2.Cfg (fun _ : Fin 1 => Bool) Label Control

def program : Label → TM2.Stmt (fun _ : Fin 1 => Bool) Label Control
  | .scan => pop 0 (fun s bit => (s.1 || bit.getD false, bit))
      (branch (fun s => s.2.isSome)
        (goto (fun _ => .scan)) halt)

def cfg (l : Option Label) (s : Control) (word : List Bool) : Config :=
  ⟨l, s, fun _ => word⟩

def run (t : Nat) (q : Config) : Config := ((advance program)^[t]) q

private theorem run_succ {c e : Config} (h : TM2.step program c = some e)
    (t : Nat) : run (t + 1) c = run t e := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem step_cons (seen : Bool) (prior : Option Bool)
    (bit : Bool) (rest : List Bool) :
    TM2.step program (cfg (some .scan) (seen, prior) (bit :: rest)) =
      some (cfg (some .scan) (seen || bit, some bit) rest) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k
  rfl

private theorem step_nil (seen : Bool) (prior : Option Bool) :
    TM2.step program (cfg (some .scan) (seen, prior) []) =
      some (cfg none (seen, none) []) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

theorem run_correct (seen : Bool) (prior : Option Bool) (word : List Bool) :
    run (word.length + 1) (cfg (some .scan) (seen, prior) word) =
      cfg none (seen || word.any id, none) [] := by
  induction word generalizing seen prior with
  | nil => simpa using run_succ (step_nil seen prior) 0
  | cons bit rest ih =>
    rw [List.length_cons, run_succ (step_cons seen prior bit rest)]
    simpa [Bool.or_assoc] using ih (seen || bit) (some bit)

theorem bitsBE_any_false_iff_zero (width value : Nat)
    (hsize : value < 2 ^ width) :
    (bitsBE width value).any id = false ↔ value = 0 := by
  constructor
  · intro hzero
    apply Nat.zero_of_testBit_eq_false
    intro j
    by_cases hj : j < width
    · have hm : value.testBit j ∈ bitsBE width value := by
        simp only [bitsBE, List.mem_reverse, List.mem_map]
        exact ⟨j, List.mem_range.mpr hj, rfl⟩
      exact Bool.eq_false_iff.mpr (List.any_eq_false.mp hzero _ hm)
    · have hp : 2 ^ width ≤ 2 ^ j :=
        Nat.pow_le_pow_right (by omega) (by omega)
      exact Nat.testBit_eq_false_of_lt (hsize.trans_le hp)
  · intro hzero
    subst value
    simp [bitsBE]

#print axioms run_correct
#print axioms bitsBE_any_false_iff_zero

end CurrentAdditive.FieldMachineHelper.ZeroWordTest
