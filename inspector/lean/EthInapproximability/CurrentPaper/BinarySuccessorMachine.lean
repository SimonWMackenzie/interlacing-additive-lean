import EthInapproximability.CurrentPaper.BitMachineEncoding
import EthInapproximability.CurrentPaper.EncodedCommunication

/-!
# Variable-width binary successor for clock inputs

Source: frozen v8 `05-iteration.tex`, sequential bounded cutoff inputs
`1,...,n`. The carry loop stores only one bit in finite control and grows
the physical binary word by one bit precisely when necessary. Unlike the
sampler's fixed-width increment, it does not wrap around.
-/

namespace EthInapproximability.CurrentPaper.BinarySuccessorMachine

open Turing Turing.TM2.Stmt BitMachineEncoding

def successor : List Bool → List Bool
  | [] => [true]
  | false :: q => true :: q
  | true :: q => false :: successor q

def carryCount : List Bool → ℕ
  | [] => 0
  | false :: _ => 0
  | true :: q => carryCount q + 1

theorem carryCount_le_length (q : List Bool) : carryCount q ≤ q.length := by
  induction q with
  | nil => rfl
  | cons b q ih => cases b <;> simp [carryCount, ih]

theorem successor_value (q : List Bool) :
    EncodedCommunication.bitsValue (successor q) = EncodedCommunication.bitsValue q + 1 := by
  induction q with
  | nil => rfl
  | cons b q ih =>
      cases b <;> simp only [successor, EncodedCommunication.bitsValue, Nat.bit_val,
        Bool.toNat_false, Bool.toNat_true, ih] <;> omega

theorem successor_bits (n : ℕ) : successor n.bits = (n + 1).bits := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n h ih =>
      rw [Nat.bits_append_bit n b h]
      cases b with
      | false =>
          have he : Nat.bit false n + 1 = Nat.bit true n := by simp [Nat.bit_val]
          rw [successor, he, Nat.bits_append_bit n true (by simp)]
      | true =>
          have he : Nat.bit true n + 1 = Nat.bit false (n + 1) := by
            simp only [Nat.bit_val, Bool.toNat_false, Bool.toNat_true]
            omega
          rw [successor, ih, he, Nat.bits_append_bit (n + 1) false (by simp)]

inductive Label where
  | carry | restore
  deriving DecidableEq, Fintype

def program : Label → TM2.Stmt (fun _ : Fin 2 => Bool) Label (Option Bool)
  | .carry => pop 0 (fun _ b => b)
      (branch Option.isSome
        (branch (fun b => b.getD false)
          (push 1 (fun _ => false) (goto (fun _ => .carry)))
          (push 0 (fun _ => true) (goto (fun _ => .restore))))
        (push 0 (fun _ => true) (goto (fun _ => .restore))))
  | .restore => pop 1 (fun _ b => b)
      (branch Option.isSome
        (push 0 (fun b => b.getD false) (goto (fun _ => .restore)))
        (load (fun _ => none) halt))

def cfg (l : Option Label) (s : Option Bool) (q saved : List Bool) :
    TM2.Cfg (fun _ : Fin 2 => Bool) Label (Option Bool) :=
  ⟨l, s, fun k => if k = 0 then q else saved⟩

def run (n : ℕ) (c : TM2.Cfg (fun _ : Fin 2 => Bool) Label (Option Bool)) :=
  ((advance program)^[n]) c

private theorem run_succ {c d : TM2.Cfg (fun _ : Fin 2 => Bool) Label (Option Bool)}
    (h : TM2.step program c = some d) (n : ℕ) : run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem step_carry_true (s : Option Bool) (q saved : List Bool) :
    TM2.step program (cfg (some .carry) s (true :: q) saved) =
      some (cfg (some .carry) (some true) q (false :: saved)) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

private theorem step_carry_false (s : Option Bool) (q saved : List Bool) :
    TM2.step program (cfg (some .carry) s (false :: q) saved) =
      some (cfg (some .restore) (some false) (true :: q) saved) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

private theorem step_carry_nil (s : Option Bool) (saved : List Bool) :
    TM2.step program (cfg (some .carry) s [] saved) =
      some (cfg (some .restore) none [true] saved) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

private theorem step_restore_cons (s : Option Bool) (x : Bool) (q saved : List Bool) :
    TM2.step program (cfg (some .restore) s q (x :: saved)) =
      some (cfg (some .restore) (some x) (x :: q) saved) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

private theorem step_restore_nil (s : Option Bool) (q : List Bool) :
    TM2.step program (cfg (some .restore) s q []) =
      some (cfg none none q []) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

theorem restore_correct (s : Option Bool) (q saved : List Bool) :
    run (saved.length + 1) (cfg (some .restore) s q saved) =
      cfg none none (saved.reverse ++ q) [] := by
  induction saved generalizing s q with
  | nil => simpa using run_succ (step_restore_nil s q) 0
  | cons x saved ih =>
      rw [List.length_cons, run_succ (step_restore_cons s x q saved)]
      simpa [List.reverse_cons, List.append_assoc] using ih (some x) (x :: q)

theorem run_correct (s : Option Bool) (q saved : List Bool) :
    run (2 * carryCount q + saved.length + 2) (cfg (some .carry) s q saved) =
      cfg none none (saved.reverse ++ successor q) [] := by
  induction q generalizing s saved with
  | nil =>
      simpa [carryCount, successor, Nat.add_assoc] using
        (run_succ (step_carry_nil s saved) (saved.length + 1)).trans
          (restore_correct none [true] saved)
  | cons b q ih =>
      cases b with
      | false =>
          simpa [carryCount, successor, Nat.add_assoc] using
            (run_succ (step_carry_false s q saved) (saved.length + 1)).trans
              (restore_correct (some false) (true :: q) saved)
      | true =>
          have h := (run_succ (step_carry_true s q saved)
            (2 * carryCount q + (false :: saved).length + 2)).trans
              (ih (some true) (false :: saved))
          have htime : 2 * carryCount (true :: q) + saved.length + 2 =
              (2 * carryCount q + (false :: saved).length + 2) + 1 := by
            simp only [carryCount, List.length_cons]
            omega
          rw [htime]
          simpa only [successor, List.reverse_cons, List.append_assoc,
            List.singleton_append] using h

noncomputable def machine : BitMachine.Machine :=
  ofFinite (0 : Fin 2) 0 .carry (none : Option Bool) program

theorem outputs_all (q : List Bool) :
    machine.OutputsWithin q (successor q) (2 * q.length + 2) := by
  apply outputsWithin_of_raw_run (0 : Fin 2) 0 .carry (none : Option Bool) program
    q (successor q) (2 * carryCount q + 2) (2 * q.length + 2)
      (by have := carryCount_le_length q; omega)
  · have h := run_correct none q []
    simp only [List.length_nil, Nat.add_zero, List.reverse_nil, List.nil_append] at h
    change (run (2 * carryCount q + 2) (cfg (some .carry) none q [])).l = none
    rw [h]
    rfl
  · have h := run_correct none q []
    simp only [List.length_nil, Nat.add_zero, List.reverse_nil, List.nil_append] at h
    change (run (2 * carryCount q + 2) (cfg (some .carry) none q [])).stk 0 = successor q
    rw [h]
    rfl

theorem successor_polytime : BitMachine.Polytime successor := by
  refine ⟨machine, 2, 1, fun q => ?_⟩
  simpa only [pow_one, Nat.mul_add, Nat.mul_one] using outputs_all q

end EthInapproximability.CurrentPaper.BinarySuccessorMachine
