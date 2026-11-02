import EthInapproximability.CurrentPaper.BinarySuccessorMachine
import EthInapproximability.CurrentPaper.CutoffBitMachineCore
import EthInapproximability.CurrentPaper.BitMachineComposition

/-!
# Writing the arithmetic cutoff's canonical input

Source: frozen v8 `05-iteration.tex`, the bounded simulations on consecutive
level indices. The loop here expands an ordinary binary word to the actual
two-bit symbol encoding accepted by the compiled cutoff program. Every
written bit and the terminator are charged; the binary successor is a
separate literal finite machine.
-/

namespace EthInapproximability.CurrentPaper.CutoffInputEncoding

open Turing Turing.TM2.Stmt BitMachineEncoding

def digits : List Bool → List Bool
  | [] => []
  | b :: q => b :: false :: digits q

def word (q : List Bool) : List Bool := digits q ++ [false, true]

theorem digits_length (q : List Bool) : (digits q).length = 2 * q.length := by
  induction q with
  | nil => rfl
  | cons b q ih => simp only [digits, List.length_cons, ih]; omega

theorem encodeStack_append (xs ys : List (Bool × Bool)) :
    BitMachinePairAlphabet.encodeStack (xs ++ ys) =
      BitMachinePairAlphabet.encodeStack xs ++ BitMachinePairAlphabet.encodeStack ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, BitMachinePairAlphabet.encodeStack, ih]

theorem trPosNum_digits (p : PosNum) :
    BitMachinePairAlphabet.encodeStack
      ((Turing.PartrecToTM2.trPosNum p).map CutoffBitMachine.Compile.symbolEquiv.symm) =
        digits (p : ℕ).bits := by
  induction p with
  | one => rfl
  | bit0 p ih =>
      have hb : (2 * (p : ℕ)).bits = false :: (p : ℕ).bits := by
        have hp := PosNum.to_nat_pos p
        simpa only [Nat.bit_val, Bool.toNat_false, zero_add] using
          Nat.bits_append_bit (p : ℕ) false (by omega)
      simp only [Turing.PartrecToTM2.trPosNum, List.map_cons,
        BitMachinePairAlphabet.encodeStack, PosNum.cast_bit0]
      rw [← two_mul, hb]
      exact congrArg (false :: false :: ·) ih
  | bit1 p ih =>
      have hb : (2 * (p : ℕ) + 1).bits = true :: (p : ℕ).bits := by
        simpa only [Nat.bit_val, Bool.toNat_true, Nat.add_comm 1] using
          Nat.bits_append_bit (p : ℕ) true (by simp)
      simp only [Turing.PartrecToTM2.trPosNum, List.map_cons,
        BitMachinePairAlphabet.encodeStack, PosNum.cast_bit1]
      rw [← two_mul, hb]
      exact congrArg (true :: false :: ·) ih

theorem trNum_digits (p : Num) :
    BitMachinePairAlphabet.encodeStack
      ((Turing.PartrecToTM2.trNum p).map CutoffBitMachine.Compile.symbolEquiv.symm) =
        digits (p : ℕ).bits := by
  cases p with
  | zero => rfl
  | pos p => exact trPosNum_digits p

theorem encodedNat_eq (n : ℕ) : CutoffBitMachine.encodedNat n = word n.bits := by
  have h : BitMachinePairAlphabet.encodeStack
      ((Turing.PartrecToTM2.trNat n).map CutoffBitMachine.Compile.symbolEquiv.symm) =
        digits n.bits := by simpa [Turing.PartrecToTM2.trNat] using trNum_digits (n : Num)
  simp only [CutoffBitMachine.encodedNat, CutoffBitMachine.Compile.encodeSymbols,
    Turing.PartrecToTM2.trList, List.map_append, encodeStack_append, h]
  rfl

inductive Label where
  | start | scan | restore
  deriving DecidableEq, Fintype

def program : Label → TM2.Stmt (fun _ : Fin 3 => Bool) Label (Option Bool)
  | .start => push 2 (fun _ => true) (push 2 (fun _ => false) (goto (fun _ => .scan)))
  | .scan => pop 0 (fun _ b => b)
      (branch Option.isSome
        (push 1 (fun b => b.getD false) (push 1 (fun _ => false) (goto (fun _ => .scan))))
        (goto (fun _ => .restore)))
  | .restore => pop 1 (fun _ b => b)
      (branch Option.isSome
        (push 2 (fun b => b.getD false) (goto (fun _ => .restore)))
        (load (fun _ => none) halt))

def cfg (l : Option Label) (v : Option Bool) (q saved out : List Bool) :
    TM2.Cfg (fun _ : Fin 3 => Bool) Label (Option Bool) :=
  ⟨l, v, ![q, saved, out]⟩

def run (n : ℕ) (c : TM2.Cfg (fun _ : Fin 3 => Bool) Label (Option Bool)) :=
  ((advance program)^[n]) c

theorem scan_cons (b : Bool) (q saved out : List Bool) (v : Option Bool) :
    advance program (cfg (some .scan) v (b :: q) saved out) =
      cfg (some .scan) (some b) q (false :: b :: saved) out := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]
  funext k
  fin_cases k <;> rfl

theorem scan_nil (saved out : List Bool) (v : Option Bool) :
    advance program (cfg (some .scan) v [] saved out) = cfg (some .restore) none [] saved out := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]

theorem scan_run (q saved out : List Bool) (v : Option Bool) :
    run (q.length + 1) (cfg (some .scan) v q saved out) =
      cfg (some .restore) none [] ((digits q).reverse ++ saved) out := by
  induction q generalizing saved v with
  | nil => simpa only [run, Function.iterate_one, List.length_nil, zero_add,
      digits, List.reverse_nil, List.nil_append] using scan_nil saved out v
  | cons b q ih =>
      simp only [List.length_cons, run, Function.iterate_succ_apply, scan_cons]
      simpa only [run, digits, List.reverse_cons, List.append_assoc, List.singleton_append]
        using ih (false :: b :: saved) (some b)

theorem restore_cons (b : Bool) (q saved out : List Bool) (v : Option Bool) :
    advance program (cfg (some .restore) v q (b :: saved) out) =
      cfg (some .restore) (some b) q saved (b :: out) := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]
  funext k
  fin_cases k <;> rfl

theorem restore_nil (q out : List Bool) (v : Option Bool) :
    advance program (cfg (some .restore) v q [] out) = cfg none none q [] out := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]

theorem restore_run (q saved out : List Bool) (v : Option Bool) :
    run (saved.length + 1) (cfg (some .restore) v q saved out) =
      cfg none none q [] (saved.reverse ++ out) := by
  induction saved generalizing out v with
  | nil => simpa only [run, Function.iterate_one, List.length_nil, zero_add,
      List.reverse_nil, List.nil_append] using restore_nil q out v
  | cons b saved ih =>
      simp only [List.length_cons, run, Function.iterate_succ_apply, restore_cons]
      simpa only [run, List.reverse_cons, List.append_assoc, List.singleton_append]
        using ih (b :: out) (some b)

theorem start_step (q out : List Bool) :
    advance program (cfg (some .start) none q [] out) =
      cfg (some .scan) none q [] (false :: true :: out) := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]
  funext k
  fin_cases k <;> rfl

theorem run_correct (q out : List Bool) :
    run (3 * q.length + 3) (cfg (some .start) none q [] out) =
      cfg none none [] [] (word q ++ out) := by
  have hs := scan_run q [] (false :: true :: out) none
  rw [List.append_nil] at hs
  have hr := restore_run [] (digits q).reverse (false :: true :: out) none
  rw [List.length_reverse, digits_length, List.reverse_reverse] at hr
  have htime : 3 * q.length + 3 = (2 * q.length + 1) + (q.length + 1) + 1 := by omega
  rw [htime]
  change ((advance program)^[_ + 1]) _ = _
  rw [Function.iterate_succ_apply, start_step, Function.iterate_add_apply]
  change run (2 * q.length + 1) (run (q.length + 1) _) = _
  rw [hs, hr]
  simp [word, List.append_assoc]

noncomputable def machine : BitMachine.Machine :=
  ofFinite (0 : Fin 3) 2 .start (none : Option Bool) program

theorem outputs_all (q : List Bool) : machine.OutputsWithin q (word q) (3 * q.length + 3) := by
  apply outputsWithin_of_raw_run (0 : Fin 3) 2 .start (none : Option Bool) program
    q (word q) (3 * q.length + 3) (3 * q.length + 3) le_rfl
  all_goals
    have hi : rawInit (0 : Fin 3) .start (none : Option Bool) q =
        cfg (some .start) none q [] [] := by
      unfold rawInit cfg
      congr 1
      funext k
      fin_cases k <;> simp
    rw [hi]
  · change (run (3 * q.length + 3) _).l = none
    rw [run_correct]
    rfl
  · change (run (3 * q.length + 3) _).stk 2 = word q
    rw [run_correct]
    simp [cfg]

theorem word_polytime : BitMachine.Polytime word := by
  refine ⟨machine, 3, 1, fun q => ?_⟩
  simpa only [pow_one, Nat.mul_add, Nat.mul_one] using outputs_all q

def nextInput (q : List Bool) : List Bool := word (BinarySuccessorMachine.successor q)

theorem nextInput_bits (n : ℕ) : nextInput n.bits = CutoffBitMachine.encodedNat (n + 1) := by
  rw [nextInput, BinarySuccessorMachine.successor_bits, ← encodedNat_eq]

theorem successor_length_le (q : List Bool) :
    (BinarySuccessorMachine.successor q).length ≤ q.length + 1 := by
  induction q with
  | nil => rfl
  | cons b q ih => cases b <;> simp only [BinarySuccessorMachine.successor,
      List.length_cons] <;> omega

noncomputable def nextMachine : BitMachine.Machine :=
  BitMachineComposition.composition BinarySuccessorMachine.machine machine

/-- The next canonical cutoff index is actually written by one composed
finite machine, starting from the current ordinary binary counter. -/
theorem next_outputs (q : List Bool) :
    nextMachine.OutputsWithin q (nextInput q) (7 * q.length + 12) := by
  have h := BitMachineComposition.composition_outputsWithin BinarySuccessorMachine.machine machine
    (BinarySuccessorMachine.outputs_all q) (outputs_all (BinarySuccessorMachine.successor q))
  apply BitMachine.outputsWithin_mono _ h
  have hl := successor_length_le q
  omega

theorem nextInput_polytime : BitMachine.Polytime nextInput :=
  BitMachineComposition.polytime_comp BinarySuccessorMachine.successor_polytime word_polytime

end EthInapproximability.CurrentPaper.CutoffInputEncoding
