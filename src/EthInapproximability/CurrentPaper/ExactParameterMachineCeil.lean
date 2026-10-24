import EthInapproximability.CurrentPaper.MatrixUnaryDivision
import EthInapproximability.CurrentPaper.BitMachineRawSequence
import Mathlib.Algebra.Order.Floor.Div

/-!
# Literal unary ceiling-division finishing step

The existing six-stack divider leaves the quotient in stack 4 and the
remainder in stack 3. One fixed transition tests whether the remainder is
nonempty and adds one unary quotient cell exactly in that case. The dividend
and divisor are actual unary stacks; no arithmetic operation is put in finite
control. A later source-derived phase supplies `3r` and `s`.
-/

namespace EthInapproximability.CurrentPaper.ExactParameterMachineCeil

open Turing Turing.TM2.Stmt BitMachineEncoding

abbrev Stack := Fin 6

def finishProgram : Fin 1 → TM2.Stmt (fun _ : Stack => Bool) (Fin 1) Bool
  | _ => pop 3 (fun _ b => b.isSome)
      (branch id (push 4 (fun _ => true) halt) halt)

def program : BitMachineRawSequence.Label MatrixUnaryDivision.Label (Fin 1) →
    TM2.Stmt (fun _ : Stack => Bool)
      (BitMachineRawSequence.Label MatrixUnaryDivision.Label (Fin 1))
      (BitMachineRawSequence.Control Bool Bool) :=
  BitMachineRawSequence.program MatrixUnaryDivision.program finishProgram 0 false false

private theorem finish_step (n m : ℕ) :
    let S := (MatrixUnaryDivision.cfg none false []
      (List.replicate m true) [] (List.replicate (n % m) true)
      (List.replicate (n / m) true) []).stk
    (advance finishProgram)
      (⟨some 0, false, S⟩ : TM2.Cfg (fun _ : Stack => Bool) (Fin 1) Bool) =
      ⟨none, (n % m ≠ 0),
        Function.update (Function.update S 3 (List.replicate (n % m - 1) true))
          4 (List.replicate (n / m + if n % m = 0 then 0 else 1) true)⟩ := by
  by_cases h : n % m = 0
  · simp [advance, finishProgram, TM2.step, TM2.stepAux, MatrixUnaryDivision.cfg, h]
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h
    simp [advance, finishProgram, TM2.step, TM2.stepAux, MatrixUnaryDivision.cfg,
      hk, List.replicate_succ]

def inputBank (n m : ℕ) : Stack → List Bool :=
  (MatrixUnaryDivision.cfg (some .start) false
    (List.replicate n true) (List.replicate m true) [] [] [] []).stk

def outputBank (n m : ℕ) : Stack → List Bool :=
  let S := (MatrixUnaryDivision.cfg none false []
    (List.replicate m true) [] (List.replicate (n % m) true)
    (List.replicate (n / m) true) []).stk
  Function.update (Function.update S 3 (List.replicate (n % m - 1) true))
    4 (List.replicate (n / m + if n % m = 0 then 0 else 1) true)

theorem run_quotient (n m : ℕ) :
    ∃ t ≤ MatrixUnaryDivision.totalTime n m + 2,
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel MatrixUnaryDivision.Label.start),
          (false, false), inputBank n m⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, (false, n % m ≠ 0), outputBank n m⟩ := by
  let S := (MatrixUnaryDivision.cfg none false []
    (List.replicate m true) [] (List.replicate (n % m) true)
    (List.replicate (n / m) true) []).stk
  have ha := MatrixUnaryDivision.division_total_run n m
  have hb := finish_step n m
  have hh := BitMachineRawSequence.runs MatrixUnaryDivision.program finishProgram
    MatrixUnaryDivision.Label.start 0 false false false (n % m ≠ 0)
    (inputBank n m) S (outputBank n m)
    (MatrixUnaryDivision.totalTime n m) 1
    (by simpa [MatrixUnaryDivision.run, inputBank] using ha)
    (by simpa [S, outputBank] using hb)
  simpa only [program, Nat.add_assoc] using hh

theorem output_quotient (n m : ℕ) :
    outputBank n m 4 =
      List.replicate (n / m + if n % m = 0 then 0 else 1) true := by
  simp [outputBank]

theorem quotient_eq_ceil (n m : ℕ) (hm : 0 < m) :
    n / m + (if n % m = 0 then 0 else 1) = n ⌈/⌉ m := by
  let q := n / m
  let r := n % m
  have hd : r + m * q = n := Nat.mod_add_div n m
  have hr : r < m := Nat.mod_lt n hm
  have hc : n ≤ m * (n ⌈/⌉ m) :=
    (ceilDiv_le_iff_le_mul hm).mp (le_refl _)
  by_cases hz : n % m = 0
  · simp only [hz, ↓reduceIte, Nat.add_zero]
    apply Nat.le_antisymm
    · by_contra h
      have hh : n ⌈/⌉ m + 1 ≤ q := by omega
      have hmul := Nat.mul_le_mul_left m hh
      change r = 0 at hz
      nlinarith
    · apply (ceilDiv_le_iff_le_mul hm).mpr
      change r = 0 at hz
      dsimp [q, r] at hd hz
      omega
  · simp only [hz, ↓reduceIte]
    apply Nat.le_antisymm
    · by_contra h
      have hh : n ⌈/⌉ m ≤ q := by omega
      have hmul := Nat.mul_le_mul_left m hh
      have hpos : 0 < r := by
        change r ≠ 0 at hz
        omega
      omega
    · apply (ceilDiv_le_iff_le_mul hm).mpr
      dsimp [q, r] at hd hr
      nlinarith

theorem output_ceil (n m : ℕ) (hm : 0 < m) :
    outputBank n m 4 = List.replicate (n ⌈/⌉ m) true := by
  rw [output_quotient, quotient_eq_ceil n m hm]

end EthInapproximability.CurrentPaper.ExactParameterMachineCeil
