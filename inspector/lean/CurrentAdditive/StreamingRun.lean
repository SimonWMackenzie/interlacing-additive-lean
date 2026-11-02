import CurrentAdditive.StreamingBitMachine
import CurrentAdditive.PowerQuotientSemantics
import CurrentAdditive.BitMulCommutative

/-! Repeated physical streaming rounds, retaining one power and printing
one dot bit per round. The orientation of multiplication is reconciled with
the constructor's right-multiplication convention separately. -/

namespace CurrentAdditive.FiniteFieldMachine.StreamingRun

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.SamplerMachine
open CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge
open CurrentAdditive.FiniteFieldConstructor.BitPrinter
open CurrentAdditive.FiniteFieldMachine.HornerNatBridge
open CurrentAdditive.FiniteFieldMachine.StreamingBitMachine

def leftPower (d modulus y : ℕ) : ℕ → ℕ
  | 0 => 1
  | j + 1 => mul d modulus y (leftPower d modulus y j)

theorem leftPower_lt (d tail y j : ℕ) (htail : tail < 2 ^ d)
    (hd : 0 < d) (hy : y < 2 ^ d) :
    leftPower d (CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d tail)
      y j < 2 ^ d := by
  induction j with
  | zero =>
      simpa only [leftPower] using Nat.one_lt_two_pow (by omega : d ≠ 0)
  | succ j ih =>
      simpa only [leftPower] using
        mul_lt d (CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d tail)
          y (leftPower d
            (CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d tail)
            y j)
          (monicBits_lt d tail htail) (monicBits_topBit d tail htail) ih

theorem leftPower_eq_power (d tail y j : ℕ) (htail : tail < 2 ^ d)
    (hd : 0 < d) (hy : y < 2 ^ d) :
    leftPower d (CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d tail)
      y j =
    power d (CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d tail)
      y j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [leftPower, power, ih]
      exact bit_mul_comm_monicBits d tail y
        (power d (CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d tail)
          y j) hd htail hy
        (power_lt d _ y j hd
          (monicBits_lt d tail htail) (monicBits_topBit d tail htail) hy)

def reverseExpected (d modulus x y j : ℕ) : ℕ → List Bool
  | 0 => []
  | n + 1 => reverseExpected d modulus x y (j + 1) n ++
      [dot d x (leftPower d modulus y j)]

theorem reverseExpected_eq_direct (d tail x y j n : ℕ)
    (htail : tail < 2 ^ d) (hd : 0 < d) (hy : y < 2 ^ d) :
    reverseExpected d
      (CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d tail)
      x y j n =
    ((List.range n).map (fun k =>
      bit d (CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d tail)
        x y (j + k))).reverse := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
      rw [reverseExpected, List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map, Nat.add_zero, List.reverse_cons]
      rw [leftPower_eq_power d tail y j htail hd hy]
      change reverseExpected d _ x y (j + 1) n ++ [bit d _ x y j] = _
      rw [ih (j + 1)]
      congr 1
      apply congrArg List.reverse
      apply List.map_congr_left
      intro k hk
      congr 1
      omega

private theorem run_check_nil (a y c x out : List Bool) :
    run 1 (cfg (some (.inr .check)) initial a y [] [] c [] [] x [] [] out) =
      cfg none initial a y [] [] c [] [] x [] [] out := by
  simpa using StreamingBitMachine.run_succ
    (StreamingBitMachine.step_check_nil initial a y [] [] c [] x [] [] out) 0

/-- All rounds of a fixed seed are literal TM2 transitions. The input fuel
is unary, and the final extra step detects its empty stack. -/
theorem run_leftStream (d tail : ℕ) (htail : tail < 2 ^ d)
    (hd : 0 < d) (x y : Fin (2 ^ d)) (j : ℕ)
    (fuel : List Bool) (out : List Bool) :
    let modulus := CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d tail
    let c := lowerWord d modulus
    let current := leftPower d modulus y.val j
    ∃ t ≤ fuel.length * (d * (4 * d + 5) + 4 * d + 6) + 1,
      run t (cfg (some (.inr .check)) initial
        (encodeWord (xBits d ⟨current, leftPower_lt d tail y.val j htail hd y.isLt⟩))
        (encodeWord (xBits d y)) [] [] (encodeWord c) [] fuel
        (encodeWord (xBits d x)) [] [] out) =
      cfg none initial
        (encodeWord (xBits d ⟨leftPower d modulus y.val (j + fuel.length),
          leftPower_lt d tail y.val (j + fuel.length) htail hd y.isLt⟩))
        (encodeWord (xBits d y)) [] [] (encodeWord c) [] []
        (encodeWord (xBits d x)) [] []
        (reverseExpected d modulus x.val y.val j fuel.length ++ out) := by
  intro modulus c current
  induction fuel generalizing j out with
  | nil =>
      refine ⟨1, by simp, ?_⟩
      simpa [reverseExpected] using
        run_check_nil
          (encodeWord (xBits d ⟨current, leftPower_lt d tail y.val j htail hd y.isLt⟩))
          (encodeWord (xBits d y)) (encodeWord c)
          (encodeWord (xBits d x)) out
  | cons b fuel ih =>
      let a : Fin (2 ^ d) :=
        ⟨leftPower d modulus y.val j, leftPower_lt d tail y.val j htail hd y.isLt⟩
      obtain ⟨ts, hts, hs⟩ :=
        round_run d tail htail hd x y a b fuel out
      obtain ⟨tr, htr, hr⟩ := ih (j + 1)
        (dot d x.val (leftPower d modulus y.val j) :: out)
      refine ⟨ts + tr, ?_, ?_⟩
      · simp only [List.length_cons]
        calc
          ts + tr ≤ (d * (4 * d + 5) + 4 * d + 6) +
              (fuel.length * (d * (4 * d + 5) + 4 * d + 6) + 1) :=
            Nat.add_le_add hts htr
          _ = (fuel.length + 1) * (d * (4 * d + 5) + 4 * d + 6) + 1 := by
            ring
      · rw [StreamingBitMachine.run_add, hs]
        change StreamingBitMachine.run tr _ = _
        have hnext : encodeWord (lowerWord d (mul d modulus y.val a.val)) =
            encodeWord (xBits d ⟨leftPower d modulus y.val (j + 1),
              leftPower_lt d tail y.val (j + 1) htail hd y.isLt⟩) := by
          rfl
        rw [hnext]
        rw [hr]
        simp only [List.length_cons, Nat.add_assoc, reverseExpected,
          List.append_assoc, List.singleton_append]
        simp only [Nat.add_comm 1 fuel.length]

/-- A complete physical one-seed printer. Its output bank is stack oriented,
so the direct word appears in reverse order; one linear copy restores the
usual printed order when the surrounding table writer needs it. -/
theorem run_bitPrinter_word (d tail n : ℕ) (htail : tail < 2 ^ d)
    (hd : 0 < d) (x y : Fin (2 ^ d)) :
    let modulus := CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d tail
    let c := lowerWord d modulus
    ∃ t ≤ n * (d * (4 * d + 5) + 4 * d + 6) + 1,
      run t (cfg (some (.inr .check)) initial
        (encodeWord (xBits d ⟨1, Nat.one_lt_two_pow (by omega : d ≠ 0)⟩))
        (encodeWord (xBits d y)) [] [] (encodeWord c) []
        (List.replicate n true) (encodeWord (xBits d x)) [] [] []) =
      cfg none initial
        (encodeWord (xBits d ⟨power d modulus y.val n,
          power_lt d modulus y.val n hd
            (monicBits_lt d tail htail) (monicBits_topBit d tail htail)
            y.isLt⟩))
        (encodeWord (xBits d y)) [] [] (encodeWord c) [] []
        (encodeWord (xBits d x)) [] []
        (word d modulus n x.val y.val).reverse := by
  intro modulus c
  obtain ⟨t, ht, hr⟩ := run_leftStream d tail htail hd x y 0
    (List.replicate n true) []
  refine ⟨t, by simpa using ht, ?_⟩
  simpa only [leftPower, List.length_replicate, Nat.zero_add, List.append_nil,
    leftPower_eq_power d tail y.val n htail hd y.isLt,
    reverseExpected_eq_direct d tail x.val y.val 0 n htail hd y.isLt,
    word] using hr

#print axioms run_leftStream
#print axioms run_bitPrinter_word

end CurrentAdditive.FiniteFieldMachine.StreamingRun
