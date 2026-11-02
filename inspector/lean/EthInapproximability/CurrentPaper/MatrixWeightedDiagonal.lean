import EthInapproximability.CurrentPaper.MatrixWeightedGroupMachine
import EthInapproximability.CurrentPaper.MatrixStage4Digits

/-!
# The joint-tail diagonal's raw column address

The diagonal support in frozen v8 Appendix A is not an arbitrary third input
table.  Its raw `B` column code consists of the actual tail code followed by
the *same* second-row code in every one of the `s` bins.  This file identifies
the exact arithmetic target for a future finite-stack address constructor.
It does not treat computation of the suffix, geometric multiplier, or power
as a unit-cost machine instruction.
-/

namespace EthInapproximability.CurrentPaper.MatrixWeightedDiagonal



open Construction MatrixStage4Codes MatrixStage4Digits MatrixMaterialization

def geometricFactor (base s : ℕ) : ℕ := ∑ i : Fin s, base ^ i.val

theorem tupleCode_constant (base s : ℕ) (d : Fin base) :
    (tupleCode base s (fun _ => d)).val = d.val * geometricFactor base s := by
  change (finFunctionFinEquiv (fun _ : Fin s => d)).val = _
  rw [finFunctionFinEquiv_apply]
  simp [geometricFactor, Finset.mul_sum]

def tailOrdinal {a s q cy : ℕ} (d : SecondRows a s q (Fin cy)) : ℕ :=
  (tupleCode cy (s + 1) (fun i => d.2 (tailCoordinate a s i))).val

theorem digit_of_suffix_mod (code base s : ℕ) (j : Fin (s + 1)) :
    (code % base ^ (s + 1)) / base ^ (s - j.val) % base =
      code / base ^ (s - j.val) % base := by
  have hj : s - j.val + (j.val + 1) = s + 1 := by omega
  have hp : base ^ (s + 1) = base ^ (s - j.val) * base ^ (j.val + 1) := by
    rw [← pow_add, hj]
  have hdvd : base ∣ base ^ (j.val + 1) := by
    refine ⟨base ^ j.val, ?_⟩
    simp [pow_succ, Nat.mul_comm]
  rw [hp, Nat.mod_mul_right_div_self]
  exact Nat.mod_mod_of_dvd _ hdvd

/-- The unused tail is the low `s+1` base-`cy` digits of the first-row word. -/
theorem tailOrdinal_mod {a s q cy : ℕ} (hcy : 0 < cy)
    (d : SecondRows a s q (Fin cy)) :
    tailOrdinal d = (firstWordCode a s cy d.2).val % cy ^ (s + 1) := by
  let word := firstWordCode a s cy d.2
  let tail := tupleCode cy (s + 1) (fun i => d.2 (tailCoordinate a s i))
  let rem : Fin (cy ^ (s + 1)) :=
    ⟨word.val % cy ^ (s + 1), Nat.mod_lt _ (pow_pos hcy _)⟩
  have ht : tail = rem := by
    apply (tupleCode cy (s + 1)).symm.injective
    funext j
    apply Fin.ext
    have hword := MatrixLabelArithmetic.tuple_digit word (tailCoordinate a s j)
    have hrem := MatrixLabelArithmetic.tuple_digit rem j
    have hexp : firstLength a s - 1 - (tailCoordinate a s j).val = s - j.val := by
      simp only [firstLength, tailCoordinate_val]
      omega
    have hexp' : s + 1 - 1 - j.val = s - j.val := by omega
    rw [hexp] at hword
    simp only [tail, Equiv.symm_apply_apply]
    change (d.2 (tailCoordinate a s j)).val =
      ((tupleCode cy (s + 1)).symm rem j).val
    calc
      (d.2 (tailCoordinate a s j)).val =
          word.val / cy ^ (s - j.val) % cy := by
            simpa [word, firstWordCode] using hword
      _ = (word.val % cy ^ (s + 1)) / cy ^ (s - j.val) % cy := by
            exact (digit_of_suffix_mod word.val cy s j).symm
      _ = ((tupleCode cy (s + 1)).symm rem j).val := by
            simpa [rem, hexp'] using hrem.symm
  exact congrArg Fin.val ht

theorem diagonal_ordinal {a s q cy : ℕ}
    (d : SecondRows a s q (Fin cy)) :
    (rawColumnCode a s q cy (diagonal d)).val =
      tailOrdinal d * (binBase a s q cy) ^ s +
        (secondRowCode a s q cy d).val *
          geometricFactor (binBase a s q cy) s := by
  change (finProdFinEquiv
    ((tupleCode cy (s + 1)) (fun i => d.2 (tailCoordinate a s i)),
      thirdColumnCode a s q cy (fun _ => d))).val = _
  have hd : (thirdColumnCode a s q cy (fun _ => d)).val =
      (secondRowCode a s q cy d).val *
        geometricFactor (binBase a s q cy) s := by
    change (tupleCode (q * cy ^ firstLength a s) s
      (fun _ => secondRowCode a s q cy d)).val = _
    simpa [binBase, wordBase] using
      tupleCode_constant (q * cy ^ firstLength a s) s (secondRowCode a s q cy d)
  rw [finProdFinEquiv_apply_val]
  rw [hd]
  simp [tailOrdinal, binBase, wordBase]
  ring

/-- The repeated-bin multiplier can be obtained from two subtractions and a
quotient once the actual power `base^s` has been physically produced. -/
theorem geometricFactor_quotient (base s : ℕ) (hb : 2 ≤ base) :
    geometricFactor base s = (base ^ s - 1) / (base - 1) := by
  have hbase : base - 1 + 1 = base := by omega
  have hgeom := geom_sum_mul_add (base - 1) s
  rw [hbase] at hgeom
  have heq : geometricFactor base s * (base - 1) + 1 = base ^ s := by
    simpa only [geometricFactor, Fin.sum_univ_eq_sum_range] using hgeom
  have hden : 0 < base - 1 := by omega
  have hpow : 1 ≤ base ^ s := by omega
  rw [← heq]
  simpa [Nat.mul_comm] using
    (Nat.mul_div_cancel_left (geometricFactor base s) hden).symm

/-- Entire diagonal raw-column address in quotient/remainder form.  Every
intermediate operand appears in a fixed-machine stage below, except the two
variable powers, whose construction is deliberately left explicit. -/
theorem diagonal_ordinal_arithmetic {a s q cy : ℕ}
    (hcy : 0 < cy) (hbase : 2 ≤ binBase a s q cy)
    (d : SecondRows a s q (Fin cy)) :
    (rawColumnCode a s q cy (diagonal d)).val =
      ((firstWordCode a s cy d.2).val % cy ^ (s + 1)) *
        (binBase a s q cy) ^ s +
      (secondRowCode a s q cy d).val *
        (((binBase a s q cy) ^ s - 1) / (binBase a s q cy - 1)) := by
  rw [diagonal_ordinal, tailOrdinal_mod hcy, geometricFactor_quotient _ _ hbase]

/-- Physical quotient/remainder split of the second-row code into its public
selector and first-column word; the word-base is an explicit unary operand. -/
def second_row_split_run (code wordBase : ℕ) :=
  MatrixIndexSplit.split_run code wordBase

/-- Physical extraction of the tail suffix code by taking the remainder
modulo `cy^(s+1)`; the power is an explicit unary operand. -/
def tail_suffix_split_run (wordCode tailPower : ℕ) :=
  MatrixIndexSplit.split_run wordCode tailPower

/-- Physical quotient for the geometric multiplier.  Its equality to the
required sum is `geometricFactor_quotient` under `base >= 2`. -/
def geometric_quotient_run (power base : ℕ) :=
  MatrixIndexSplit.split_run (power - 1) (base - 1)

/-- Physical final multiply-add stage of the diagonal ordinal formula.
The two addends are produced by prior charged stages, not host arithmetic
inside this finite program. -/
def diagonal_address_run (tailCode power repeatedCode : ℕ) :=
  MatrixAddressMachine.address_run tailCode power repeatedCode false []

end EthInapproximability.CurrentPaper.MatrixWeightedDiagonal
