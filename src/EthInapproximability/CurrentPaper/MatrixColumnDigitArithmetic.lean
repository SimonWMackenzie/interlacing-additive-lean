import EthInapproximability.CurrentPaper.MatrixLabelArithmetic

/-!
# Quotient chains and the lexicographic column labels

These arithmetic identities connect the physical divisions in
`MatrixColumnDecode` to the column equivalence used by the exact construction.
They do not replace or estimate any machine transitions.
-/

namespace EthInapproximability.CurrentPaper.MatrixColumnDigitArithmetic

open MatrixMaterialization ExactConstruction

def digit (n b : ℕ) (p : Fin 4) : ℕ := n / b ^ (3 - p.val) % b

theorem low_digit (n b : ℕ) (p : Fin 4) :
    (n % b ^ 4 / b ^ (3 - p.val)) % b = digit n b p := by
  have hsum : 4 = (3 - p.val) + (p.val + 1) := by have := p.isLt; omega
  have hp : b ^ 4 = b ^ (3 - p.val) * b ^ (p.val + 1) := by
    rw [← pow_add, ← hsum]
  rw [hp, Nat.mod_mul_right_div_self]
  exact Nat.mod_mod_of_dvd _ (by
    refine ⟨b ^ p.val, ?_⟩
    simp [pow_succ, Nat.mul_comm])

theorem coordinate {d N₁ : ℕ} (code : Fin (8 * (d * N₁) ^ 4)) (p : Fin 4) :
    (((columnCode d N₁).symm code).2 p).1.val = digit code.val (d * N₁) p / N₁ := by
  rw [MatrixLabelArithmetic.column_coordinate, low_digit]

theorem family_index {d N₁ : ℕ} (code : Fin (8 * (d * N₁) ^ 4)) (p : Fin 4) :
    (((columnCode d N₁).symm code).2 p).2.val = digit code.val (d * N₁) p % N₁ := by
  rw [MatrixLabelArithmetic.column_family_index, low_digit]

theorem digit_zero (n b : ℕ) : digit n b 0 = n / b / b / b % b := by
  simp [digit, Nat.div_div_eq_div_mul, pow_succ, Nat.mul_assoc]

theorem digit_one (n b : ℕ) : digit n b 1 = n / b / b % b := by
  simp [digit, Nat.div_div_eq_div_mul, pow_succ]

theorem digit_two (n b : ℕ) : digit n b 2 = n / b % b := by
  simp [digit]

theorem digit_three (n b : ℕ) : digit n b 3 = n % b := by
  simp [digit]

theorem tail_quotient (n b : ℕ) : n / b ^ 4 = n / b / b / b / b := by
  simp [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_assoc]

theorem tail_index {d N₁ : ℕ} (code : Fin (8 * (d * N₁) ^ 4)) :
    (tailCode ((columnCode d N₁).symm code).1).val =
      code.val / (d * N₁) / (d * N₁) / (d * N₁) / (d * N₁) := by
  rw [MatrixLabelArithmetic.column_tail_index, tail_quotient]

end EthInapproximability.CurrentPaper.MatrixColumnDigitArithmetic
