import EthInapproximability.CurrentPaper.MatrixMaterialization

/-!
# Arithmetic decoding of the fixed row-major label order

Source: locked v8 explicit carriers and Appendix B lexicographic orders.
These identities identify the public equivalences used by the finite proof
with quotient/remainder operations. Actual unary operations are implemented
separately in `MatrixUnaryDivision`; these identities alone are not runtime.
-/

namespace EthInapproximability.CurrentPaper.MatrixLabelArithmetic

open MatrixMaterialization ExactConstruction

theorem tuple_digit {m n : ℕ} (code : Fin (m ^ n)) (j : Fin n) :
    ((tupleCode m n).symm code j).val = code.val / m ^ (n - 1 - j.val) % m := by
  have he : j.rev.val = n - 1 - j.val := by simp only [Fin.val_rev]; omega
  change code.val / m ^ j.rev.val % m = _
  rw [he]

theorem template_row_value {N₂ n : ℕ} (p : Fin 4) (z : Fin N₂) :
    (rowCode N₂ n (.inl (p, z))).val = z.val + N₂ * p.val := by
  rfl

theorem source_row_value {N₂ n : ℕ} (i : Fin n) :
    (rowCode N₂ n (.inr i)).val = 4 * N₂ + i.val := by
  rfl

theorem template_row_bin {N₂ n : ℕ} (p : Fin 4) (z : Fin N₂) :
    (rowCode N₂ n (.inl (p, z))).val / N₂ = p.val := by
  have hn : 0 < N₂ := lt_of_le_of_lt (Nat.zero_le z.val) z.isLt
  rw [template_row_value, Nat.add_mul_div_left _ _ hn]
  simp [Nat.div_eq_of_lt z.isLt]

theorem template_row_index {N₂ n : ℕ} (p : Fin 4) (z : Fin N₂) :
    (rowCode N₂ n (.inl (p, z))).val % N₂ = z.val := by
  rw [template_row_value]
  simp [Nat.mod_eq_of_lt z.isLt]

theorem column_tail_index {d N₁ : ℕ} (code : Fin (8 * (d * N₁) ^ 4)) :
    (tailCode ((columnCode d N₁).symm code).1).val = code.val / (d * N₁) ^ 4 := by
  change (tailCode (tailCode.symm code.divNat)).val = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem column_coordinate {d N₁ : ℕ} (code : Fin (8 * (d * N₁) ^ 4)) (p : Fin 4) :
    (((columnCode d N₁).symm code).2 p).1.val =
      ((code.val % (d * N₁) ^ 4 / (d * N₁) ^ (3 - p.val)) % (d * N₁)) / N₁ := by
  change (((tupleCode (d * N₁) 4).symm code.modNat p).val / N₁) = _
  rw [tuple_digit]
  rfl

theorem column_family_index {d N₁ : ℕ} (code : Fin (8 * (d * N₁) ^ 4)) (p : Fin 4) :
    (((columnCode d N₁).symm code).2 p).2.val =
      ((code.val % (d * N₁) ^ 4 / (d * N₁) ^ (3 - p.val)) % (d * N₁)) % N₁ := by
  change (((tupleCode (d * N₁) 4).symm code.modNat p).val % N₁) = _
  rw [tuple_digit]
  rfl

theorem column_tail_bit {d N₁ : ℕ} (code : Fin (8 * (d * N₁) ^ 4)) (j : Fin 3) :
    (finTwoEquiv.symm (((columnCode d N₁).symm code).1 j)).val =
      (code.val / (d * N₁) ^ 4 / 2 ^ (2 - j.val)) % 2 := by
  change (finTwoEquiv.symm (finTwoEquiv _)).val = _
  rw [Equiv.symm_apply_apply]
  exact tuple_digit (m := 2) code.divNat j

end EthInapproximability.CurrentPaper.MatrixLabelArithmetic
