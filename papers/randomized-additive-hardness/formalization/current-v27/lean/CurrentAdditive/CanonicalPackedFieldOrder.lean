import CurrentAdditive.CanonicalPackedFieldBits

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalTable

open CurrentAdditive.SmallBias
open CurrentAdditive.FiniteFieldConstructor

/-- The packed bit array is the concatenation of the words in pair-label order. -/
theorem packedFieldBits_eq_flatten_ofFn (d modulus n : ℕ) :
    packedFieldBits d modulus n =
      (List.ofFn fun ℓ : Fin ((2 ^ d) ^ 2) =>
        List.ofFn fun j : Fin n =>
          let xy := (printerPairLabel d).symm ℓ
          BitPrinter.bit d modulus xy.1.val xy.2.val j.val).flatten := by
  rw [packedFieldBits, List.ofFn_mul]
  congr 1
  congr 1
  funext ℓ
  congr 1
  funext j
  have hk : (⟨ℓ.val * n + j.val, by
      have h1 : ℓ.val * n + j.val < (ℓ.val + 1) * n := by
        rw [Nat.add_mul]
        omega
      exact h1.trans_le (Nat.mul_le_mul_right n ℓ.isLt)⟩ :
        Fin ((2 ^ d) ^ 2 * n)) = finProdFinEquiv (ℓ,j) := by
    apply Fin.ext
    simp [finProdFinEquiv, Nat.mul_comm]
    omega
  rw [hk, Equiv.symm_apply_apply]

theorem ofFn_bit_eq_word (d modulus n x y : ℕ) :
    (List.ofFn fun j : Fin n => BitPrinter.bit d modulus x y j.val) =
      BitPrinter.word d modulus n x y := by
  apply List.ext_getElem (by simp [BitPrinter.word])
  intro i h₁ h₂
  simp only [List.getElem_ofFn, BitPrinter.word, List.getElem_map,
    List.getElem_range]

theorem packedFieldBits_eq_flatten_words (d modulus n : ℕ) :
    packedFieldBits d modulus n =
      (List.ofFn fun ℓ : Fin ((2 ^ d) ^ 2) =>
        let xy := (printerPairLabel d).symm ℓ
        BitPrinter.word d modulus n xy.1.val xy.2.val).flatten := by
  rw [packedFieldBits_eq_flatten_ofFn]
  congr 1
  congr 1
  funext ℓ
  exact ofFn_bit_eq_word d modulus n _ _

#print axioms packedFieldBits_eq_flatten_ofFn
#print axioms ofFn_bit_eq_word
#print axioms packedFieldBits_eq_flatten_words

end CurrentAdditive.FiniteFieldConstructor.CanonicalTable
