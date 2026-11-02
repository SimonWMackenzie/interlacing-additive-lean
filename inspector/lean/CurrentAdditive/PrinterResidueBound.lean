import CurrentAdditive.FirstPassingTotal

namespace CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge

open CurrentAdditive.FiniteFieldConstructor.BitPrinter

private theorem raw_fold_lt (d a b : ℕ) (hb : b < 2 ^ d)
    (xs : List ℕ) (hxs : ∀ i ∈ xs, i < d)
    (acc : ℕ) (hacc : acc < 2 ^ (2 * d)) :
    xs.foldl (fun z i => if a.testBit i then Nat.xor z (b <<< i) else z) acc <
      2 ^ (2 * d) := by
  induction xs generalizing acc with
  | nil => simpa using hacc
  | cons i xs ih =>
      have hi : i < d := hxs i (by simp)
      have hxs' : ∀ j ∈ xs, j < d := by
        intro j hj
        exact hxs j (by simp [hj])
      rw [List.foldl_cons]
      apply ih hxs'
      split_ifs
      · apply xor_lt_pow hacc
        have hs := Nat.shiftLeft_lt (m := i) hb
        have hp : 2 ^ (d + i) ≤ 2 ^ (2 * d) :=
          Nat.pow_le_pow_right (by omega) (by omega)
        exact hs.trans_le hp
      · exact hacc

theorem rawProduct_lt (d a b : ℕ) (hb : b < 2 ^ d) :
    rawProduct d a b < 2 ^ (2 * d) := by
  unfold rawProduct
  apply raw_fold_lt d a b hb
  · intro i hi
    simpa using hi
  · exact Nat.pow_pos (by omega)

theorem reduce_eq_run (d modulus p : ℕ) :
    reduce d modulus p = run d modulus d p := by
  rw [run_eq_fold]
  rfl

theorem reduce_lt (d modulus p : ℕ) (hmodulus : modulus < 2 ^ (d + 1))
    (htop : modulus.testBit d = true) (hp : p < 2 ^ (2 * d)) :
    reduce d modulus p < 2 ^ d := by
  rw [reduce_eq_run]
  apply run_lt d modulus d p hmodulus htop
  simpa [two_mul] using hp

theorem mul_lt (d modulus a b : ℕ)
    (hmodulus : modulus < 2 ^ (d + 1))
    (htop : modulus.testBit d = true) (hb : b < 2 ^ d) :
    mul d modulus a b < 2 ^ d := by
  exact reduce_lt d modulus (rawProduct d a b) hmodulus htop
    (rawProduct_lt d a b hb)

#print axioms rawProduct_lt
#print axioms reduce_lt
#print axioms mul_lt

end CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge
