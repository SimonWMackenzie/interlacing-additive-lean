import CurrentAdditive.QuotientCoordinates

namespace CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge

open CurrentAdditive.FiniteFieldConstructor.BitPrinter

def boolCoeff (b : Bool) : ZMod 2 := if b then 1 else 0

theorem boolCoeff_xor (a b : Bool) :
    boolCoeff (a ^^ b) = boolCoeff a + boolCoeff b :=
  bit_xor_add a b

theorem boolCoeff_and (a b : Bool) :
    boolCoeff (a && b) = boolCoeff a * boolCoeff b := by
  cases a <;> cases b <;> decide

private theorem fold_dot_coeff (xs : List ℕ) (x z : ℕ) (acc : Bool) :
    boolCoeff
        (xs.foldl (fun a i => a ^^ (x.testBit i && z.testBit i)) acc) =
      boolCoeff acc +
        (xs.map fun i => boolCoeff (x.testBit i) * boolCoeff (z.testBit i)).sum := by
  induction xs generalizing acc with
  | nil => simp
  | cons i xs ih =>
      rw [List.foldl_cons, ih]
      simp only [List.map_cons, List.sum_cons]
      rw [boolCoeff_xor, boolCoeff_and]
      ring

theorem dot_coeff (d x z : ℕ) :
    boolCoeff (dot d x z) =
      ∑ i : Fin d, boolCoeff (x.testBit i) * boolCoeff (z.testBit i) := by
  have h : boolCoeff (dot d x z) =
      ((List.range d).map fun i =>
        boolCoeff (x.testBit i) * boolCoeff (z.testBit i)).sum := by
    simpa [dot, boolCoeff] using fold_dot_coeff (List.range d) x z false
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range] at h
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ => boolCoeff (x.testBit i) * boolCoeff (z.testBit i)) d]
  exact h

theorem dot_eq_decide (d x z : ℕ) :
    dot d x z =
      decide ((∑ i : Fin d,
        boolCoeff (x.testBit i) * boolCoeff (z.testBit i)) = 1) := by
  calc
    dot d x z = decide (boolCoeff (dot d x z) = 1) := by
      cases hbit : dot d x z <;> simp [hbit, boolCoeff]
    _ = decide ((∑ i : Fin d,
        boolCoeff (x.testBit i) * boolCoeff (z.testBit i)) = 1) := by
      rw [dot_coeff]

#print axioms dot_eq_decide

end CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge
