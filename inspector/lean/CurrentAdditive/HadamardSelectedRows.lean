import CurrentAdditive.HadamardNormalization

set_option maxHeartbeats 1000000

namespace CurrentAdditive.HadamardSupport

open Matrix

/-- The exact determinant envelope for any finite common row/column type. -/
theorem generic_det_zero_one_natAbs_sq_le_pow {ι : Type*}
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ)
    (hA : ∀ i j, A i j = 0 ∨ A i j = 1) :
    A.det.natAbs ^ 2 ≤ Fintype.card ι ^ Fintype.card ι := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  simpa only [Matrix.det_submatrix_equiv_self] using
    det_zero_one_natAbs_sq_le_pow (Fintype.card ι) (A.submatrix e e)
      (fun i j => hA (e i) (e j))

/-- A generic-index version of the positive, unsquared determinant scaling. -/
theorem generic_square_zero_one_cramer_normalization {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (b : ι → ℤ) (x : ι → ℚ)
    (hA : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hb : ∀ i, b i = 0 ∨ b i = 1)
    (hdet : A.det ≠ 0)
    (hAx : (A.map fun t : ℤ => (t : ℚ)).mulVec x = fun i => (b i : ℚ)) :
    ∃ (D : ℕ) (z : ι → ℤ),
      0 < D ∧ D ^ 2 ≤ Fintype.card ι ^ Fintype.card ι ∧
      (∀ j, (z j).natAbs ^ 2 ≤ Fintype.card ι ^ Fintype.card ι) ∧
      (∀ j, x j = (z j : ℚ) / (D : ℚ)) := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let B := A.submatrix e e
  have hBdet : B.det ≠ 0 := by simpa only [B, Matrix.det_submatrix_equiv_self]
    using hdet
  have hBx : (B.map fun t : ℤ => (t : ℚ)).mulVec (x ∘ e) =
      fun i => (b (e i) : ℚ) := by
    funext i
    change (∑ j : Fin (Fintype.card ι), (A (e i) (e j) : ℚ) * x (e j)) = _
    rw [show (∑ j : Fin (Fintype.card ι), (A (e i) (e j) : ℚ) * x (e j)) =
      ∑ j : ι, (A (e i) j : ℚ) * x j from
      e.sum_comp (fun j => (A (e i) j : ℚ) * x j)]
    exact congrFun hAx (e i)
  obtain ⟨D, z, hD, hDB, hz, hrep⟩ :=
    square_zero_one_cramer_normalization (Fintype.card ι) B (b ∘ e) (x ∘ e)
      (fun i j => hA (e i) (e j)) (fun i => hb (e i)) hBdet hBx
  refine ⟨D, z ∘ e.symm, hD, hDB, fun j => hz (e.symm j), ?_⟩
  intro j
  simpa only [Function.comp_apply, e.apply_symm_apply] using hrep (e.symm j)

/-- A solution on independent zero-one columns has one positive integer
scaling with the manuscript's exact rank-sensitive coefficient bound. The
solution `x` is an input, so this applies to the actual Gauss solution rather
than choosing an unrelated dependence. -/
theorem zero_one_independent_hadamard_normalization {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (m : Nat) (A : Matrix (Fin m) ι ℤ) (b : Fin m → ℤ) (x : ι → ℚ)
    (hA : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hb : ∀ i, b i = 0 ∨ b i = 1)
    (hinj : Function.Injective (A.map fun t : ℤ => (t : ℚ)).mulVec)
    (hAx : (A.map fun t : ℤ => (t : ℚ)).mulVec x = fun i => (b i : ℚ)) :
    ∃ (D : ℕ) (z : ι → ℤ),
      0 < D ∧ D ^ 2 ≤ Fintype.card ι ^ Fintype.card ι ∧
      (∀ j, (z j).natAbs ^ 2 ≤ Fintype.card ι ^ Fintype.card ι) ∧
      (∀ j, x j = (z j : ℚ) / (D : ℚ)) := by
  classical
  obtain ⟨rows, _hrows, hdetq⟩ :=
    exists_invertible_row_selection m (A.map fun t : ℤ => (t : ℚ)) hinj
  let S : Matrix ι ι ℤ := A.submatrix rows id
  have hmap : S.map (fun t : ℤ => (t : ℚ)) =
      (A.map fun t : ℤ => (t : ℚ)).submatrix rows id := rfl
  have hdet : S.det ≠ 0 := by
    intro h
    apply hdetq
    rw [← hmap, ← Int.cast_det, h]
    simp
  have hSx : (S.map fun t : ℤ => (t : ℚ)).mulVec x =
      fun i => (b (rows i) : ℚ) := by
    funext i
    exact congrFun hAx (rows i)
  exact generic_square_zero_one_cramer_normalization S (b ∘ rows) x
    (fun i j => hA (rows i) j) (fun i => hb (rows i)) hdet hSx

#print axioms generic_det_zero_one_natAbs_sq_le_pow
#print axioms generic_square_zero_one_cramer_normalization
#print axioms zero_one_independent_hadamard_normalization

end CurrentAdditive.HadamardSupport
