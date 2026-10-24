import CurrentAdditive.HadamardSupport

set_option maxHeartbeats 1000000

namespace CurrentAdditive.HadamardSupport

open Matrix CurrentAdditive.RationalBitBounds

/-- An invertible zero-one minor represents its unique rational solution by
one positive denominator. Neither the denominator nor any numerator has been
squared to avoid its sign. Their squares obey the exact Hadamard envelope. -/
theorem square_zero_one_cramer_normalization (r : Nat)
    (A : Matrix (Fin r) (Fin r) ℤ) (b : Fin r → ℤ) (x : Fin r → ℚ)
    (hA : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hb : ∀ i, b i = 0 ∨ b i = 1)
    (hdet : A.det ≠ 0)
    (hAx : (A.map fun t : ℤ => (t : ℚ)).mulVec x = fun i => (b i : ℚ)) :
    ∃ (D : ℕ) (z : Fin r → ℤ),
      0 < D ∧ D ^ 2 ≤ r ^ r ∧
      (∀ j, (z j).natAbs ^ 2 ≤ r ^ r) ∧
      (∀ j, x j = (z j : ℚ) / (D : ℚ)) := by
  let D : ℕ := A.det.natAbs
  let z : Fin r → ℤ := fun j =>
    if 0 < A.det then (A.updateCol j b).det else -(A.updateCol j b).det
  have hD : 0 < D := Int.natAbs_pos.mpr hdet
  have hAqdet : (A.map fun t : ℤ => (t : ℚ)).det ≠ 0 := by
    rw [← Int.cast_det]
    exact_mod_cast hdet
  refine ⟨D, z, hD, det_zero_one_natAbs_sq_le_pow r A hA, ?_, ?_⟩
  · intro j
    have hU : ∀ i k, (A.updateCol j b) i k = 0 ∨ (A.updateCol j b) i k = 1 := by
      intro i k
      rw [Matrix.updateCol_apply]
      split_ifs
      · exact hb i
      · exact hA i k
    have hB := det_zero_one_natAbs_sq_le_pow r (A.updateCol j b) hU
    simpa only [z, apply_ite Int.natAbs, Int.natAbs_neg, ite_self] using hB
  · intro j
    have hU : ((A.map fun t : ℤ => (t : ℚ)).updateCol j
          (fun i => (b i : ℚ))).det = ((A.updateCol j b).det : ℚ) := by
      have hmap : (A.updateCol j b).map (fun t : ℤ => (t : ℚ)) =
          (A.map fun t : ℤ => (t : ℚ)).updateCol j (fun i => (b i : ℚ)) := by
        ext i k
        simp [Matrix.updateCol_apply]
      rw [← hmap, ← Int.cast_det]
    have hx := cramer_solution r (A.map fun t : ℤ => (t : ℚ))
      (fun i => (b i : ℚ)) x hAqdet hAx j
    rw [hU, ← Int.cast_det] at hx
    rw [hx]
    by_cases hp : 0 < A.det
    · have hDcast : (D : ℚ) = (A.det : ℚ) := by
        change ((A.det.natAbs : ℕ) : ℚ) = (A.det : ℚ)
        rw [Nat.cast_natAbs, abs_of_pos hp]
      simp only [z, if_pos hp, hDcast]
    · have hn : A.det < 0 := lt_of_le_of_ne (le_of_not_gt hp) hdet
      have hDcast : (D : ℚ) = -(A.det : ℚ) := by
        change ((A.det.natAbs : ℕ) : ℚ) = -(A.det : ℚ)
        rw [Nat.cast_natAbs, abs_of_neg hn, Int.cast_neg]
      simp only [z, if_neg hp, Int.cast_neg, hDcast, neg_div_neg_eq]

/-- Independent columns admit a square invertible matrix obtained only by
selecting original rows; no Gram products alter the zero-one entries. -/
theorem exists_invertible_row_selection {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : Nat) (A : Matrix (Fin m) ι ℚ)
    (hinj : Function.Injective A.mulVec) :
    ∃ rows : ι → Fin m, Function.Injective rows ∧
      (A.submatrix rows id).det ≠ 0 := by
  classical
  have hrank : A.rank = Fintype.card ι := by
    rw [Matrix.rank]
    simpa using (LinearMap.finrank_range_of_inj
      (show Function.Injective A.mulVecLin from hinj))
  have htop : Submodule.span ℚ (Set.range A.row) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← A.rank_eq_finrank_span_row, hrank]
    simp
  obtain ⟨κ, rows, hrows, hspan, hli⟩ := exists_linearIndependent' ℚ A.row
  letI : Finite κ := Finite.of_injective rows hrows
  letI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = Fintype.card ι := by
    have h := linearIndependent_iff_card_eq_finrank_span.mp hli
    change Fintype.card κ = Module.finrank ℚ
      (Submodule.span ℚ (Set.range (A.row ∘ rows))) at h
    rw [hspan, htop] at h
    simpa using h
  let e : ι ≃ κ := Fintype.equivOfCardEq hcard.symm
  refine ⟨rows ∘ e, hrows.comp e.injective, ?_⟩
  have hli' : LinearIndependent ℚ (A.submatrix (rows ∘ e) id).row := by
    exact hli.comp e e.injective
  exact isUnit_iff_ne_zero.mp
    (((A.submatrix (rows ∘ e) id).isUnit_iff_isUnit_det).mp
      (Matrix.linearIndependent_rows_iff_isUnit.mp hli'))

#print axioms square_zero_one_cramer_normalization
#print axioms exists_invertible_row_selection

end CurrentAdditive.HadamardSupport
