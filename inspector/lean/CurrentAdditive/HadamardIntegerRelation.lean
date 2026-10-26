import CurrentAdditive.HadamardActualCandidate

set_option maxHeartbeats 1000000

namespace CurrentAdditive.HadamardSupport

open CurrentAdditive.RationalBitBounds
open CurrentAdditive.SequentialTotality
open CurrentAdditive.MaterializedGauss

/-- Scaling one rational kernel vector by a positive common denominator
gives exactly one integer kernel vector, on the same original columns. -/
theorem integer_kernel_of_common_scaling {m k : Nat}
    (A : Matrix (Fin m) (Fin k) ℤ) (x : Fin k → ℚ)
    (D : ℕ) (coeff : Fin k → ℤ) (hD : 0 < D)
    (hrep : ∀ j, x j = (coeff j : ℚ) / (D : ℚ))
    (hker : ∀ i, rowDot (fun i j => (A i j : ℚ)) x i = 0) :
    (∀ j, (coeff j : ℚ) = (D : ℚ) * x j) ∧ A.mulVec coeff = 0 := by
  have hdq : (D : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  have hscale : ∀ j, (coeff j : ℚ) = (D : ℚ) * x j := by
    intro j
    calc
      (coeff j : ℚ) = x j * (D : ℚ) := ((eq_div_iff hdq).mp (hrep j)).symm
      _ = (D : ℚ) * x j := mul_comm _ _
  refine ⟨hscale, ?_⟩
  funext i
  have hq : ((A.mulVec coeff i : ℤ) : ℚ) = 0 := by
    change ((∑ j, A i j * coeff j : ℤ) : ℚ) = 0
    push_cast
    calc
      (∑ j, (A i j : ℚ) * (coeff j : ℚ)) =
          ∑ j, (D : ℚ) * ((A i j : ℚ) * x j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hscale]
        ring
      _ = (D : ℚ) * rowDot (fun i j => (A i j : ℚ)) x i := by
        simp only [rowDot, Finset.mul_sum]
      _ = 0 := by rw [hker, mul_zero]
  exact_mod_cast hq

/-- A successful actual materialized call admits the manuscript's nonzero
integer relation, with a positive free coefficient and exact Hadamard size.
This theorem quantifies over the returned vector itself, with no overfull
matrix assumption and no alternative relation supplied as a premise. -/
theorem materialized_integer_hadamard_relation {m k : Nat}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (hzeroOne : ∀ i j, A i j = 0 ∨ A i j = 1)
    (x : Fin k → ℚ)
    (hx : dependenceMaterialized (fun i j => (A i j : ℚ)) = some x) :
    let out := echelonTyped (fun i j => (A i j : ℚ)) 0 0 k
    let r := Fintype.card (PivotIndex out.2)
    r ≤ m ∧ ∃ (f : Fin k) (D : ℕ) (coeff : Fin k → ℤ),
      typedFree out.2 = some f ∧
      0 < D ∧ D ^ 2 ≤ r ^ r ∧
      (∀ j, (coeff j).natAbs ^ 2 ≤ r ^ r) ∧
      (∀ j, x j = (coeff j : ℚ) / (D : ℚ)) ∧
      (∀ j, (coeff j : ℚ) = (D : ℚ) * x j) ∧
      A.mulVec coeff = 0 ∧
      coeff f = (D : ℤ) ∧ coeff f ≠ 0 ∧
      (∀ j, j ≠ f → j ∉ out.2.map Prod.snd → coeff j = 0) := by
  let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
  let out := echelonTyped Aq 0 0 k
  have hn := echelonTyped_pivot_rows_nodup Aq 0 0 k
  have hi := pivot_rows_injective out.2 (by simpa [out] using hn)
  have hr : Fintype.card (PivotIndex out.2) ≤ m := by
    exact (Fintype.card_le_of_injective _ hi).trans (by simp)
  obtain ⟨f, D, coeff, hf, hD, hDB, hcoeff, hrep, hfc, hs⟩ :=
    materialized_dependence_hadamard A hzeroOne x hx
  have hfree : f ∉ out.2.map Prod.snd := typedFree_spec out.2 f hf
  have hxval : x = typedCandidate out.1 out.2 f := by
    rw [dependenceMaterialized_eq] at hx
    change (typedFree out.2).map (typedCandidate out.1 out.2) = some x at hx
    have hf' : typedFree out.2 = some f := hf
    have hh : some (typedCandidate out.1 out.2 f) = some x := by
      simpa only [hf', Option.map_some] using hx
    exact (Option.some.inj hh).symm
  have hker : ∀ i, rowDot Aq x i = 0 := by
    rw [hxval]
    exact echelon_candidate_kernel Aq f hfree
  obtain ⟨hscale, hz⟩ := integer_kernel_of_common_scaling A x D coeff hD hrep hker
  refine ⟨hr, f, D, coeff, hf, hD, hDB, hcoeff, hrep, hscale, hz, hfc, ?_, hs⟩
  rw [hfc]
  exact_mod_cast Nat.ne_of_gt hD

#print axioms integer_kernel_of_common_scaling
#print axioms materialized_integer_hadamard_relation

end CurrentAdditive.HadamardSupport
