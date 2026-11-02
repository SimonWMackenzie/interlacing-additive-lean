import CurrentAdditive.GenericGramBound
import CurrentAdditive.SequentialTotality

/-! Transfer the Gram bound to the exact pivot list returned by typed and
materialized Gauss--Jordan. -/

namespace CurrentAdditive.RationalBitBounds

open CurrentAdditive.SequentialTotality

abbrev PivotIndex {m k : Nat} (ps : List (Fin m × Fin k)) :=
  {p : Fin m × Fin k // p ∈ ps.toFinset}

def pivotLift {m k : Nat} (ps : List (Fin m × Fin k))
    (u : PivotIndex ps → ℚ) : Fin k → ℚ :=
  fun j => ∑ p : PivotIndex ps, if j = p.val.2 then u p else 0

theorem rowDot_pivotLift {m k : Nat}
    (C : Fin m → Fin k → ℚ) (ps : List (Fin m × Fin k))
    (u : PivotIndex ps → ℚ) (i : Fin m) :
    rowDot C (pivotLift ps u) i =
      ∑ p : PivotIndex ps, C i p.val.2 * u p := by
  simp only [rowDot, pivotLift, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [mul_ite, mul_zero]
  simp

theorem rowDot_typedCandidate_cross {m k : Nat}
    (C B : Fin m → Fin k → ℚ)
    (ps : List (Fin m × Fin k)) (f : Fin k) (i : Fin m) :
    rowDot C (typedCandidate B ps f) i =
      C i f - ∑ p ∈ ps.toFinset, C i p.2 * B p.1 f := by
  simp only [rowDot, typedCandidate, mul_sub, Finset.sum_sub_distrib,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [mul_ite, mul_one, mul_zero]
  simp

theorem pivot_rows_injective {m k : Nat}
    (ps : List (Fin m × Fin k))
    (hnodup : (ps.map Prod.fst).Nodup) :
    Function.Injective (fun p : PivotIndex ps => p.val.1) := by
  have hps : ps.Nodup := hnodup.of_map
  have hinj := (List.nodup_map_iff_inj_on hps).mp hnodup
  intro p q heq
  apply Subtype.ext
  exact hinj p.val (List.mem_toFinset.mp p.property)
    q.val (List.mem_toFinset.mp q.property) heq

theorem pivot_columns_injective {m k : Nat}
    (B : Fin m → Fin k → ℚ) (ps : List (Fin m × Fin k))
    (hunit : ∀ p ∈ ps, ∀ i : Fin m,
      B i p.2 = if i = p.1 then 1 else 0)
    (hnodup : (ps.map Prod.fst).Nodup) :
    Function.Injective (fun p : PivotIndex ps => p.val.2) := by
  have hrow := pivot_rows_injective ps hnodup
  intro p q hcol
  have hp := hunit p.val (List.mem_toFinset.mp p.property) p.val.1
  have hq := hunit q.val (List.mem_toFinset.mp q.property) p.val.1
  change p.val.2 = q.val.2 at hcol
  have hrows : p.val.1 = q.val.1 := by
    by_contra hne
    simp only [ite_true] at hp
    simp only [if_neg hne] at hq
    rw [hcol] at hp
    exact one_ne_zero (hp.symm.trans hq)
  exact hrow hrows

theorem pivot_columns_independent {m k : Nat}
    (A : Fin m → Fin k → ℚ) (B : Fin m → Fin k → ℚ)
    (ps : List (Fin m × Fin k))
    (hunit : ∀ p ∈ ps, ∀ i : Fin m,
      B i p.2 = if i = p.1 then 1 else 0)
    (hnodup : (ps.map Prod.fst).Nodup)
    (hker : ∀ z : Fin k → ℚ,
      (∀ i, rowDot B z i = 0) ↔ (∀ i, rowDot A z i = 0)) :
    Function.Injective
      (fun u : PivotIndex ps → ℚ =>
        fun i : Fin m => ∑ p : PivotIndex ps, A i p.val.2 * u p) := by
  let ι := PivotIndex ps
  have hrow := pivot_rows_injective ps hnodup
  intro u v huv
  have hA : ∀ i, rowDot A (pivotLift ps (fun p => u p - v p)) i = 0 := by
    intro i
    rw [rowDot_pivotLift]
    have hi := congrFun huv i
    change (∑ p : ι, A i p.val.2 * u p) =
      ∑ p : ι, A i p.val.2 * v p at hi
    calc
      (∑ p : ι, A i p.val.2 * (u p - v p)) =
          (∑ p : ι, A i p.val.2 * u p) -
            (∑ p : ι, A i p.val.2 * v p) := by
              simp [mul_sub, Finset.sum_sub_distrib]
      _ = 0 := sub_eq_zero.mpr hi
  have hB := (hker (pivotLift ps (fun p => u p - v p))).mpr hA
  funext p0
  have hi := hB p0.val.1
  rw [rowDot_pivotLift] at hi
  have hsingle :
      (∑ p : ι, B p0.val.1 p.val.2 * (u p - v p)) =
      u p0 - v p0 := by
    calc
      (∑ p : ι, B p0.val.1 p.val.2 * (u p - v p)) =
          ∑ p : ι, (if p0.val.1 = p.val.1 then 1 else 0) * (u p - v p) := by
            apply Finset.sum_congr rfl
            intro p _
            rw [hunit p.val (List.mem_toFinset.mp p.property) p0.val.1]
      _ = u p0 - v p0 := by
        simp [hrow.eq_iff]
  rw [hsingle] at hi
  exact sub_eq_zero.mp hi

theorem pivot_solution_component_bound {m k : Nat}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (B : Fin m → Fin k → ℚ)
    (ps : List (Fin m × Fin k)) (f : Fin k)
    (hzeroOne : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hunit : ∀ p ∈ ps, ∀ i : Fin m,
      B i p.2 = if i = p.1 then 1 else 0)
    (hnodup : (ps.map Prod.fst).Nodup)
    (hker : ∀ z : Fin k → ℚ,
      (∀ i, rowDot B z i = 0) ↔
        (∀ i, rowDot (fun i j => (A i j : ℚ)) z i = 0))
    (hcandidate : ∀ i,
      rowDot (fun i j => (A i j : ℚ))
        (typedCandidate B ps f) i = 0)
    (p0 : PivotIndex ps) :
    (B p0.val.1 f).num.natAbs ≤
        (Fintype.card (PivotIndex ps)).factorial *
          m ^ Fintype.card (PivotIndex ps) ∧
      (B p0.val.1 f).den ≤
        (Fintype.card (PivotIndex ps)).factorial *
          m ^ Fintype.card (PivotIndex ps) := by
  let ι := PivotIndex ps
  let C : Matrix (Fin m) ι ℤ := fun i p => A i p.val.2
  let b : Fin m → ℤ := fun i => A i f
  let x : ι → ℚ := fun p => B p.val.1 f
  have hC : ∀ i p, C i p = 0 ∨ C i p = 1 :=
    fun i p => hzeroOne i p.val.2
  have hb : ∀ i, b i = 0 ∨ b i = 1 :=
    fun i => hzeroOne i f
  have hinj : Function.Injective
      (C.map fun t : ℤ => (t : ℚ)).mulVec := by
    have hi := pivot_columns_independent
      (fun i j => (A i j : ℚ)) B ps hunit hnodup hker
    simpa only [C, Matrix.mulVec, dotProduct, Matrix.map_apply] using hi
  have hAx : (C.map fun t : ℤ => (t : ℚ)).mulVec x =
      fun i => (b i : ℚ) := by
    funext i
    have hcross := rowDot_typedCandidate_cross
      (fun i j => (A i j : ℚ)) B ps f i
    rw [hcandidate i] at hcross
    have hsum : (∑ p : ι, (A i p.val.2 : ℚ) * B p.val.1 f) =
        ∑ p ∈ ps.toFinset, (A i p.2 : ℚ) * B p.1 f := by
      exact (Finset.sum_subtype ps.toFinset (fun p => Iff.rfl)
        (fun p => (A i p.2 : ℚ) * B p.1 f)).symm
    change (∑ p : ι, (A i p.val.2 : ℚ) * B p.val.1 f) = (A i f : ℚ)
    rw [hsum]
    linarith
  exact generic_zero_one_solution_bound m C b x hC hb hinj hAx p0

/-- The coefficients read from the exact typed Gauss--Jordan output obey the
Gram/Cramer bound, for every free column. By `echelonMaterialized_eq`, this is
also the mathematical value stored by the eagerly materialized array loop. -/
theorem echelon_pivot_coefficient_bound {m k : Nat}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (hzeroOne : ∀ i j, A i j = 0 ∨ A i j = 1)
    (f : Fin k)
    (hfree : f ∉
      ((echelonTyped (fun i j => (A i j : ℚ)) 0 0 k).2.map Prod.snd))
    (p0 : PivotIndex (echelonTyped (fun i j => (A i j : ℚ)) 0 0 k).2) :
    let out := echelonTyped (fun i j => (A i j : ℚ)) 0 0 k
    (out.1 p0.val.1 f).num.natAbs ≤
        (Fintype.card (PivotIndex out.2)).factorial *
          m ^ Fintype.card (PivotIndex out.2) ∧
      (out.1 p0.val.1 f).den ≤
        (Fintype.card (PivotIndex out.2)).factorial *
          m ^ Fintype.card (PivotIndex out.2) := by
  let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
  let out := echelonTyped Aq 0 0 k
  let B := out.1
  let ps := out.2
  have hbelow : BelowZero Aq 0 0 := by
    intro i j _ hj
    omega
  have hstair := (echelonTyped_staircase Aq 0 0 k (by simp) hbelow).1
  have hunit := echelonTyped_pivot_units Aq 0 0 k (by simp) hbelow
  have hrows := echelonTyped_pivot_rows Aq 0 0 k (by omega)
  have hnodup := echelonTyped_pivot_rows_nodup Aq 0 0 k
  have hred : ∀ i, rowDot B (typedCandidate B ps f) i = 0 := by
    have h := typedCandidate_reduced_kernel B ps f
      (by simpa [Aq, out, ps] using hfree)
      (by simpa [B, ps, out] using hunit)
      (by
        intro i hi j
        exact hstair i j (by simpa [ps, out] using hi) (by omega))
      (by
        intro i hi
        have hh := hrows.2 i (by omega) (by simpa [ps, out] using hi)
        simpa [ps, out] using hh)
      (by simpa [ps, out] using hnodup)
    exact h.2
  have hcand : ∀ i, rowDot Aq (typedCandidate B ps f) i = 0 :=
    (echelonTyped_kernel_iff Aq 0 0 k (typedCandidate B ps f)).mp hred
  exact pivot_solution_component_bound A B ps f hzeroOne
    (by simpa [Aq, out, B, ps] using hunit)
    (by simpa [Aq, out, ps] using hnodup)
    (by
      intro z
      simpa [Aq, out, B] using (echelonTyped_kernel_iff Aq 0 0 k z))
    (by simpa [Aq] using hcand) p0

end CurrentAdditive.RationalBitBounds
