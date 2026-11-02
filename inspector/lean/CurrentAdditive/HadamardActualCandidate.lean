import CurrentAdditive.HadamardSelectedRows
import CurrentAdditive.CandidateBitsLocal
import CurrentAdditive.MaterializedGauss

set_option maxHeartbeats 1000000

namespace CurrentAdditive.HadamardSupport

open CurrentAdditive.RationalBitBounds
open CurrentAdditive.SequentialTotality
open CurrentAdditive.MaterializedGauss

/-- The exact Cramer normalization of the actual pivot solution. -/
theorem pivot_solution_hadamard {m k : Nat}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (B : Fin m → Fin k → ℚ)
    (ps : List (Fin m × Fin k)) (f : Fin k)
    (hzeroOne : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hunit : ∀ p ∈ ps, ∀ i : Fin m,
      B i p.2 = if i = p.1 then 1 else 0)
    (hnodup : (ps.map Prod.fst).Nodup)
    (hker : ∀ v : Fin k → ℚ,
      (∀ i, rowDot B v i = 0) ↔
        (∀ i, rowDot (fun i j => (A i j : ℚ)) v i = 0))
    (hcandidate : ∀ i,
      rowDot (fun i j => (A i j : ℚ)) (typedCandidate B ps f) i = 0) :
    ∃ (D : ℕ) (z : PivotIndex ps → ℤ),
      0 < D ∧
      D ^ 2 ≤ Fintype.card (PivotIndex ps) ^ Fintype.card (PivotIndex ps) ∧
      (∀ p, (z p).natAbs ^ 2 ≤
        Fintype.card (PivotIndex ps) ^ Fintype.card (PivotIndex ps)) ∧
      (∀ p, B p.val.1 f = (z p : ℚ) / (D : ℚ)) := by
  let ι := PivotIndex ps
  let C : Matrix (Fin m) ι ℤ := fun i p => A i p.val.2
  let b : Fin m → ℤ := fun i => A i f
  let x : ι → ℚ := fun p => B p.val.1 f
  have hC : ∀ i p, C i p = 0 ∨ C i p = 1 := fun i p => hzeroOne i p.val.2
  have hb : ∀ i, b i = 0 ∨ b i = 1 := fun i => hzeroOne i f
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
  exact zero_one_independent_hadamard_normalization m C b x hC hb hinj hAx

/-- The selected free-column candidate is a kernel vector even when the
number of columns is already at most the number of feature rows. -/
theorem echelon_candidate_kernel {m k : Nat}
    (A : Fin m → Fin k → ℚ) (f : Fin k)
    (hfree : f ∉ ((echelonTyped A 0 0 k).2.map Prod.snd)) :
    let out := echelonTyped A 0 0 k
    ∀ i, rowDot A (typedCandidate out.1 out.2 f) i = 0 := by
  let out := echelonTyped A 0 0 k
  have hbelow : BelowZero A 0 0 := by
    intro i j _ hj
    omega
  have hstair := (echelonTyped_staircase A 0 0 k (by simp) hbelow).1
  have hunit := echelonTyped_pivot_units A 0 0 k (by simp) hbelow
  have hrows := echelonTyped_pivot_rows A 0 0 k (by omega)
  have hnodup := echelonTyped_pivot_rows_nodup A 0 0 k
  have hred := typedCandidate_reduced_kernel out.1 out.2 f
    (by simpa [out] using hfree)
    (by simpa [out] using hunit)
    (by
      intro i hi j
      exact hstair i j (by simpa [out] using hi) (by omega))
    (by
      intro i hi
      have hh := hrows.2 i (by omega) (by simpa [out] using hi)
      simpa [out] using hh)
    (by simpa [out] using hnodup)
  exact (echelonTyped_kernel_iff A 0 0 k (typedCandidate out.1 out.2 f)).mp hred.2

theorem echelon_pivot_hadamard {m k : Nat}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (hzeroOne : ∀ i j, A i j = 0 ∨ A i j = 1)
    (f : Fin k)
    (hfree : f ∉
      ((echelonTyped (fun i j => (A i j : ℚ)) 0 0 k).2.map Prod.snd)) :
    let out := echelonTyped (fun i j => (A i j : ℚ)) 0 0 k
    ∃ (D : ℕ) (z : PivotIndex out.2 → ℤ),
      0 < D ∧
      D ^ 2 ≤ Fintype.card (PivotIndex out.2) ^ Fintype.card (PivotIndex out.2) ∧
      (∀ p, (z p).natAbs ^ 2 ≤
        Fintype.card (PivotIndex out.2) ^ Fintype.card (PivotIndex out.2)) ∧
      (∀ p, out.1 p.val.1 f = (z p : ℚ) / (D : ℚ)) := by
  let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
  let out := echelonTyped Aq 0 0 k
  have hbelow : BelowZero Aq 0 0 := by
    intro i j _ hj
    omega
  have hunit := echelonTyped_pivot_units Aq 0 0 k (by simp) hbelow
  have hnodup := echelonTyped_pivot_rows_nodup Aq 0 0 k
  exact pivot_solution_hadamard A out.1 out.2 f hzeroOne
    (by simpa [Aq, out] using hunit)
    (by simpa [Aq, out] using hnodup)
    (by
      intro v
      simpa [Aq, out] using (echelonTyped_kernel_iff Aq 0 0 k v))
    (echelon_candidate_kernel Aq f hfree)

/-- Lift the normalized pivot coefficients to precisely the actual candidate.
The positive free coefficient is the shared denominator. -/
theorem typedCandidate_hadamard_coefficients {m k : Nat}
    (B : Fin m → Fin k → ℚ) (ps : List (Fin m × Fin k))
    (f : Fin k) (hfree : f ∉ ps.map Prod.snd)
    (hcol : Function.Injective (fun p : PivotIndex ps => p.val.2))
    (D H : ℕ) (hD : 0 < D) (hDH : D ^ 2 ≤ H)
    (z : PivotIndex ps → ℤ)
    (hz : ∀ p, (z p).natAbs ^ 2 ≤ H)
    (hrep : ∀ p, B p.val.1 f = (z p : ℚ) / (D : ℚ)) :
    ∃ coeff : Fin k → ℤ,
      (∀ j, (coeff j).natAbs ^ 2 ≤ H) ∧
      (∀ j, typedCandidate B ps f j = (coeff j : ℚ) / (D : ℚ)) ∧
      coeff f = (D : ℤ) ∧
      (∀ j, j ≠ f → j ∉ ps.map Prod.snd → coeff j = 0) := by
  classical
  have hpoint : ∀ j : Fin k, ∃ c : ℤ,
      c.natAbs ^ 2 ≤ H ∧ typedCandidate B ps f j = (c : ℚ) / (D : ℚ) := by
    intro j
    by_cases hjf : j = f
    · subst j
      refine ⟨(D : ℤ), by simpa using hDH, ?_⟩
      rw [typedCandidate_at_free B ps f hfree]
      have hdq : (D : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
      field_simp
      norm_cast
    · by_cases hjp : j ∈ ps.map Prod.snd
      · obtain ⟨p, hp, hcolp⟩ := List.mem_map.mp hjp
        let p0 : PivotIndex ps := ⟨p, List.mem_toFinset.mpr hp⟩
        refine ⟨-z p0, by simpa using hz p0, ?_⟩
        have hj : j = p0.val.2 := hcolp.symm
        subst j
        rw [typedCandidate_at_pivot B ps f hfree hcol p0, hrep p0]
        push_cast
        ring
      · refine ⟨0, by simp, ?_⟩
        rw [typedCandidate_off_pivots B ps f j hjf hjp]
        simp
  let coeff : Fin k → ℤ := fun j => Classical.choose (hpoint j)
  have hc : ∀ j, typedCandidate B ps f j = (coeff j : ℚ) / (D : ℚ) :=
    fun j => (Classical.choose_spec (hpoint j)).2
  have hdq : (D : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  refine ⟨coeff, fun j => (Classical.choose_spec (hpoint j)).1, hc, ?_, ?_⟩
  · have hf := hc f
    rw [typedCandidate_at_free B ps f hfree] at hf
    have hcf : (coeff f : ℚ) = (D : ℚ) := by
      exact (div_eq_one_iff_eq hdq).mp hf.symm
    exact_mod_cast hcf
  · intro j hjf hjp
    have hj := hc j
    rw [typedCandidate_off_pivots B ps f j hjf hjp] at hj
    have hzq : (coeff j : ℚ) = 0 := (div_eq_zero_iff).mp hj.symm |>.resolve_right hdq
    exact_mod_cast hzq

theorem echelon_candidate_hadamard {m k : Nat}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (hzeroOne : ∀ i j, A i j = 0 ∨ A i j = 1)
    (f : Fin k)
    (hfree : f ∉
      ((echelonTyped (fun i j => (A i j : ℚ)) 0 0 k).2.map Prod.snd)) :
    let out := echelonTyped (fun i j => (A i j : ℚ)) 0 0 k
    let r := Fintype.card (PivotIndex out.2)
    ∃ (D : ℕ) (coeff : Fin k → ℤ),
      0 < D ∧ D ^ 2 ≤ r ^ r ∧
      (∀ j, (coeff j).natAbs ^ 2 ≤ r ^ r) ∧
      (∀ j, typedCandidate out.1 out.2 f j = (coeff j : ℚ) / (D : ℚ)) ∧
      coeff f = (D : ℤ) ∧
      (∀ j, j ≠ f → j ∉ out.2.map Prod.snd → coeff j = 0) := by
  let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
  let out := echelonTyped Aq 0 0 k
  obtain ⟨D, z, hD, hDH, hz, hrep⟩ := echelon_pivot_hadamard A hzeroOne f hfree
  have hbelow : BelowZero Aq 0 0 := by
    intro i j _ hj
    omega
  have hunit := echelonTyped_pivot_units Aq 0 0 k (by simp) hbelow
  have hnodup := echelonTyped_pivot_rows_nodup Aq 0 0 k
  have hcol : Function.Injective (fun p : PivotIndex out.2 => p.val.2) :=
    pivot_columns_injective out.1 out.2
      (by simpa [out] using hunit) (by simpa [out] using hnodup)
  obtain ⟨coeff, hcoeff, hcoeffrep, hfreecoeff, hsupport⟩ :=
    typedCandidate_hadamard_coefficients out.1 out.2 f hfree hcol D _ hD hDH z hz hrep
  exact ⟨D, coeff, hD, hDH, hcoeff, hcoeffrep, hfreecoeff, hsupport⟩

/-- Exact Hadamard normalization of every successful return from the actual
deterministic, materialized, first-free-column implementation. -/
theorem materialized_dependence_hadamard {m k : Nat}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (hzeroOne : ∀ i j, A i j = 0 ∨ A i j = 1)
    (x : Fin k → ℚ)
    (hx : dependenceMaterialized (fun i j => (A i j : ℚ)) = some x) :
    let out := echelonTyped (fun i j => (A i j : ℚ)) 0 0 k
    let r := Fintype.card (PivotIndex out.2)
    ∃ (f : Fin k) (D : ℕ) (coeff : Fin k → ℤ),
      typedFree out.2 = some f ∧
      0 < D ∧ D ^ 2 ≤ r ^ r ∧
      (∀ j, (coeff j).natAbs ^ 2 ≤ r ^ r) ∧
      (∀ j, x j = (coeff j : ℚ) / (D : ℚ)) ∧
      coeff f = (D : ℤ) ∧
      (∀ j, j ≠ f → j ∉ out.2.map Prod.snd → coeff j = 0) := by
  let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
  let out := echelonTyped Aq 0 0 k
  rw [dependenceMaterialized_eq] at hx
  change (typedFree out.2).map (typedCandidate out.1 out.2) = some x at hx
  cases hf : typedFree out.2 with
  | none => simp [hf] at hx
  | some f =>
      have hxval : x = typedCandidate out.1 out.2 f := by
        simpa [hf] using hx.symm
      have hfree : f ∉ out.2.map Prod.snd := typedFree_spec out.2 f hf
      obtain ⟨D, coeff, hD, hDB, hcoeffB, hrep, hfc, hs⟩ :=
        echelon_candidate_hadamard A hzeroOne f (by simpa [Aq, out] using hfree)
      refine ⟨f, D, coeff, hf, hD, hDB, hcoeffB, ?_, hfc, hs⟩
      intro j
      rw [hxval]
      exact hrep j

#print axioms pivot_solution_hadamard
#print axioms echelon_candidate_kernel
#print axioms echelon_pivot_hadamard
#print axioms typedCandidate_hadamard_coefficients
#print axioms echelon_candidate_hadamard
#print axioms materialized_dependence_hadamard

end CurrentAdditive.HadamardSupport
