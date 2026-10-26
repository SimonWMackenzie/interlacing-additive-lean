import CurrentAdditive.SharedGramDenominator
import CurrentAdditive.CandidateBitsLocal
import CurrentAdditive.MaterializedGauss

set_option maxHeartbeats 1000000

namespace CurrentAdditive.RationalCandidateCompletion

open CurrentAdditive.RationalBitBounds
open CurrentAdditive.SequentialTotality
open CurrentAdditive.MaterializedGauss
open CurrentAdditive.SequentialArrayBridge
open CurrentAdditive.SequentialCode

theorem typedCandidate_shared_coefficients {m k : Nat}
    (B : Fin m → Fin k → ℚ) (ps : List (Fin m × Fin k))
    (f : Fin k) (hfree : f ∉ ps.map Prod.snd)
    (hcol : Function.Injective (fun p : PivotIndex ps => p.val.2))
    (D H : ℕ) (hD : 0 < D) (hDH : D ≤ H)
    (z : PivotIndex ps → ℤ)
    (hz : ∀ p, (z p).natAbs ≤ H)
    (hrep : ∀ p, B p.val.1 f = (z p : ℚ) / (D : ℚ)) :
    ∃ coeff : Fin k → ℤ,
      (∀ j, (coeff j).natAbs ≤ H) ∧
      (∀ j, typedCandidate B ps f j = (coeff j : ℚ) / (D : ℚ)) := by
  classical
  have hpoint : ∀ j : Fin k, ∃ c : ℤ,
      c.natAbs ≤ H ∧ typedCandidate B ps f j = (c : ℚ) / (D : ℚ) := by
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
  exact ⟨coeff,
    fun j => (Classical.choose_spec (hpoint j)).1,
    fun j => (Classical.choose_spec (hpoint j)).2⟩

theorem echelon_candidate_shared {m k : Nat}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (hzeroOne : ∀ i j, A i j = 0 ∨ A i j = 1)
    (f : Fin k)
    (hfree : f ∉
      ((echelonTyped (fun i j => (A i j : ℚ)) 0 0 k).2.map Prod.snd)) :
    let out := echelonTyped (fun i j => (A i j : ℚ)) 0 0 k
    ∃ (D : ℕ) (coeff : Fin k → ℤ),
      0 < D ∧
      D ≤ ((Fintype.card (PivotIndex out.2)).factorial *
        m ^ Fintype.card (PivotIndex out.2)) ^ 2 ∧
      (∀ j, (coeff j).natAbs ≤
        ((Fintype.card (PivotIndex out.2)).factorial *
          m ^ Fintype.card (PivotIndex out.2)) ^ 2) ∧
      (∀ j, typedCandidate out.1 out.2 f j =
        (coeff j : ℚ) / (D : ℚ)) := by
  let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
  let out := echelonTyped Aq 0 0 k
  let B := out.1
  let ps := out.2
  obtain ⟨D, z, hD, hDH, hz, hrep⟩ :=
    echelon_pivot_shared A hzeroOne f hfree
  have hbelow : BelowZero Aq 0 0 := by
    intro i j _ hj
    omega
  have hunit := echelonTyped_pivot_units Aq 0 0 k (by simp) hbelow
  have hnodup := echelonTyped_pivot_rows_nodup Aq 0 0 k
  have hcol : Function.Injective (fun p : PivotIndex ps => p.val.2) :=
    pivot_columns_injective B ps
      (by simpa [B, ps, out] using hunit)
      (by simpa [ps, out] using hnodup)
  obtain ⟨coeff, hcoeff, hcoeffrep⟩ :=
    typedCandidate_shared_coefficients B ps f
      (by simpa [ps, out, Aq] using hfree) hcol D _ hD hDH z hz hrep
  exact ⟨D, coeff, hD, hDH, hcoeff, hcoeffrep⟩

/-- The same coefficient bound applies to the relation selected by the
materialized algorithm, including its deterministic first-free-column choice. -/
theorem materialized_dependence_shared {m k : Nat}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (hzeroOne : ∀ i j, A i j = 0 ∨ A i j = 1)
    (x : Fin k → ℚ)
    (hx : dependenceMaterialized (fun i j => (A i j : ℚ)) = some x) :
    ∃ (D : ℕ) (coeff : Fin k → ℤ),
      0 < D ∧
      D ≤ ((m.factorial * m ^ m) ^ 2) ∧
      (∀ j, (coeff j).natAbs ≤ ((m.factorial * m ^ m) ^ 2)) ∧
      (∀ j, x j = (coeff j : ℚ) / (D : ℚ)) := by
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
      obtain ⟨D, coeff, hD, hDB, hcoeffB, hrep⟩ :=
        echelon_candidate_shared A hzeroOne f
          (by simpa [Aq, out] using hfree)
      have hcard : Fintype.card (PivotIndex out.2) ≤ m := by
        -- Distinct pivot rows embed the pivot list into the row index.
        have hn := echelonTyped_pivot_rows_nodup Aq 0 0 k
        have hi := pivot_rows_injective out.2 (by simpa [out] using hn)
        exact (Fintype.card_le_of_injective _ hi).trans (by simp)
      have hH :
          ((Fintype.card (PivotIndex out.2)).factorial *
            m ^ Fintype.card (PivotIndex out.2)) ^ 2 ≤
          (m.factorial * m ^ m) ^ 2 := by
        apply Nat.pow_le_pow_left
        apply Nat.mul_le_mul
        · exact Nat.factorial_le hcard
        · by_cases hm : m = 0
          · subst m
            have hc : Fintype.card (PivotIndex out.2) = 0 := by omega
            simp [hc]
          · exact Nat.pow_le_pow_right (by omega) hcard
      refine ⟨D, coeff, hD, hDB.trans hH,
        fun j => (hcoeffB j).trans hH, ?_⟩
      intro j
      rw [hxval]
      exact hrep j

/-- The returned array of the materialized finder has a single bounded
common denominator whenever its input cells are zero or one. -/
theorem materialized_array_shared (a : Array (Array ℚ))
    (h01 : ∀ i : Fin a.size, ∀ j : Fin (columnCount a),
      matrixOfArray a i j = 0 ∨ matrixOfArray a i j = 1)
    (x : Array ℚ) (hx : materializedArrayDependence a = some x) :
    ∃ (D : ℕ) (coeff : Fin (columnCount a) → ℤ),
      0 < D ∧
      D ≤ (a.size.factorial * a.size ^ a.size) ^ 2 ∧
      (∀ j, (coeff j).natAbs ≤
        (a.size.factorial * a.size ^ a.size) ^ 2) ∧
      x.size = columnCount a ∧
      (∀ j, x[j.val]?.getD 0 = (coeff j : ℚ) / (D : ℚ)) := by
  let A : Matrix (Fin a.size) (Fin (columnCount a)) ℤ :=
    fun i j => if matrixOfArray a i j = 0 then 0 else 1
  have hA : ∀ i j, A i j = 0 ∨ A i j = 1 := by
    intro i j
    by_cases h : matrixOfArray a i j = 0
    · exact Or.inl (by simp [A, h])
    · exact Or.inr (by simp [A, h])
  have hAq : (fun i j => (A i j : ℚ)) = matrixOfArray a := by
    funext i j
    by_cases h : matrixOfArray a i j = 0
    · simp [A, h]
    · have h1 := (h01 i j).resolve_left h
      simp [A, h, h1]
  cases hdep : dependenceMaterialized (matrixOfArray a) with
  | none => simp [materializedArrayDependence, hdep] at hx
  | some v =>
      have hxarr : x = Array.ofFn v := by
        simpa [materializedArrayDependence, hdep] using hx.symm
      obtain ⟨D, coeff, hD, hDB, hcoeff, hrep⟩ :=
        materialized_dependence_shared A hA v (by simpa [hAq] using hdep)
      refine ⟨D, coeff, hD, hDB, hcoeff, ?_, ?_⟩
      · simp [hxarr]
      · intro j
        simp [hxarr, hrep j]

theorem certified_materialized_shared (a : Array (Array ℚ))
    (h01 : ∀ i : Fin a.size, ∀ j : Fin (columnCount a),
      matrixOfArray a i j = 0 ∨ matrixOfArray a i j = 1)
    (cert : {x : Array ℚ // IsDependence a x})
    (hcert : certifiedMaterializedDependence a = some cert) :
    ∃ (D : ℕ) (coeff : Fin (columnCount a) → ℤ),
      0 < D ∧
      D ≤ (a.size.factorial * a.size ^ a.size) ^ 2 ∧
      (∀ j, (coeff j).natAbs ≤
        (a.size.factorial * a.size ^ a.size) ^ 2) ∧
      cert.val.size = columnCount a ∧
      (∀ j, cert.val[j.val]?.getD 0 =
        (coeff j : ℚ) / (D : ℚ)) := by
  unfold certifiedMaterializedDependence at hcert
  cases hraw : materializedArrayDependence a with
  | none => simp [hraw] at hcert
  | some x =>
      simp only [hraw] at hcert
      split at hcert
      · cases hcert
        exact materialized_array_shared a h01 x hraw
      · cases hcert

#print axioms typedCandidate_shared_coefficients
#print axioms echelon_candidate_shared
#print axioms materialized_dependence_shared
#print axioms certified_materialized_shared

end CurrentAdditive.RationalCandidateCompletion
