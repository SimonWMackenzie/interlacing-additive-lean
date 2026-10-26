import CurrentAdditive.PivotGramBridge

set_option maxHeartbeats 1000000

/-!
One denominator for all coordinates of the *actual* typed pivot solution.
The squared Gram determinant avoids a sign choice; its extra constant factor
does not change the manuscript's O(M log M) coefficient-bit charge.
-/

namespace CurrentAdditive.RationalCandidateCompletion

open CurrentAdditive.RationalBitBounds

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem generic_zero_one_shared_gram (m : Nat)
    (A : Matrix (Fin m) ι ℤ) (b : Fin m → ℤ) (x : ι → ℚ)
    (hA : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hb : ∀ i, b i = 0 ∨ b i = 1)
    (hinj : Function.Injective (A.map fun t : ℤ => (t : ℚ)).mulVec)
    (hAx : (A.map fun t : ℤ => (t : ℚ)).mulVec x =
      fun i => (b i : ℚ)) :
    ∃ (D : ℕ) (z : ι → ℤ),
      0 < D ∧
      D ≤ ((Fintype.card ι).factorial * m ^ Fintype.card ι) ^ 2 ∧
      (∀ j, (z j).natAbs ≤
        ((Fintype.card ι).factorial * m ^ Fintype.card ι) ^ 2) ∧
      (∀ j, x j = (z j : ℚ) / (D : ℚ)) := by
  let Aq : Matrix (Fin m) ι ℚ := A.map fun t : ℤ => (t : ℚ)
  let G : Matrix ι ι ℤ := A.transpose * A
  let c : ι → ℤ := A.transpose.mulVec b
  let H := (Fintype.card ι).factorial * m ^ Fintype.card ι
  have hGmap : (G.map fun t : ℤ => (t : ℚ)) = Aq.transpose * Aq := by
    change (A.transpose * A).map (Int.castRingHom ℚ) =
      (A.map (Int.castRingHom ℚ)).transpose * A.map (Int.castRingHom ℚ)
    rw [Matrix.map_mul, Matrix.transpose_map]
  have hcmap : (fun i => (c i : ℚ)) =
      Aq.transpose.mulVec (fun i => (b i : ℚ)) := by
    funext i
    simp [c, Aq, Matrix.mulVec, dotProduct, Int.cast_sum]
  have hGdetq : (Aq.transpose * Aq).det ≠ 0 :=
    generic_gram_det_ne_zero m Aq hinj
  have hGdet : G.det ≠ 0 := by
    intro hh
    apply hGdetq
    rw [← hGmap, ← Int.cast_det, hh]
    simp
  have hGx : (G.map fun t : ℤ => (t : ℚ)).mulVec x =
      fun i => (c i : ℚ) := by
    rw [hGmap, hcmap, ← Matrix.mulVec_mulVec, hAx]
  have hentry : ∀ i k, |G i k| ≤ (m : ℤ) := by
    intro i k
    dsimp only [G]
    rw [Matrix.mul_apply]
    exact zero_one_sum_products_abs_le m (fun t => A t i) (fun t => A t k)
      (fun t => hA t i) (fun t => hA t k)
  have hright : ∀ i, |c i| ≤ (m : ℤ) := by
    intro i
    change |∑ t, A t i * b t| ≤ (m : ℤ)
    exact zero_one_sum_products_abs_le m (fun t => A t i) b
      (fun t => hA t i) hb
  have hdBound : G.det.natAbs ≤ H := generic_det_bound m G hentry
  let D : ℕ := G.det.natAbs ^ 2
  let z : ι → ℤ := fun j => G.det * (G.updateCol j c).det
  refine ⟨D, z, ?_, ?_, ?_, ?_⟩
  · exact pow_pos (Int.natAbs_pos.mpr hGdet) _
  · exact Nat.pow_le_pow_left hdBound _
  · intro j
    have hupdate : ∀ i k, |(G.updateCol j c) i k| ≤ (m : ℤ) := by
      intro i k
      rw [Matrix.updateCol_apply]
      split_ifs
      · exact hright i
      · exact hentry i k
    have hnBound : (G.updateCol j c).det.natAbs ≤ H :=
      generic_det_bound m (G.updateCol j c) hupdate
    change (G.det * (G.updateCol j c).det).natAbs ≤ H ^ 2
    rw [Int.natAbs_mul, pow_two]
    exact Nat.mul_le_mul hdBound hnBound
  · intro j
    have hdetEq : (G.map fun t : ℤ => (t : ℚ)).det = (G.det : ℚ) :=
      (Int.cast_det G).symm
    have hdetq : (G.map fun t : ℤ => (t : ℚ)).det ≠ 0 := by
      rw [hdetEq]
      exact_mod_cast hGdet
    have hcramer := generic_cramer_solution
      (G.map fun t : ℤ => (t : ℚ)) (fun i => (c i : ℚ)) x hdetq hGx j
    have hU : ((G.map fun t : ℤ => (t : ℚ)).updateCol j
          (fun i => (c i : ℚ))).det = ((G.updateCol j c).det : ℚ) := by
      have hmap : (G.updateCol j c).map (fun t : ℤ => (t : ℚ)) =
          (G.map fun t : ℤ => (t : ℚ)).updateCol j (fun i => (c i : ℚ)) := by
        ext i k
        simp [Matrix.updateCol_apply]
      rw [← hmap, ← Int.cast_det]
    rw [hU, hdetEq] at hcramer
    have hdq : (G.det : ℚ) ≠ 0 := by exact_mod_cast hGdet
    change x j = ((G.det * (G.updateCol j c).det : ℤ) : ℚ) /
      ((G.det.natAbs ^ 2 : ℕ) : ℚ)
    have hDcast : ((G.det.natAbs ^ 2 : ℕ) : ℚ) = (G.det : ℚ) ^ 2 := by
      calc
        ((G.det.natAbs ^ 2 : ℕ) : ℚ) = ((G.det.natAbs ^ 2 : ℕ) : ℤ) := by norm_cast
        _ = ((G.det ^ 2 : ℤ) : ℚ) := by
          congr 1
          simpa only [Nat.cast_pow, Int.natCast_natAbs] using (sq_abs G.det)
        _ = (G.det : ℚ) ^ 2 := by push_cast; rfl
    rw [hcramer, hDcast]
    push_cast
    field_simp

open CurrentAdditive.SequentialTotality

theorem pivot_solution_shared {m k : Nat}
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
      rowDot (fun i j => (A i j : ℚ))
        (typedCandidate B ps f) i = 0) :
    ∃ (D : ℕ) (z : PivotIndex ps → ℤ),
      0 < D ∧
      D ≤ ((Fintype.card (PivotIndex ps)).factorial *
        m ^ Fintype.card (PivotIndex ps)) ^ 2 ∧
      (∀ p, (z p).natAbs ≤
        ((Fintype.card (PivotIndex ps)).factorial *
          m ^ Fintype.card (PivotIndex ps)) ^ 2) ∧
      (∀ p, B p.val.1 f = (z p : ℚ) / (D : ℚ)) := by
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
  exact generic_zero_one_shared_gram m C b x hC hb hinj hAx

theorem echelon_pivot_shared {m k : Nat}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (hzeroOne : ∀ i j, A i j = 0 ∨ A i j = 1)
    (f : Fin k)
    (hfree : f ∉
      ((echelonTyped (fun i j => (A i j : ℚ)) 0 0 k).2.map Prod.snd)) :
    let out := echelonTyped (fun i j => (A i j : ℚ)) 0 0 k
    ∃ (D : ℕ) (z : PivotIndex out.2 → ℤ),
      0 < D ∧
      D ≤ ((Fintype.card (PivotIndex out.2)).factorial *
        m ^ Fintype.card (PivotIndex out.2)) ^ 2 ∧
      (∀ p, (z p).natAbs ≤
        ((Fintype.card (PivotIndex out.2)).factorial *
          m ^ Fintype.card (PivotIndex out.2)) ^ 2) ∧
      (∀ p, out.1 p.val.1 f = (z p : ℚ) / (D : ℚ)) := by
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
  exact pivot_solution_shared A B ps f hzeroOne
    (by simpa [Aq, out, B, ps] using hunit)
    (by simpa [Aq, out, ps] using hnodup)
    (by
      intro v
      simpa [Aq, out, B] using (echelonTyped_kernel_iff Aq 0 0 k v))
    (by simpa [Aq] using hcand)

#print axioms generic_zero_one_shared_gram
#print axioms echelon_pivot_shared

end CurrentAdditive.RationalCandidateCompletion
