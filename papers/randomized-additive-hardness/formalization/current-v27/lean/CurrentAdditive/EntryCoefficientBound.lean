import CurrentAdditive.EliminationEntryTrace
import CurrentAdditive.CramerMinorBound

/-!
Polynomial bit growth for the actual eager Gauss--Jordan entries. This file
uses the checked instrumented trace, selected original-row minor, and the
generic integer Cramer estimate.
-/

namespace CurrentAdditive.EliminationEntryBounds

open CurrentAdditive.RationalBitBounds

theorem generic_det_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Nat) (A : Matrix ι ι ℤ)
    (hentry : ∀ i j, |A i j| ≤ (T : ℤ)) :
    A.det.natAbs ≤ (Fintype.card ι).factorial * T ^ Fintype.card ι := by
  have h := Matrix.det_le (abv := (AbsoluteValue.abs : AbsoluteValue ℤ ℤ))
    (x := (T : ℤ)) hentry
  have h' : |A.det| ≤ ((Fintype.card ι).factorial : ℤ) * (T : ℤ) ^
      Fintype.card ι := by
    simpa [AbsoluteValue.abs_apply] using h
  have hInt : ((A.det.natAbs : ℕ) : ℤ) ≤
      (((Fintype.card ι).factorial * T ^ Fintype.card ι : ℕ) : ℤ) := by
    simpa only [Int.natCast_natAbs, Nat.cast_mul, Nat.cast_pow] using h'
  exact_mod_cast hInt

theorem generic_cramer_solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ) (b x : ι → ℚ)
    (hdet : A.det ≠ 0) (hAx : A.mulVec x = b) (j : ι) :
    x j = (A.updateCol j b).det / A.det := by
  have hinj : Function.Injective A.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((A.isUnit_iff_isUnit_det).mpr (isUnit_iff_ne_zero.mpr hdet))
  have hscale : A.mulVec (A.det • x) = A.mulVec (A.cramer b) := by
    rw [Matrix.mulVec_smul, hAx, Matrix.mulVec_cramer]
  have hx := congrFun (hinj hscale) j
  rw [Matrix.cramer_apply] at hx
  simp only [Pi.smul_apply, smul_eq_mul] at hx
  apply (eq_div_iff hdet).mpr
  simpa [mul_comm] using hx

theorem generic_cramer_bounded_component {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (T : Nat) (A : Matrix ι ι ℤ) (b : ι → ℤ) (x : ι → ℚ)
    (hA : ∀ i j, |A i j| ≤ (T : ℤ))
    (hb : ∀ i, |b i| ≤ (T : ℤ))
    (hdet : A.det ≠ 0)
    (hAx : (A.map fun t : ℤ => (t : ℚ)).mulVec x =
      fun i => (b i : ℚ)) (j : ι) :
    (x j).num.natAbs ≤ (Fintype.card ι).factorial * T ^ Fintype.card ι ∧
    (x j).den ≤ (Fintype.card ι).factorial * T ^ Fintype.card ι := by
  let Aq : Matrix ι ι ℚ := A.map fun t : ℤ => (t : ℚ)
  let bq : ι → ℚ := fun i => (b i : ℚ)
  have hdetEq : Aq.det = (A.det : ℚ) := (Int.cast_det A).symm
  have hdetq : Aq.det ≠ 0 := by
    rw [hdetEq]
    exact_mod_cast hdet
  have hU : (Aq.updateCol j bq).det =
      ((A.updateCol j b).det : ℚ) := by
    have hmap : (A.updateCol j b).map (fun t : ℤ => (t : ℚ)) =
        Aq.updateCol j bq := by
      ext i k
      simp [Aq, bq, Matrix.updateCol_apply]
    rw [← hmap, ← Int.cast_det]
  have hr : x j = ((A.updateCol j b).det : ℚ) / (A.det : ℚ) := by
    rw [←hU, ←hdetEq]
    exact generic_cramer_solution Aq bq x hdetq hAx j
  have hupdate : ∀ i k, |(A.updateCol j b) i k| ≤ (T : ℤ) := by
    intro i k
    rw [Matrix.updateCol_apply]
    split_ifs
    · exact hb i
    · exact hA i k
  have hD := generic_det_bound T A hA
  have hN := generic_det_bound T (A.updateCol j b) hupdate
  obtain ⟨hn, hd⟩ := rat_components_le_of_divInt (x j)
    (A.updateCol j b).det A.det hdet hr
  exact ⟨hn.trans hN, hd.trans hD⟩

theorem selectedRow_system {m k : Nat}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (B : Fin m → Fin k → ℚ) (U : Fin m → Fin m → ℚ)
    (π : Fin m → Fin m) (r : Nat)
    (hrep : Represents (fun i j => (A i j : ℚ)) B U)
    (hs : Support U π r) (hπ : Function.Injective π)
    (col : {t : Fin m // t.val < r} → Fin k)
    (hunit : ∀ v : {t : Fin m // t.val < r}, ∀ i : Fin m,
      B i (col v) = if i = v.val then 1 else 0)
    (i : Fin m) :
    let ι := {t : Fin m // t.val < r}
    let C : Matrix ι ι ℤ := fun v u => A (π u.val) (col v)
    let x : ι → ℚ := fun u => U i (π u.val)
    let b : ι → ℤ := fun v =>
      if i.val < r then (if i = v.val then 1 else 0)
      else -(A (π i) (col v))
    (C.map fun t : ℤ => (t : ℚ)).mulVec x =
      fun v => (b v : ℚ) := by
  let ι := {t : Fin m // t.val < r}
  let C : Matrix ι ι ℤ := fun v u => A (π u.val) (col v)
  let x : ι → ℚ := fun u => U i (π u.val)
  let b : ι → ℤ := fun v =>
    if i.val < r then (if i = v.val then 1 else 0)
    else -(A (π i) (col v))
  funext v
  have hcomm : (∑ u : ι, (A (π u.val) (col v) : ℚ) * U i (π u.val)) =
      ∑ u : ι, U i (π u.val) * (A (π u.val) (col v) : ℚ) := by
    apply Finset.sum_congr rfl
    intro u _
    ring
  by_cases hi : i.val < r
  · have hh := pivotRow_selected_sum
      (fun i j => (A i j : ℚ)) B U π r hrep hs hπ i hi (col v)
    rw [hunit v i] at hh
    simp only [C, x, b, Matrix.mulVec, dotProduct, Matrix.map_apply,
      hi, ite_true]
    change (∑ u : ι, (A (π u.val) (col v) : ℚ) * U i (π u.val)) =
      ((if i = v.val then (1 : ℤ) else 0 : ℤ) : ℚ)
    rw [hcomm]
    simpa using hh.symm
  · have hh := residualRow_selected_sum
      (fun i j => (A i j : ℚ)) B U π r hrep hs hπ i
      (by omega) (col v)
    have hne : i ≠ v.val := by
      intro h
      have := congrArg Fin.val h
      omega
    rw [hunit v i, if_neg hne] at hh
    simp only [C, x, b, Matrix.mulVec, dotProduct, Matrix.map_apply,
      hi, ite_false]
    change (∑ u : ι, (A (π u.val) (col v) : ℚ) * U i (π u.val)) =
      ((-(A (π i) (col v))) : ℚ)
    rw [hcomm]
    push_cast
    linarith [hh]

theorem selectedRow_coefficient_bound {m k : Nat}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (B : Fin m → Fin k → ℚ) (U : Fin m → Fin m → ℚ)
    (π : Fin m → Fin m) (r : Nat)
    (hrep : Represents (fun i j => (A i j : ℚ)) B U)
    (hs : Support U π r) (hπ : Function.Injective π)
    (col : {t : Fin m // t.val < r} → Fin k)
    (hunit : ∀ v : {t : Fin m // t.val < r}, ∀ i : Fin m,
      B i (col v) = if i = v.val then 1 else 0) :
    let ι := {t : Fin m // t.val < r}
    ∀ i : Fin m, ∀ u : ι,
      (U i (π u.val)).num.natAbs ≤ (Fintype.card ι).factorial ∧
      (U i (π u.val)).den ≤ (Fintype.card ι).factorial := by
  classical
  let ι := {t : Fin m // t.val < r}
  let C : Matrix ι ι ℤ := fun v u => A (π u.val) (col v)
  let M : Matrix ι ι ℚ := fun u v => (A (π u.val) (col v) : ℚ)
  have hM : M.det ≠ 0 := by
    exact selectedMinor_nonsingular (fun i j => (A i j : ℚ)) B U π r
      hrep hs hπ col hunit
  have hCmap : (C.map fun z : ℤ => (z : ℚ)) = M.transpose := by
    ext v u
    rfl
  have hdetq : (C.det : ℚ) ≠ 0 := by
    rw [Int.cast_det C, hCmap, Matrix.det_transpose]
    exact hM
  have hdet : C.det ≠ 0 := by
    exact_mod_cast hdetq
  have hC : ∀ v u, |C v u| ≤ (1 : ℤ) := by
    intro v u
    rcases h01 (π u.val) (col v) with h | h <;> simp [C, h]
  change ∀ i : Fin m, ∀ u : ι,
    (U i (π u.val)).num.natAbs ≤ (Fintype.card ι).factorial ∧
    (U i (π u.val)).den ≤ (Fintype.card ι).factorial
  intro i u
  let x : ι → ℚ := fun u => U i (π u.val)
  let b : ι → ℤ := fun v =>
    if i.val < r then (if i = v.val then 1 else 0)
    else -(A (π i) (col v))
  have hb : ∀ v, |b v| ≤ (1 : ℤ) := by
    intro v
    by_cases hi : i.val < r
    · by_cases hiv : i = v.val <;> simp [b, hi, hiv, v.property]
    · rcases h01 (π i) (col v) with h | h <;> simp [b, hi, h]
  have hAx : (C.map fun z : ℤ => (z : ℚ)).mulVec x =
      fun v => (b v : ℚ) :=
    selectedRow_system A B U π r hrep hs hπ col hunit i
  have h := generic_cramer_bounded_component 1 C b x hC hb hdet hAx u
  simpa [x] using h

end CurrentAdditive.EliminationEntryBounds
