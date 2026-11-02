import CurrentAdditive.CramerMinorBound

/-! The same Gram/Cramer bound with pivot pairs themselves as column labels. -/

namespace CurrentAdditive.RationalBitBounds

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem generic_det_bound (T : Nat) (A : Matrix ι ι ℤ)
    (hentry : ∀ i j, |A i j| ≤ (T : ℤ)) :
    A.det.natAbs ≤ (Fintype.card ι).factorial * T ^ Fintype.card ι := by
  have h := Matrix.det_le (abv := (AbsoluteValue.abs : AbsoluteValue ℤ ℤ))
    (x := (T : ℤ)) hentry
  have h' : |A.det| ≤ ((Fintype.card ι).factorial : ℤ) * (T : ℤ) ^ Fintype.card ι := by
    simpa [AbsoluteValue.abs_apply] using h
  have hInt : ((A.det.natAbs : ℕ) : ℤ) ≤
      (((Fintype.card ι).factorial * T ^ Fintype.card ι : ℕ) : ℤ) := by
    simpa only [Int.natCast_natAbs, Nat.cast_mul, Nat.cast_pow] using h'
  exact_mod_cast hInt

theorem generic_cramer_solution (A : Matrix ι ι ℚ)
    (b x : ι → ℚ) (hdet : A.det ≠ 0)
    (hAx : A.mulVec x = b) (j : ι) :
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

theorem generic_cramer_bound (T : Nat)
    (A : Matrix ι ι ℤ) (b : ι → ℤ) (x : ι → ℚ)
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

theorem generic_gram_det_ne_zero (m : Nat)
    (A : Matrix (Fin m) ι ℚ)
    (hinj : Function.Injective A.mulVec) :
    (A.transpose * A).det ≠ 0 := by
  have hlinj : Function.Injective A.mulVecLin := by
    simpa only [Matrix.mulVecLin_apply] using hinj
  have hker : (A.transpose * A).mulVecLin.ker = ⊥ := by
    rw [Matrix.ker_mulVecLin_transpose_mul_self]
    exact LinearMap.ker_eq_bot_of_injective hlinj
  have hginj : Function.Injective (A.transpose * A).mulVec := by
    simpa only [Matrix.mulVecLin_apply] using
      (LinearMap.ker_eq_bot.mp hker)
  have hu : IsUnit (A.transpose * A) :=
    Matrix.mulVec_injective_iff_isUnit.mp hginj
  exact isUnit_iff_ne_zero.mp ((A.transpose * A).isUnit_iff_isUnit_det.mp hu)

theorem generic_zero_one_solution_bound (m : Nat)
    (A : Matrix (Fin m) ι ℤ) (b : Fin m → ℤ)
    (x : ι → ℚ)
    (hA : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hb : ∀ i, b i = 0 ∨ b i = 1)
    (hinj : Function.Injective (A.map fun t : ℤ => (t : ℚ)).mulVec)
    (hAx : (A.map fun t : ℤ => (t : ℚ)).mulVec x =
      fun i => (b i : ℚ)) (j : ι) :
    (x j).num.natAbs ≤ (Fintype.card ι).factorial * m ^ Fintype.card ι ∧
      (x j).den ≤ (Fintype.card ι).factorial * m ^ Fintype.card ι := by
  let Aq : Matrix (Fin m) ι ℚ := A.map fun t : ℤ => (t : ℚ)
  let G : Matrix ι ι ℤ := A.transpose * A
  let c : ι → ℤ := A.transpose.mulVec b
  have hGmap : (G.map fun t : ℤ => (t : ℚ)) = Aq.transpose * Aq := by
    change (A.transpose * A).map (Int.castRingHom ℚ) =
      (A.map (Int.castRingHom ℚ)).transpose * A.map (Int.castRingHom ℚ)
    rw [Matrix.map_mul, Matrix.transpose_map]
  have hcmap : (fun i => (c i : ℚ)) = Aq.transpose.mulVec (fun i => (b i : ℚ)) := by
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
  exact generic_cramer_bound m G c x
    (fun i k => by
      dsimp only [G]
      rw [Matrix.mul_apply]
      exact zero_one_sum_products_abs_le m (fun t => A t i) (fun t => A t k)
        (fun t => hA t i) (fun t => hA t k))
    (fun i => by
      change |∑ t, A t i * b t| ≤ (m : ℤ)
      exact zero_one_sum_products_abs_le m (fun t => A t i) b
        (fun t => hA t i) hb)
    hGdet hGx j

end CurrentAdditive.RationalBitBounds
