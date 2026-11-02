import Mathlib
import CurrentAdditive.RationalBitBounds

/-! Determinant and Cramer bounds for zero-one feature minors. -/

namespace CurrentAdditive.RationalBitBounds

theorem det_natAbs_le_factorial (r : Nat) (A : Matrix (Fin r) (Fin r) ℤ)
    (hentry : ∀ i j, |A i j| ≤ 1) :
    A.det.natAbs ≤ r.factorial := by
  have h := Matrix.det_le (abv := (AbsoluteValue.abs : AbsoluteValue ℤ ℤ))
    (x := (1 : ℤ)) hentry
  have h' : |A.det| ≤ (r.factorial : ℤ) := by
    simpa [AbsoluteValue.abs_apply, Fintype.card_fin] using h
  have hInt : ((A.det.natAbs : ℕ) : ℤ) ≤ (r.factorial : ℤ) := by
    simpa only [Int.natCast_natAbs] using h'
  exact_mod_cast hInt

theorem det_natAbs_le_factorial_mul_pow (r T : Nat)
    (A : Matrix (Fin r) (Fin r) ℤ)
    (hentry : ∀ i j, |A i j| ≤ (T : ℤ)) :
    A.det.natAbs ≤ r.factorial * T ^ r := by
  have h := Matrix.det_le (abv := (AbsoluteValue.abs : AbsoluteValue ℤ ℤ))
    (x := (T : ℤ)) hentry
  have h' : |A.det| ≤ (r.factorial : ℤ) * (T : ℤ) ^ r := by
    simpa [AbsoluteValue.abs_apply, Fintype.card_fin] using h
  have hInt : ((A.det.natAbs : ℕ) : ℤ) ≤
      ((r.factorial * T ^ r : ℕ) : ℤ) := by
    simpa only [Int.natCast_natAbs, Nat.cast_mul, Nat.cast_pow] using h'
  exact_mod_cast hInt

theorem cramer_solution (r : Nat) (A : Matrix (Fin r) (Fin r) ℚ)
    (b x : Fin r → ℚ) (hdet : A.det ≠ 0)
    (hAx : A.mulVec x = b) (j : Fin r) :
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

theorem rat_components_le_of_divInt (q : ℚ) (n d : ℤ)
    (hd : d ≠ 0) (hq : q = (n : ℚ) / (d : ℚ)) :
    q.num.natAbs ≤ n.natAbs ∧ q.den ≤ d.natAbs := by
  rw [← Rat.divInt_eq_div] at hq
  subst q
  constructor
  · by_cases hn : n = 0
    · simp [hn]
    · exact Int.natAbs_le_of_dvd_ne_zero (Rat.num_dvd n hd) hn
  · have hdvd : (Rat.divInt n d).den ∣ d.natAbs := by
      simpa using (Int.natAbs_dvd_natAbs.mpr (Rat.den_dvd n d))
    exact Nat.le_of_dvd (Int.natAbs_pos.mpr hd) hdvd

theorem cramer_zero_one_component_bound (r : Nat)
    (A : Matrix (Fin r) (Fin r) ℤ) (b : Fin r → ℤ)
    (x : Fin r → ℚ)
    (hA : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hb : ∀ i, b i = 0 ∨ b i = 1)
    (hdet : A.det ≠ 0)
    (hAx : (A.map fun t : ℤ => (t : ℚ)).mulVec x =
      fun i => (b i : ℚ)) (j : Fin r) :
    (x j).num.natAbs ≤ r.factorial ∧ (x j).den ≤ r.factorial := by
  let Aq : Matrix (Fin r) (Fin r) ℚ := A.map fun t : ℤ => (t : ℚ)
  let bq : Fin r → ℚ := fun i => (b i : ℚ)
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
    exact cramer_solution r Aq bq x hdetq hAx j
  have hentry : ∀ i k, |A i k| ≤ 1 := by
    intro i k
    rcases hA i k with h | h <;> simp [h]
  have hupdate : ∀ i k, |(A.updateCol j b) i k| ≤ 1 := by
    intro i k
    rw [Matrix.updateCol_apply]
    split_ifs
    · rcases hb i with h | h <;> simp [h]
    · exact hentry i k
  have hD := det_natAbs_le_factorial r A hentry
  have hN := det_natAbs_le_factorial r (A.updateCol j b) hupdate
  obtain ⟨hn, hd⟩ := rat_components_le_of_divInt (x j)
    (A.updateCol j b).det A.det hdet hr
  exact ⟨hn.trans hN, hd.trans hD⟩

theorem cramer_bounded_component_bound (r T : Nat)
    (A : Matrix (Fin r) (Fin r) ℤ) (b : Fin r → ℤ)
    (x : Fin r → ℚ)
    (hA : ∀ i j, |A i j| ≤ (T : ℤ))
    (hb : ∀ i, |b i| ≤ (T : ℤ))
    (hdet : A.det ≠ 0)
    (hAx : (A.map fun t : ℤ => (t : ℚ)).mulVec x =
      fun i => (b i : ℚ)) (j : Fin r) :
    (x j).num.natAbs ≤ r.factorial * T ^ r ∧
      (x j).den ≤ r.factorial * T ^ r := by
  let Aq : Matrix (Fin r) (Fin r) ℚ := A.map fun t : ℤ => (t : ℚ)
  let bq : Fin r → ℚ := fun i => (b i : ℚ)
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
    exact cramer_solution r Aq bq x hdetq hAx j
  have hupdate : ∀ i k, |(A.updateCol j b) i k| ≤ (T : ℤ) := by
    intro i k
    rw [Matrix.updateCol_apply]
    split_ifs
    · exact hb i
    · exact hA i k
  have hD := det_natAbs_le_factorial_mul_pow r T A hA
  have hN := det_natAbs_le_factorial_mul_pow r T (A.updateCol j b) hupdate
  obtain ⟨hn, hd⟩ := rat_components_le_of_divInt (x j)
    (A.updateCol j b).det A.det hdet hr
  exact ⟨hn.trans hN, hd.trans hD⟩

/-- For a rectangular rational matrix with independent columns, the square
Gram matrix is invertible. This avoids selecting a nonzero row minor. -/
theorem gram_det_ne_zero_of_injective (m r : Nat)
    (A : Matrix (Fin m) (Fin r) ℚ)
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

theorem zero_one_sum_products_abs_le (m : Nat)
    (f g : Fin m → ℤ)
    (hf : ∀ i, f i = 0 ∨ f i = 1)
    (hg : ∀ i, g i = 0 ∨ g i = 1) :
    |∑ i, f i * g i| ≤ (m : ℤ) := by
  have hterm : ∀ i, 0 ≤ f i * g i ∧ f i * g i ≤ 1 := by
    intro i
    rcases hf i with hfi | hfi <;> rcases hg i with hgi | hgi <;>
      simp [hfi, hgi]
  have hnonneg : 0 ≤ ∑ i, f i * g i :=
    Finset.sum_nonneg (fun i _ => (hterm i).1)
  have hle : (∑ i, f i * g i) ≤ (m : ℤ) := by
    calc
      (∑ i, f i * g i) ≤ ∑ _i : Fin m, (1 : ℤ) :=
        Finset.sum_le_sum (fun i _ => (hterm i).2)
      _ = (m : ℤ) := by simp
  simpa [abs_of_nonneg hnonneg] using hle

theorem zero_one_gram_entry_bound (m r : Nat)
    (A : Matrix (Fin m) (Fin r) ℤ)
    (hA : ∀ i j, A i j = 0 ∨ A i j = 1)
    (i j : Fin r) :
    |(A.transpose * A) i j| ≤ (m : ℤ) := by
  rw [Matrix.mul_apply]
  exact zero_one_sum_products_abs_le m (fun t => A t i) (fun t => A t j)
    (fun t => hA t i) (fun t => hA t j)

theorem zero_one_gram_rhs_bound (m r : Nat)
    (A : Matrix (Fin m) (Fin r) ℤ) (b : Fin m → ℤ)
    (hA : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hb : ∀ i, b i = 0 ∨ b i = 1)
    (j : Fin r) :
    |A.transpose.mulVec b j| ≤ (m : ℤ) := by
  change |∑ t, A t j * b t| ≤ (m : ℤ)
  exact zero_one_sum_products_abs_le m (fun t => A t j) b
    (fun t => hA t j) hb

/-- A coordinate bound for the unique coefficients of independent zero-one
columns. The bound is obtained from the integer Gram system, so no choice of
an invertible submatrix is needed. -/
theorem zero_one_independent_solution_bound (m r : Nat)
    (A : Matrix (Fin m) (Fin r) ℤ) (b : Fin m → ℤ)
    (x : Fin r → ℚ)
    (hA : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hb : ∀ i, b i = 0 ∨ b i = 1)
    (hinj : Function.Injective (A.map fun t : ℤ => (t : ℚ)).mulVec)
    (hAx : (A.map fun t : ℤ => (t : ℚ)).mulVec x =
      fun i => (b i : ℚ)) (j : Fin r) :
    (x j).num.natAbs ≤ r.factorial * m ^ r ∧
      (x j).den ≤ r.factorial * m ^ r := by
  let Aq : Matrix (Fin m) (Fin r) ℚ := A.map fun t : ℤ => (t : ℚ)
  let G : Matrix (Fin r) (Fin r) ℤ := A.transpose * A
  let c : Fin r → ℤ := A.transpose.mulVec b
  have hGmap : (G.map fun t : ℤ => (t : ℚ)) = Aq.transpose * Aq := by
    change (A.transpose * A).map (Int.castRingHom ℚ) =
      (A.map (Int.castRingHom ℚ)).transpose * A.map (Int.castRingHom ℚ)
    rw [Matrix.map_mul, Matrix.transpose_map]
  have hcmap : (fun i => (c i : ℚ)) = Aq.transpose.mulVec (fun i => (b i : ℚ)) := by
    funext i
    simp [c, Aq, Matrix.mulVec, dotProduct, Int.cast_sum]
  have hGdetq : (Aq.transpose * Aq).det ≠ 0 :=
    gram_det_ne_zero_of_injective m r Aq hinj
  have hGdet : G.det ≠ 0 := by
    intro hh
    apply hGdetq
    rw [← hGmap, ← Int.cast_det, hh]
    simp
  have hGx : (G.map fun t : ℤ => (t : ℚ)).mulVec x =
      fun i => (c i : ℚ) := by
    rw [hGmap, hcmap, ← Matrix.mulVec_mulVec, hAx]
  exact cramer_bounded_component_bound r m G c x
    (fun i k => zero_one_gram_entry_bound m r A hA i k)
    (fun i => zero_one_gram_rhs_bound m r A b hA hb i)
    hGdet hGx j

/-- A deliberately loose explicit polynomial bit budget for the Gram/Cramer
numerator and denominator. -/
theorem gram_coefficient_pow_bound (m r : Nat) :
    r.factorial * m ^ r ≤ 2 ^ ((2 * r) * (m + r + 2)) := by
  let N := m + r + 2
  have hrle : r ≤ 2 ^ N := by
    have hn : N < 2 ^ N := Nat.lt_two_pow_self
    omega
  have hmle : m ≤ 2 ^ N := by
    have hn : N < 2 ^ N := Nat.lt_two_pow_self
    omega
  calc
    r.factorial * m ^ r ≤ r ^ r * m ^ r :=
      Nat.mul_le_mul_right _ (Nat.factorial_le_pow r)
    _ ≤ (2 ^ N) ^ r * (2 ^ N) ^ r :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hrle r) (Nat.pow_le_pow_left hmle r)
    _ = 2 ^ ((2 * r) * N) := by
      rw [← pow_add, ← pow_mul]
      congr 1
      ring

theorem zero_one_independent_solution_bits (m r : Nat)
    (A : Matrix (Fin m) (Fin r) ℤ) (b : Fin m → ℤ)
    (x : Fin r → ℚ)
    (hA : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hb : ∀ i, b i = 0 ∨ b i = 1)
    (hinj : Function.Injective (A.map fun t : ℤ => (t : ℚ)).mulVec)
    (hAx : (A.map fun t : ℤ => (t : ℚ)).mulVec x =
      fun i => (b i : ℚ)) (j : Fin r) :
    Nat.size (x j).num.natAbs ≤ (2 * r) * (m + r + 2) + 1 ∧
      Nat.size (x j).den ≤ (2 * r) * (m + r + 2) + 1 := by
  obtain ⟨hn, hd⟩ :=
    zero_one_independent_solution_bound m r A b x hA hb hinj hAx j
  have hp := gram_coefficient_pow_bound m r
  exact ⟨size_le_of_pow_bound (hn.trans hp),
    size_le_of_pow_bound (hd.trans hp)⟩

end CurrentAdditive.RationalBitBounds
