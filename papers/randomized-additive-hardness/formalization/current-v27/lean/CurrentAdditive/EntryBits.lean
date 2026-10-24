import CurrentAdditive.EntryCoefficientBound

namespace CurrentAdditive.EliminationEntryBounds

theorem sum_den_dvd_prod {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℚ) :
    (∑ i ∈ s, f i).den ∣ ∏ i ∈ s, (f i).den := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha, Finset.prod_insert ha]
    exact (Rat.add_den_dvd (f a) (∑ i ∈ s, f i)).trans
      (Nat.mul_dvd_mul_left (f a).den ih)

theorem rat_abs_eq_num_den (q : ℚ) :
    |q| = (q.num.natAbs : ℚ) / (q.den : ℚ) := by
  conv_lhs => rw [← Rat.num_div_den q]
  rw [abs_div]
  simp

theorem rat_abs_le_num (q : ℚ) : |q| ≤ (q.num.natAbs : ℚ) := by
  rw [rat_abs_eq_num_den]
  have hd : (1 : ℚ) ≤ q.den := by exact_mod_cast q.den_pos
  apply (div_le_iff₀ (by positivity)).2
  nlinarith [Nat.cast_nonneg (α := ℚ) q.num.natAbs]

theorem rat_num_le_of_abs_den (q : ℚ) (N D : ℕ)
    (ha : |q| ≤ N) (hd : q.den ≤ D) :
    q.num.natAbs ≤ N * D := by
  have hden : (q.den : ℚ) ≠ 0 := by positivity
  have heq : (q.num.natAbs : ℚ) = |q| * q.den := by
    rw [rat_abs_eq_num_den, div_mul_cancel₀ _ hden]
  have hcast : (q.num.natAbs : ℚ) ≤ (N * D : ℕ) := by
    rw [heq, Nat.cast_mul]
    exact mul_le_mul ha (by exact_mod_cast hd) (by positivity) (by positivity)
  exact_mod_cast hcast

theorem sum_components_bound {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℚ) (M : ℕ) (hM : 0 < M)
    (hf : ∀ i ∈ s, (f i).num.natAbs ≤ M ∧ (f i).den ≤ M) :
    (∑ i ∈ s, f i).den ≤ M ^ s.card ∧
    (∑ i ∈ s, f i).num.natAbs ≤ s.card * M ^ (s.card + 1) := by
  have hprod : (∏ i ∈ s, (f i).den) ≤ M ^ s.card := by
    calc
      (∏ i ∈ s, (f i).den) ≤ ∏ _i ∈ s, M := by
        apply Finset.prod_le_prod
        · intro i hi
          exact (f i).den_pos.le
        · intro i hi
          exact (hf i hi).2
      _ = M ^ s.card := by simp
  have hden : (∑ i ∈ s, f i).den ≤ M ^ s.card :=
    (Nat.le_of_dvd (by positivity) (sum_den_dvd_prod s f)).trans hprod
  have habs : |∑ i ∈ s, f i| ≤ (s.card * M : ℕ) := by
    calc
      |∑ i ∈ s, f i| ≤ ∑ i ∈ s, |f i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ s, (M : ℚ) := by
        apply Finset.sum_le_sum
        intro i hi
        exact (rat_abs_le_num (f i)).trans (by exact_mod_cast (hf i hi).1)
      _ = (s.card * M : ℕ) := by simp [mul_comm]
  refine ⟨hden, ?_⟩
  have hn := rat_num_le_of_abs_den (∑ i ∈ s, f i)
    (s.card * M) (M ^ s.card) habs hden
  simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hn

theorem selectedRow_entry_bound {m k : Nat}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (B : Fin m → Fin k → ℚ) (U : Fin m → Fin m → ℚ)
    (π : Fin m → Fin m) (r : Nat)
    (hrep : Represents (fun i j => (A i j : ℚ)) B U)
    (hs : Support U π r) (hπ : Function.Injective π)
    (col : {t : Fin m // t.val < r} → Fin k)
    (hunit : ∀ v : {t : Fin m // t.val < r}, ∀ i : Fin m,
      B i (col v) = if i = v.val then 1 else 0)
    (i : Fin m) (j : Fin k) :
    let ι := {t : Fin m // t.val < r}
    let M := (Fintype.card ι).factorial
    (B i j).den ≤ M ^ (Fintype.card ι + 1) ∧
    (B i j).num.natAbs ≤
      (Fintype.card ι + 1) * M ^ (Fintype.card ι + 2) := by
  classical
  let ι := {t : Fin m // t.val < r}
  let M := (Fintype.card ι).factorial
  let f : Option ι → ℚ
    | none => if i.val < r then 0 else (A (π i) j : ℚ)
    | some u => U i (π u.val) * (A (π u.val) j : ℚ)
  have hM1 : 1 ≤ M := Nat.factorial_pos _
  have hcoeff := selectedRow_coefficient_bound A h01 B U π r
    hrep hs hπ col hunit
  have hf : ∀ t : Option ι,
      (f t).num.natAbs ≤ M ∧ (f t).den ≤ M := by
    intro t
    cases t with
    | none =>
      by_cases hi : i.val < r
      · simp [f, hi, M] <;> omega
      · rcases h01 (π i) j with h | h <;> simp [f, hi, h, M] <;> omega
    | some u =>
      rcases h01 (π u.val) j with h | h
      · simp [f, h, M] <;> omega
      · simpa [f, h, M] using hcoeff i u
  have hsum : (∑ t : Option ι, f t) = B i j := by
    rw [Fintype.sum_option]
    by_cases hi : i.val < r
    · have hh := pivotRow_selected_sum (fun i j => (A i j : ℚ)) B U π r
        hrep hs hπ i hi j
      simpa [f, hi] using hh.symm
    · have hh := residualRow_selected_sum (fun i j => (A i j : ℚ)) B U π r
        hrep hs hπ i (by omega) j
      simpa [f, hi, add_comm] using hh.symm
  have hh := sum_components_bound (Finset.univ : Finset (Option ι))
    f M (Nat.factorial_pos _) (by intro t _; exact hf t)
  simp only [Finset.card_univ,
    Fintype.card_option, hsum] at hh
  exact hh

theorem actualPrefix_entry_bound {m k : Nat}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (fuel : Nat) (hfuel : fuel ≤ k) :
    let out := runTrace (fun i j => (A i j : ℚ)) identityRows
      (fun i => i) 0 0 fuel
    let ι := {t : Fin m // t.val < out.pivots.length}
    let M := (Fintype.card ι).factorial
    ∀ i : Fin m, ∀ j : Fin k,
      (out.B i j).den ≤ M ^ (Fintype.card ι + 1) ∧
      (out.B i j).num.natAbs ≤
        (Fintype.card ι + 1) * M ^ (Fintype.card ι + 2) := by
  classical
  let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
  let out := runTrace Aq identityRows (fun i => i) 0 0 fuel
  have hinv := runTrace_invariant Aq Aq identityRows (fun i => i)
    0 0 fuel (identityRows_represents Aq) identityRows_support
    (fun _ _ h => h)
  have hrep : Represents Aq out.B out.U := hinv.1
  have hs : Support out.U out.π out.pivots.length := by
    simpa only [Nat.zero_add] using hinv.2.1
  have hπ : Function.Injective out.π := hinv.2.2
  obtain ⟨col, hunit, _⟩ := actualPrefix_nonsingular Aq fuel hfuel
  let ι := {t : Fin m // t.val < out.pivots.length}
  let M := (Fintype.card ι).factorial
  change ∀ i : Fin m, ∀ j : Fin k,
    (out.B i j).den ≤ M ^ (Fintype.card ι + 1) ∧
    (out.B i j).num.natAbs ≤
      (Fintype.card ι + 1) * M ^ (Fintype.card ι + 2)
  intro i j
  exact selectedRow_entry_bound A h01 out.B out.U out.π
    out.pivots.length hrep hs hπ col hunit i j

theorem factorial_le_two_pow_square (m t : ℕ) (ht : t ≤ m) :
    t.factorial ≤ 2 ^ ((m + 1) ^ 2) := by
  calc
    t.factorial ≤ m.factorial := Nat.factorial_le ht
    _ ≤ m ^ m := Nat.factorial_le_pow m
    _ ≤ (m + 1) ^ m := Nat.pow_le_pow_left (by omega) m
    _ ≤ 2 ^ (m * (m + 1)) :=
      CurrentAdditive.RationalBitBounds.coefficient_pow_bound m
    _ ≤ 2 ^ ((m + 1) ^ 2) := by
      apply Nat.pow_le_pow_right (by omega)
      nlinarith

theorem entry_components_fits_bits (m t : ℕ) (ht : t ≤ m) (q : ℚ)
    (hden : q.den ≤ t.factorial ^ (t + 1))
    (hnum : q.num.natAbs ≤ (t + 1) * t.factorial ^ (t + 2)) :
    let E := (m + 3) * (m + 1) ^ 2
    Nat.size q.den ≤ E + 1 ∧ Nat.size q.num.natAbs ≤ E + 1 := by
  let P := (m + 1) ^ 2
  let E := (m + 3) * P
  have hM := factorial_le_two_pow_square m t ht
  have htb : t + 1 ≤ 2 ^ P := by
    calc
      t + 1 ≤ m + 1 := by omega
      _ ≤ 2 ^ (m + 1) := le_of_lt Nat.lt_two_pow_self
      _ ≤ 2 ^ P := by
        apply Nat.pow_le_pow_right (by omega)
        dsimp [P]
        nlinarith
  have hdenpow : t.factorial ^ (t + 1) ≤ 2 ^ E := by
    calc
      t.factorial ^ (t + 1) ≤ (2 ^ P) ^ (t + 1) :=
        Nat.pow_le_pow_left hM _
      _ = 2 ^ (P * (t + 1)) := by rw [pow_mul]
      _ ≤ 2 ^ E := by
        apply Nat.pow_le_pow_right (by omega)
        dsimp [E, P]
        nlinarith
  have hnumpow : (t + 1) * t.factorial ^ (t + 2) ≤ 2 ^ E := by
    calc
      (t + 1) * t.factorial ^ (t + 2) ≤
          2 ^ P * (2 ^ P) ^ (t + 2) :=
        Nat.mul_le_mul htb (Nat.pow_le_pow_left hM _)
      _ = 2 ^ (P * (t + 3)) := by
        rw [pow_mul, pow_succ]
        exact mul_comm _ _
      _ ≤ 2 ^ E := by
        apply Nat.pow_le_pow_right (by omega)
        dsimp [E, P]
        nlinarith
  exact ⟨CurrentAdditive.RationalBitBounds.size_le_of_pow_bound
      (hden.trans hdenpow),
    CurrentAdditive.RationalBitBounds.size_le_of_pow_bound
      (hnum.trans hnumpow)⟩

theorem actualPrefix_entry_bits {m k : Nat}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (fuel : Nat) (hfuel : fuel ≤ k) :
    let out := runTrace (fun i j => (A i j : ℚ)) identityRows
      (fun i => i) 0 0 fuel
    ∀ i : Fin m, ∀ j : Fin k,
      Nat.size (out.B i j).den ≤ (m + 3) * (m + 1) ^ 2 + 1 ∧
      Nat.size (out.B i j).num.natAbs ≤
        (m + 3) * (m + 1) ^ 2 + 1 := by
  classical
  let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
  let out := runTrace Aq identityRows (fun i => i) 0 0 fuel
  let ι := {t : Fin m // t.val < out.pivots.length}
  let t := Fintype.card ι
  have ht : t ≤ m := by
    simpa [t] using Fintype.card_le_of_injective
      (fun u : ι => u.val) Subtype.val_injective
  change ∀ i : Fin m, ∀ j : Fin k,
    Nat.size (out.B i j).den ≤ (m + 3) * (m + 1) ^ 2 + 1 ∧
    Nat.size (out.B i j).num.natAbs ≤
      (m + 3) * (m + 1) ^ 2 + 1
  intro i j
  have hh := actualPrefix_entry_bound A h01 fuel hfuel i j
  exact entry_components_fits_bits m t ht (out.B i j) hh.1 hh.2

theorem materializedPrefix_entry_bits {m k : Nat}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (fuel : Nat) (hfuel : fuel ≤ k) (i : Fin m) (j : Fin k) :
    let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
    let B := (CurrentAdditive.MaterializedGauss.echelonMaterialized
      Aq 0 0 fuel).1
    Nat.size (B i j).den ≤ (m + 3) * (m + 1) ^ 2 + 1 ∧
    Nat.size (B i j).num.natAbs ≤
      (m + 3) * (m + 1) ^ 2 + 1 := by
  let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
  let out := runTrace Aq identityRows (fun i => i) 0 0 fuel
  have heq := runTrace_materialized Aq identityRows (fun i => i) 0 0 fuel
  have hB : out.B =
      (CurrentAdditive.MaterializedGauss.echelonMaterialized Aq 0 0 fuel).1 :=
    congrArg Prod.fst heq
  change Nat.size ((CurrentAdditive.MaterializedGauss.echelonMaterialized
      Aq 0 0 fuel).1 i j).den ≤ (m + 3) * (m + 1) ^ 2 + 1 ∧
    Nat.size ((CurrentAdditive.MaterializedGauss.echelonMaterialized
      Aq 0 0 fuel).1 i j).num.natAbs ≤
      (m + 3) * (m + 1) ^ 2 + 1
  rw [← hB]
  exact actualPrefix_entry_bits A h01 fuel hfuel i j

end CurrentAdditive.EliminationEntryBounds
