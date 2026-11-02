import Paper2.RestorationCoverParameters

/-!
# Dyadic grouping of actual incoming protected densities

Frozen v12 `res:incoming`, lines 330--351. Densities are real numbers on
the original `Fin w` labels. The grouping does not assume a good group or
a large-enough number of labels as a certificate.
-/

namespace Paper2.ProtectedDensityGroups

open scoped BigOperators
open scoped Classical

private theorem dyadic_bin_cover (r : ℕ) (d : ℝ)
    (hd0 : 0 < d) (hd1 : d ≤ 1)
    (hdlow : (1 / 2 : ℝ) ^ (r + 1) ≤ d) :
    ∃ j : ℕ, j ≤ r + 1 ∧
      (1 / 2 : ℝ) ^ (j + 1) < d ∧ d ≤ (1 / 2 : ℝ) ^ j := by
  induction r generalizing d with
  | zero =>
    by_cases h : (1 / 2 : ℝ) < d
    · exact ⟨0, by omega, by norm_num at h ⊢; exact h, by simpa using hd1⟩
    · refine ⟨1, by omega, ?_, ?_⟩
      · norm_num at hdlow ⊢
        linarith
      · simpa using le_of_not_gt h
  | succ r ih =>
    by_cases h : (1 / 2 : ℝ) < d
    · exact ⟨0, by omega, by norm_num at h ⊢; exact h, by simpa using hd1⟩
    · have htwo : 0 < 2 * d := by linarith
      have htwo1 : 2 * d ≤ 1 := by linarith
      have htwolow : (1 / 2 : ℝ) ^ (r + 1) ≤ 2 * d := by
        rw [show r + 1 + 1 = r + 2 by omega, pow_succ] at hdlow
        nlinarith
      obtain ⟨j, hj, hjlo, hjup⟩ := ih (2 * d) htwo htwo1 htwolow
      refine ⟨j + 1, by omega, ?_, ?_⟩
      · rw [show j + 1 + 1 = (j + 1) + 1 by rfl, pow_succ]
        nlinarith
      · rw [pow_succ]
        nlinarith

private theorem sum_le_low_add_groups {ι γ : Type*}
    [Fintype ι] [Fintype γ] [DecidableEq ι]
    (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i)
    (Low : ι → Prop) (G : γ → Finset ι)
    (hcover : ∀ i, ¬ Low i → ∃ j, i ∈ G j) :
    (∑ i, d i) ≤
      (∑ i, if Low i then d i else 0) +
        ∑ j, ∑ i ∈ G j, d i := by
  classical
  have hswap : (∑ j, ∑ i ∈ G j, d i) =
      ∑ i, ∑ j, if i ∈ G j then d i else 0 := by
    calc
      _ = ∑ j, ∑ i, if i ∈ G j then d i else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        simp
      _ = _ := Finset.sum_comm
  rw [hswap, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hterm : ∀ j : γ, 0 ≤ if i ∈ G j then d i else 0 := by
    intro j
    by_cases h : i ∈ G j <;> simp [h, hd i]
  by_cases hi : Low i
  · simp [hi]
    exact Finset.sum_nonneg (fun j _ => hterm j)
  · simp [hi]
    obtain ⟨j, hj⟩ := hcover i hi
    have hsingle := Finset.single_le_sum (f := fun j : γ =>
      if i ∈ G j then d i else 0) (fun j _ => hterm j) (Finset.mem_univ j)
    simpa [hj] using hsingle

noncomputable def dyadicGroup {w r : ℕ} (d : Fin w → ℝ) (D : ℝ)
    (j : Fin (r + 2)) : Finset (Fin w) := by
  classical
  exact Finset.univ.filter (fun i =>
    D / (2 * (w : ℝ)) ≤ d i ∧
      (1 / 2 : ℝ) ^ (j.val + 1) < d i ∧ d i ≤ (1 / 2 : ℝ) ^ j.val)

private theorem high_mem_group {w r : ℕ} (hw : w = 2 ^ r)
    (d : Fin w → ℝ) (D : ℝ) (hD : 1 ≤ D)
    (hd : ∀ i, d i ≤ 1) (i : Fin w)
    (hi : D / (2 * (w : ℝ)) ≤ d i) :
    ∃ j : Fin (r + 2), i ∈ dyadicGroup d D j := by
  have hwpos : 0 < (w : ℝ) := by rw [hw]; positivity
  have hlow : (1 / 2 : ℝ) ^ (r + 1) ≤ d i := by
    have he : (1 / 2 : ℝ) ^ (r + 1) = 1 / (2 * (w : ℝ)) := by
      rw [hw, pow_succ]
      push_cast
      rw [one_div_pow]
      ring
    rw [he]
    have hden : 0 < 2 * (w : ℝ) := by positivity
    have hh : 1 / (2 * (w : ℝ)) ≤ D / (2 * (w : ℝ)) := by
      apply div_le_div_of_nonneg_right hD (by positivity)
    exact hh.trans hi
  have hip : 0 < d i := lt_of_lt_of_le (by positivity) hlow
  obtain ⟨j, hj, hjlo, hjup⟩ := dyadic_bin_cover r (d i) hip (hd i) hlow
  refine ⟨⟨j, by omega⟩, ?_⟩
  simpa only [dyadicGroup, Finset.mem_filter, Finset.mem_univ, true_and]
    using (And.intro hi (And.intro hjlo hjup))

/-- At most `r+2` explicit dyadic bins cover every density not discarded
by the source's `D/(2w)` cutoff. One bin carries at least its average share
of the undiscarded total. -/
theorem exists_dense_dyadic_group {w r : ℕ}
    (d : Fin w → ℝ) (hw : w = 2 ^ r)
    (hd0 : ∀ i, 0 ≤ d i) (hd1 : ∀ i, d i ≤ 1)
    (D : ℝ) (hD : D = ∑ i, d i) (hDone : 1 ≤ D) :
    ∃ j : Fin (r + 2),
      D / (2 * (r + 2 : ℝ)) ≤
        ∑ i ∈ dyadicGroup d D j, d i := by
  classical
  have hwpos : 0 < (w : ℝ) := by rw [hw]; positivity
  let low : Fin w → Prop := fun i => d i < D / (2 * (w : ℝ))
  let G : Fin (r + 2) → Finset (Fin w) := dyadicGroup d D
  have hcover : ∀ i, ¬ low i → ∃ j, i ∈ G j := by
    intro i hi
    exact high_mem_group hw d D hDone hd1 i (le_of_not_gt hi)
  have hdecomp := sum_le_low_add_groups d hd0 low G hcover
  rw [← hD] at hdecomp
  have hlow : (∑ i, if low i then d i else 0) ≤ D / 2 := by
    have hpoint (i : Fin w) :
        (if low i then d i else 0) ≤ D / (2 * (w : ℝ)) := by
      by_cases hi : low i
      · simp only [hi, ite_true]
        exact le_of_lt hi
      · simp only [hi, ite_false]
        positivity
    calc
      _ ≤ ∑ _i : Fin w, D / (2 * (w : ℝ)) :=
        Finset.sum_le_sum (fun i _ => hpoint i)
      _ = D / 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        field_simp
  have hsum : D / 2 ≤ ∑ j : Fin (r + 2), ∑ i ∈ G j, d i := by
    linarith
  have hconst : (∑ _j : Fin (r + 2), D / (2 * (r + 2 : ℝ))) = D / 2 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    have hrpos : (r + 2 : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  have hnonempty : (Finset.univ : Finset (Fin (r + 2))).Nonempty := by
    exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hex := Finset.exists_le_of_sum_le hnonempty
    (show (∑ j ∈ (Finset.univ : Finset (Fin (r + 2))),
      D / (2 * (r + 2 : ℝ))) ≤
      ∑ j ∈ (Finset.univ : Finset (Fin (r + 2))),
        ∑ i ∈ G j, d i by simpa [hconst] using hsum)
  obtain ⟨j, _, hj⟩ := hex
  exact ⟨j, hj⟩

/-- The chosen actual bin has a dyadic upper density and enough labelled
coordinates to carry its share of the total. -/
theorem density_group {w r : ℕ}
    (d : Fin w → ℝ) (hw : w = 2 ^ r)
    (hd0 : ∀ i, 0 ≤ d i) (hd1 : ∀ i, d i ≤ 1)
    (D : ℝ) (hD : D = ∑ i, d i) (hDone : 1 ≤ D) :
    ∃ j : Fin (r + 2),
      let δ : ℝ := (1 / 2 : ℝ) ^ j.val
      let V := dyadicGroup d D j
      0 < δ ∧ δ ≤ 1 ∧
        D / (2 * (w : ℝ)) ≤ δ ∧
        (∀ i ∈ V, δ / 2 < d i ∧ d i ≤ δ) ∧
        D / (2 * (r + 2 : ℝ)) ≤ (V.card : ℝ) * δ := by
  obtain ⟨j, hj⟩ := exists_dense_dyadic_group d hw hd0 hd1 D hD hDone
  refine ⟨j, ?_⟩
  dsimp only
  let δ : ℝ := (1 / 2 : ℝ) ^ j.val
  let V := dyadicGroup d D j
  have hδpos : 0 < δ := by dsimp [δ]; positivity
  have hδone : δ ≤ 1 := by
    dsimp [δ]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hV : V.Nonempty := by
    by_contra hn
    have he : V = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    rw [show dyadicGroup d D j = V by rfl, he] at hj
    simp at hj
    have hDpos : 0 < D / (2 * (r + 2 : ℝ)) := by positivity
    linarith
  obtain ⟨i, hi⟩ := hV
  have himem : D / (2 * (w : ℝ)) ≤ d i ∧
      (1 / 2 : ℝ) ^ (j.val + 1) < d i ∧ d i ≤ δ := by
    simpa only [V, dyadicGroup, Finset.mem_filter, Finset.mem_univ,
      true_and, δ] using hi
  have hδlow : D / (2 * (w : ℝ)) ≤ δ := himem.1.trans himem.2.2
  have hrows : ∀ i ∈ V, δ / 2 < d i ∧ d i ≤ δ := by
    intro i hi
    have h := (show D / (2 * (w : ℝ)) ≤ d i ∧
        (1 / 2 : ℝ) ^ (j.val + 1) < d i ∧ d i ≤ δ by
          simpa only [V, dyadicGroup, Finset.mem_filter, Finset.mem_univ,
            true_and, δ] using hi)
    have he : δ / 2 = (1 / 2 : ℝ) ^ (j.val + 1) := by
      rw [pow_succ]
      dsimp [δ]
      ring
    exact ⟨by rw [he]; exact h.2.1, h.2.2⟩
  have hsum : (∑ i ∈ V, d i) ≤ (V.card : ℝ) * δ := by
    have h := Finset.sum_le_card_nsmul V d δ (fun i hi => (hrows i hi).2)
    simpa only [nsmul_eq_mul] using h
  exact ⟨hδpos, hδone, hδlow, hrows, hj.trans hsum⟩

/-- Minimal dyadic size, selected from an actual endpoint budget. -/
theorem dyadic_size (r s κ : ℕ) (δ : ℝ)
    (hδone : δ ≤ 1)
    (hs : 0 < s) (hκ : 0 < κ)
    (hcap : 16 * (s : ℝ) * (κ : ℝ) ≤ (2 ^ r : ℕ) * δ) :
    ∃ k : ℕ, k ≤ r ∧
      16 * (s : ℝ) * (κ : ℝ) ≤ (2 ^ k : ℕ) * δ ∧
      (2 ^ k : ℕ) * δ < 32 * (s : ℝ) * (κ : ℝ) := by
  let T : ℝ := 16 * (s : ℝ) * (κ : ℝ)
  let p : ℕ → Prop := fun k => T ≤ (2 ^ k : ℕ) * δ
  have hex : ∃ k, p k := ⟨r, hcap⟩
  let k := Nat.find hex
  have hkle : k ≤ r := Nat.find_min' (H := hex) hcap
  have hmain : p k := Nat.find_spec hex
  have hT : 1 < T := by
    dsimp [T]
    have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
    have hκ' : (1 : ℝ) ≤ κ := by exact_mod_cast hκ
    nlinarith
  have hkpos : 0 < k := by
    by_contra hn
    have hk0 : k = 0 := by omega
    have hh := hmain
    simp only [p, hk0, pow_zero, Nat.cast_one, one_mul] at hh
    linarith
  have hprev : (2 ^ (k - 1) : ℕ) * δ < T := by
    have hn : k - 1 < k := by omega
    exact lt_of_not_ge (Nat.find_min hex hn)
  have hpow : (2 ^ k : ℕ) = 2 * (2 ^ (k - 1) : ℕ) := by
    have he : k - 1 + 1 = k := by omega
    conv_lhs => rw [← he, pow_succ]
    omega
  refine ⟨k, hkle, hmain, ?_⟩
  dsimp [T] at hprev ⊢
  rw [hpow]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  have htwice := mul_lt_mul_of_pos_left hprev (show (0 : ℝ) < 2 by norm_num)
  convert htwice using 1 <;> ring

/-- The exact source grouping and minimal dyadic size, with strict density
intervals and strict `|V| > u B`. Every chosen coordinate is an actual
original label. -/
theorem density_group_and_size {w r : ℕ}
    (d : Fin w → ℝ) (hw : w = 2 ^ r)
    (hd0 : ∀ i, 0 ≤ d i) (hd1 : ∀ i, d i ≤ 1)
    (s κ B : ℕ) (hs : 0 < s) (hκ : 0 < κ) (hB : 0 < B)
    (D : ℝ) (hD : D = ∑ i, d i)
    (hlarge : 512 * (B : ℝ) * (r + 2 : ℝ) * (s : ℝ) * (κ : ℝ) ≤ D) :
    ∃ (j : Fin (r + 2)) (k : ℕ),
      let δ : ℝ := (1 / 2 : ℝ) ^ j.val
      let V : Finset (Fin w) := dyadicGroup d D j
      let u : ℕ := 2 ^ k
      k ≤ r ∧ 0 < δ ∧ δ ≤ 1 ∧
        D / (2 * (w : ℝ)) ≤ δ ∧
        (∀ i ∈ V, δ / 2 < d i ∧ d i ≤ δ) ∧
        D / (2 * (r + 2 : ℝ)) ≤ (V.card : ℝ) * δ ∧
        16 * (s : ℝ) * (κ : ℝ) ≤ (u : ℝ) * δ ∧
        (u : ℝ) * δ < 32 * (s : ℝ) * (κ : ℝ) ∧
        u * B < V.card ∧ u ≤ w := by
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hκ1 : (1 : ℝ) ≤ κ := by exact_mod_cast hκ
  have hr1 : (1 : ℝ) ≤ (r + 2 : ℝ) := by
    exact_mod_cast (show 1 ≤ r + 2 by omega)
  have hprod : (1 : ℝ) ≤
      (B : ℝ) * (r + 2 : ℝ) * (s : ℝ) * (κ : ℝ) := by
    calc
      (1 : ℝ) = 1 * 1 * 1 * 1 := by ring
      _ ≤ (B : ℝ) * (r + 2 : ℝ) * (s : ℝ) * (κ : ℝ) := by
        gcongr
  have hDone : 1 ≤ D := by nlinarith [hprod]
  obtain ⟨j, hδpos, hδone, hδlow, hrows, hcount⟩ :=
    density_group d hw hd0 hd1 D hD hDone
  let δ : ℝ := (1 / 2 : ℝ) ^ j.val
  let V := dyadicGroup d D j
  have hwpos : 0 < (w : ℝ) := by rw [hw]; positivity
  have hLpos : 0 < (r + 2 : ℝ) := by positivity
  have hBpos : 0 < (B : ℝ) := by exact_mod_cast hB
  have hspos : 0 < (s : ℝ) := by exact_mod_cast hs
  have hκpos : 0 < (κ : ℝ) := by exact_mod_cast hκ
  have hwd : D ≤ 2 * (w : ℝ) * δ := by
    have hh := (div_le_iff₀ (by positivity : 0 < 2 * (w : ℝ))).mp hδlow
    nlinarith
  have hcap : 16 * (s : ℝ) * (κ : ℝ) ≤ (2 ^ r : ℕ) * δ := by
    rw [← hw]
    have hBL : (1 : ℝ) ≤ (B : ℝ) * (r + 2 : ℝ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hB1) (sub_nonneg.mpr hr1)]
    have hsk : 0 ≤ (s : ℝ) * (κ : ℝ) := by positivity
    have hh := mul_le_mul_of_nonneg_right hBL hsk
    nlinarith [hlarge, hwd, hh]
  obtain ⟨k, hk, hulo, huhi⟩ :=
    dyadic_size r s κ δ hδone hs hκ hcap
  let u := 2 ^ k
  have huw : u ≤ w := by
    dsimp [u]
    rw [hw]
    exact pow_le_pow_right₀ (by omega) hk
  have hVB : (u : ℝ) * (B : ℝ) < (V.card : ℝ) := by
    have hcount' : D ≤ 2 * (r + 2 : ℝ) * ((V.card : ℝ) * δ) := by
      have hh := (div_le_iff₀ (by positivity : 0 < 2 * (r + 2 : ℝ))).mp hcount
      nlinarith
    have hU : (u : ℝ) * δ < 32 * (s : ℝ) * (κ : ℝ) := huhi
    have hU' := mul_lt_mul_of_pos_right hU hBpos
    have hV' : 256 * (B : ℝ) * (s : ℝ) * (κ : ℝ) ≤
        (V.card : ℝ) * δ := by
      have hL := mul_le_mul_of_nonneg_left hcount' (show (0 : ℝ) ≤
        1 / (2 * (r + 2 : ℝ)) by positivity)
      nlinarith [hlarge]
    nlinarith [hU', hV', hδpos]
  have hnat : u * B < V.card := by exact_mod_cast hVB
  refine ⟨j, k, hk, hδpos, hδone, hδlow, hrows, hcount, ?_, ?_, ?_, ?_⟩
  · simpa only [u, δ] using hulo
  · simpa only [u, δ] using huhi
  · simpa only [u, V] using hnat
  · simpa only [u] using huw

end Paper2.ProtectedDensityGroups

#print axioms Paper2.ProtectedDensityGroups.exists_dense_dyadic_group
#print axioms Paper2.ProtectedDensityGroups.density_group
#print axioms Paper2.ProtectedDensityGroups.dyadic_size
#print axioms Paper2.ProtectedDensityGroups.density_group_and_size
