import CurrentAdditive.SupportReduction

/-!
Classical finite existence extension of v27 Appendix H, `det:code`.
The previously checked `SupportReduction.lean` is imported unchanged.
-/

namespace CurrentAdditive

open Finset

variable {ι κ : Type*} [Fintype κ]

/-- Excess columns in a finite rational feature matrix have a nonzero
dependence. The distinguished constant-one coordinate makes the dependence
affine, so its coefficients have zero sum. -/
theorem exists_rational_affine_dependence
    (s : Finset ι) (φ : ι → κ → ℚ) (j₀ : κ)
    (hconst : ∀ i ∈ s, φ i j₀ = 1)
    (hexcess : Fintype.card κ < s.card) :
    ∃ a : ι → ℚ,
      (∑ i ∈ s, a i = 0) ∧
      (∀ j : κ, ∑ i ∈ s, a i * φ i j = 0) ∧
      (∃ i ∈ s, a i ≠ 0) := by
  classical
  have hdep : ¬ LinearIndepOn ℚ (fun i : ι => φ i) s := by
    intro hli
    have hbound : s.card ≤ Fintype.card κ := by
      have h := hli.fintype_card_le_finrank
      simpa [Module.finrank_pi] using h
    exact (not_le_of_gt hexcess) hbound
  obtain ⟨a, hvector, hnonzero⟩ :=
    (not_linearIndepOn_finset_iff (R := ℚ) (v := fun i : ι => φ i)).mp hdep
  have hmom (j : κ) : ∑ i ∈ s, a i * φ i j = 0 := by
    have hj := congrArg (fun f : κ → ℚ => f j) hvector
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using hj
  have hsum : ∑ i ∈ s, a i = 0 := by
    calc
      ∑ i ∈ s, a i = ∑ i ∈ s, a i * φ i j₀ := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [hconst i hi]
      _ = 0 := hmom j₀
  exact ⟨a, hsum, hmom, hnonzero⟩

/-- Deleting zero weights does not change a weighted finite sum. -/
private theorem sum_positive_support_mul_eq
    (s : Finset ι) (w f : ι → ℚ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    ∑ i ∈ s.filter (fun i => 0 < w i), w i * f i =
      ∑ i ∈ s, w i * f i := by
  classical
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i hi hnot
  have hle : w i ≤ 0 := by
    apply le_of_not_gt
    intro hpos
    exact hnot (Finset.mem_filter.mpr ⟨hi, hpos⟩)
  have hzero : w i = 0 := le_antisymm hle (hw i hi)
  simp [hzero]

/-- Repeatedly eliminate dependent columns. The resulting finite rational
law has at most as many positive support points as feature coordinates and
preserves exactly the total mass and all feature moments. -/
theorem exists_compressed_positive_weights
    (φ : ι → κ → ℚ) (j₀ : κ)
    (hconst : ∀ i : ι, φ i j₀ = 1)
    (s : Finset ι) (w : ι → ℚ)
    (hw : ∀ i ∈ s, 0 < w i) :
    ∃ (t : Finset ι) (u : ι → ℚ),
      t ⊆ s ∧ t.card ≤ Fintype.card κ ∧
      (∀ i ∈ t, 0 < u i) ∧
      (∑ i ∈ t, u i = ∑ i ∈ s, w i) ∧
      (∀ j : κ, ∑ i ∈ t, u i * φ i j = ∑ i ∈ s, w i * φ i j) := by
  classical
  induction s using Finset.strongInductionOn generalizing w with
  | _ s ih =>
    by_cases hsmall : s.card ≤ Fintype.card κ
    · exact ⟨s, w, Subset.rfl, hsmall, hw, rfl, fun _ => rfl⟩
    · have hexcess : Fintype.card κ < s.card := Nat.lt_of_not_ge hsmall
      obtain ⟨a, hsum, hfeature, hnonzero⟩ :=
        exists_rational_affine_dependence s φ j₀ (fun i _ => hconst i) hexcess
      obtain ⟨τ, w', i₀, hτ, hi₀, hzero, hnonneg, hupdate,
        houtside, htotal, hmom, hcard⟩ :=
          rational_support_reduction_step s w a φ hw hsum hfeature hnonzero
      let s' : Finset ι := s.filter (fun i => 0 < w' i)
      have hss : s' ⊂ s := by
        apply Finset.filter_ssubset.mpr
        exact ⟨i₀, hi₀, by simp [hzero]⟩
      have hw' : ∀ i ∈ s', 0 < w' i := by
        intro i hi
        exact (Finset.mem_filter.mp hi).2
      obtain ⟨t, u, hts', hbound, hu, htotal', hmom'⟩ := ih s' hss w' hw'
      refine ⟨t, u, hts'.trans (Finset.filter_subset _ _), hbound, hu, ?_, ?_⟩
      · calc
          ∑ i ∈ t, u i = ∑ i ∈ s', w' i := htotal'
          _ = ∑ i ∈ s, w' i := by
            simpa only [mul_one] using
              (sum_positive_support_mul_eq s w' (fun _ => 1) hnonneg)
          _ = ∑ i ∈ s, w i := htotal
      · intro j
        calc
          ∑ i ∈ t, u i * φ i j = ∑ i ∈ s', w' i * φ i j := hmom' j
          _ = ∑ i ∈ s, w' i * φ i j :=
            sum_positive_support_mul_eq s w' (fun i => φ i j) hnonneg
          _ = ∑ i ∈ s, w i * φ i j := hmom j

#print axioms exists_rational_affine_dependence
#print axioms exists_compressed_positive_weights

end CurrentAdditive
