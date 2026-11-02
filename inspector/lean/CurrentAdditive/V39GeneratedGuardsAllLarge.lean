import CurrentAdditive.V39GeneratedProfileGuards

/-! All generated source-profile guards at the accepted public cutoff.
The fixed positive deletion constant retains the source's explicit cap. -/

namespace CurrentAdditive.V39GeneratedGuardsAllLarge

open Paper2 V38Schedule

theorem source_profile_guards (γ c : ℚ) (Δ L n m : ℕ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hc : 0 < c)
    (hcmax : c ≤ min 1 (min (γ/(4*Δ)) (sourceZeta γ/256))/2^16)
    (hL : GeneratedCutoff.cutoffLog Δ c ≤ L) (hn : 0 < n)
    (hnN : n ≤ generatedN L) (hlow : n ≤ 2*m) (hdegree : 2*m ≤ Δ*n) :
    2 ≤ quarterCeil L ∧ 2 ≤ 4*L ∧
    (0 : ℝ) < ((generatedRho L : ℚ) : ℝ) ∧
    (0 : ℝ) < ((generatedX L : ℚ) : ℝ) ∧
    ((generatedX L : ℚ) : ℝ) ≤ 1 ∧
    (∀ j : Fin 2, (2 : ℝ)^(quarterCeil L-j.val)*((generatedRho L : ℚ) : ℝ) < 1) ∧
    (∀ j : Fin 2, (2 : ℝ)^(4*L-j.val)*((generatedX L : ℚ) : ℝ) < 1) ∧
    (∀ j : Fin 2, (2 : ℝ)^(quarterCeil L-j.val)*((generatedX L : ℚ) : ℝ) < 1) ∧
    (∀ j : Fin 2,
      (((2^((quarterCeil L-j.val)-1)+1)+V38Moments.exceptionCount ((generatedX L : ℚ) : ℝ) 1 : ℕ) : ℝ)*
        (1-(2 : ℝ)^(quarterCeil L-j.val)*((generatedRho L : ℚ) : ℝ)) ≤
        (generatedQ₁ L : ℝ)*((3/5 : ℝ)*(1/2 : ℝ)^j.val-(2 : ℝ)^(quarterCeil L-j.val)*((generatedRho L : ℚ) : ℝ))) ∧
    (∀ j : Fin 2,
      (((2^((4*L-j.val)-1)+1)+V38Moments.exceptionCount ((generatedX L : ℚ) : ℝ) 1 : ℕ) : ℝ)*
        (1-(2 : ℝ)^(4*L-j.val)*((generatedX L : ℚ) : ℝ)) ≤
        (generatedQ₂ L : ℝ)*((3/5 : ℝ)*(1/2 : ℝ)^j.val-(2 : ℝ)^(4*L-j.val)*((generatedX L : ℚ) : ℝ))) ∧
    (∀ j : Fin 2,
      (((2^((quarterCeil L-j.val)-1)+1)+V38Moments.exceptionCount ((generatedX L : ℚ) : ℝ) 1 : ℕ) : ℝ)*
        (1-(2 : ℝ)^(quarterCeil L-j.val)*((generatedX L : ℚ) : ℝ)) ≤
        (generatedS L : ℝ)*(SourceProfilesReference.templateThreshold ((3/5 : ℝ)*(1/2 : ℝ)^j.val)-
          (2 : ℝ)^(quarterCeil L-j.val)*((generatedX L : ℚ) : ℝ))) := by
  have ht := GeneratedCutoff.all_large_sources γ c Δ hγ hΔ hc hcmax
    L n m hL hn hnN hlow hdegree
  obtain ⟨ha,hb,hρ,hx,hx1,_,_,_,_⟩ :=
    V39GeneratedProfileGuards.scalar_parameters c (sourceDeltaV γ Δ n m) (sourceZeta γ) L m ht
  obtain ⟨hsa,hst,hsn⟩ :=
    V39GeneratedProfileGuards.scale_guards c (sourceDeltaV γ Δ n m) (sourceZeta γ) L m ht
  obtain ⟨hba,hbt,hbn⟩ :=
    V39GeneratedProfileGuards.population_budgets c (sourceDeltaV γ Δ n m) (sourceZeta γ) L m ht
  exact ⟨ha,hb,hρ,hx,hx1,hsa,hst,hsn,hba,hbt,hbn⟩

#print axioms source_profile_guards

end CurrentAdditive.V39GeneratedGuardsAllLarge
