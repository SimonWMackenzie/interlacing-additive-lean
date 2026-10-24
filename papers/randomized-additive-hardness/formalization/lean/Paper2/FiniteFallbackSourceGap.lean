import Paper2.FiniteFallbackOutput

/-!+# The actual source promise for the finite exceptional branch

Frozen v12 Appendix D, finite-source branch. The constructor makes its own
finite colouring decision; a positive source gap is used only to analyse
its NO output. This does not prove the schedule cutoff or machine costs.
-/

namespace Paper2.FiniteFallbackSourceGap

open FiniteFallbackOutput Workspace.Types.CommComplexity

theorem not_threeColourable_of_gap {v e : ℕ}
    (edge : Fin e → Bool → Fin v) (gamma : ℝ)
    (hgamma : 0 < gamma) (he : 0 < e)
    (gap : ∀ colour : Fin v → Fin 3, gamma * e ≤
      ((Finset.univ.filter (fun z => colour (edge z false) =
        colour (edge z true))).card : ℝ)) :
    ¬ ThreeColourable edge := by
  rintro ⟨colour, proper⟩
  have hempty : (Finset.univ.filter (fun z : Fin e =>
      colour (edge z false) = colour (edge z true))) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact proper z (Finset.mem_filter.mp hz).2
  have hbad := gap colour
  rw [hempty] at hbad
  simp only [Finset.card_empty, Nat.cast_zero] at hbad
  have hpos : (0 : ℝ) < gamma * e :=
    mul_pos hgamma (by exact_mod_cast he)
  exact (not_le_of_gt hpos) hbad

/-- The original graph gap forces exact cost `k` in the literal fallback
output, including the one-row branch `k=1`. -/
theorem fallback_source_no_D {v e : ℕ}
    (edge : Fin e → Bool → Fin v) (gamma : ℝ)
    (hgamma : 0 < gamma) (he : 0 < e)
    (gap : ∀ colour : Fin v → Fin 3, gamma * e ≤
      ((Finset.univ.filter (fun z => colour (edge z false) =
        colour (edge z true))).card : ℝ))
    (k : ℕ) (hk : 1 ≤ k) :
    D (fallbackTable edge k).matrix = budget + k := by
  have hn := not_threeColourable_of_gap edge gamma hgamma he gap
  by_cases h1 : k = 1
  · subst k
    simpa [budget] using fallback_no_one_D edge hn
  · simpa [budget] using fallback_no_D edge k (by omega) hn

#print axioms not_threeColourable_of_gap
#print axioms fallback_source_no_D

end Paper2.FiniteFallbackSourceGap
