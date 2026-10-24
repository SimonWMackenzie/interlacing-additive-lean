import Paper2.SourceDensitySchedule
import Paper2.SourceRationalSchedule

/-!
Finite quantitative bounds for the *actual* v12 public dyadic `Q`.
The graph-derived lower bound on `eta` supplies the upper bound on `Q`;
no deletion-budget certificate is supplied by the caller.
-/

namespace Paper2.SourceQBounds

open SourceDensityScheduleScratch SourceRationalScheduleScratch
  RestorationPublicQScratch SourceProfileParameters

variable {V E : Type*} [Fintype V] [Nonempty V] [Fintype E]

/-- Dyadic rounding gives the exact threshold lower bound and a strict
factor-two upper bound when the manuscript's threshold is at least one. -/
theorem publicQ_threshold_bounds (L : ℕ) (hL : 1 ≤ L)
    (gamma : ℚ) (Delta : ℕ)
    (hgamma : 0 < gamma) (hDelta : 0 < Delta)
    (hE : 0 < Fintype.card E) :
    let δ := SourceRationalScheduleScratch.deltaU (V := V) (E := E)
      L gamma Delta
    let Q := SourceRationalScheduleScratch.publicQ (V := V) (E := E)
      L gamma Delta
    threshold L δ ≤ (Q : ℚ) ∧
      (Q : ℚ) < 2 * threshold L δ := by
  dsimp
  have hδ := SourceRationalScheduleScratch.deltaU_pos (V := V) (E := E)
    L gamma Delta hgamma hDelta hE
  have hdomain := SourceRationalScheduleScratch.manuscript_powTwo_domain
    (V := V) (E := E) L hL gamma Delta hgamma hDelta hE
  have hmeet := RestorationPublicQScratch.publicQ_meets L
    (SourceRationalScheduleScratch.deltaU (V := V) (E := E) L gamma Delta) hδ
  have hlower : threshold L
      (SourceRationalScheduleScratch.deltaU (V := V) (E := E) L gamma Delta) ≤
      (RestorationPublicQScratch.publicQ L
        (SourceRationalScheduleScratch.deltaU (V := V) (E := E)
          L gamma Delta) : ℚ) := by
    exact (div_le_iff₀ hδ).2 hmeet
  have hupper := RestorationPublicQScratch.publicQ_lt_twice_max L hL
    (SourceRationalScheduleScratch.deltaU (V := V) (E := E) L gamma Delta) hδ
  rw [max_eq_right hdomain] at hupper
  exact ⟨hlower, hupper⟩

/-- The graph density bound gives an explicit reciprocal bound for the
actual rational threshold, with `w` the scheduled restoration width. -/
theorem threshold_graph_upper (edge : E → Bool → V) (L Delta : ℕ)
    (gamma : ℚ) (hgamma : 0 < gamma) (hDelta : 0 < Delta)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Delta) :
    threshold L (SourceRationalScheduleScratch.deltaU (V := V) (E := E)
      L gamma Delta) ≤
      (1280 * L * width L * SourceRationalScheduleScratch.restorationWidth L : ℚ) /
        SourceDensityScheduleScratch.etaConstant Delta gamma := by
  let c := SourceDensityScheduleScratch.etaConstant Delta gamma
  let s := width L
  let w := SourceRationalScheduleScratch.restorationWidth L
  let η := SourceRationalScheduleScratch.eta (V := V) (E := E) L gamma Delta
  let δ := SourceRationalScheduleScratch.deltaU (V := V) (E := E) L gamma Delta
  have hc : 0 < c := SourceDensityScheduleScratch.etaConstant_pos
    Delta gamma hDelta hgamma
  have hs : (0 : ℚ) < s := by
    exact_mod_cast (show 0 < s by dsimp [s, width]; positivity)
  have hw : (0 : ℚ) < w := by
    exact_mod_cast (show 0 < w by dsimp [w, SourceRationalScheduleScratch.restorationWidth]; positivity)
  have hE := SourceDensityScheduleScratch.edges_pos edge hincident
  have hδ : 0 < δ := SourceRationalScheduleScratch.deltaU_pos
    (V := V) (E := E) L gamma Delta hgamma hDelta hE
  have hη : c / s ≤ η :=
    (SourceDensityScheduleScratch.eta_bounds edge L Delta gamma
      hgamma hDelta hincident hdegree).1
  have hcs : c ≤ η * s := by
    have hh := (div_le_iff₀ hs).1 hη
    nlinarith
  have hδeq : δ = η / (16 * w) := rfl
  have hcd : c ≤ 16 * s * w * δ := by
    rw [hδeq]
    field_simp
    nlinarith [hcs]
  have hprod : (80 * L : ℚ) * c ≤
      (1280 * L * s * w : ℚ) * δ := by
    have h80 : (0 : ℚ) ≤ (80 * L : ℕ) := by
      exact_mod_cast Nat.zero_le (80 * L)
    have hh := mul_le_mul_of_nonneg_left hcd
      h80
    nlinarith [hh]
  unfold threshold
  apply (div_le_div_iff₀ hδ hc).2
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hprod

/-- A fully graph-derived finite upper bound for the public dyadic `Q`.
The rational coefficient depends only on `Delta` and `gamma`. -/
theorem publicQ_graph_upper (edge : E → Bool → V) (L Delta : ℕ)
    (hL : 1 ≤ L) (gamma : ℚ) (hgamma : 0 < gamma)
    (hDelta : 0 < Delta)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Delta) :
    (SourceRationalScheduleScratch.publicQ (V := V) (E := E) L gamma Delta : ℚ) <
      (2560 * L * width L * SourceRationalScheduleScratch.restorationWidth L : ℚ) /
        SourceDensityScheduleScratch.etaConstant Delta gamma := by
  have hE := SourceDensityScheduleScratch.edges_pos edge hincident
  have hround := (publicQ_threshold_bounds (V := V) (E := E)
    L hL gamma Delta hgamma hDelta hE).2
  have hgraph := threshold_graph_upper edge L Delta gamma hgamma hDelta
    hincident hdegree
  calc
    _ < 2 * threshold L
        (SourceRationalScheduleScratch.deltaU (V := V) (E := E)
          L gamma Delta) := hround
    _ ≤ 2 * ((1280 * L * width L *
        SourceRationalScheduleScratch.restorationWidth L : ℚ) /
          SourceDensityScheduleScratch.etaConstant Delta gamma) := by
            exact mul_le_mul_of_nonneg_left hgraph (by norm_num)
    _ = _ := by ring

#print axioms publicQ_threshold_bounds
#print axioms threshold_graph_upper
#print axioms publicQ_graph_upper

end Paper2.SourceQBounds
