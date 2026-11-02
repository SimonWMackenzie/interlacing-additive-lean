import Paper2.SourceConstruction
import Paper2.SourceRationalSchedule

/-!
The literal indexed-incidence density bounds behind v12 Appendix C.
Parallel edge labels remain distinct. No simple-graph abstraction is used.
-/

namespace Paper2.SourceDensityScheduleScratch

open SourceItems SourceRationalScheduleScratch SourceProfileParameters

variable {V E : Type*} [Fintype V] [Nonempty V] [Fintype E]

theorem sum_degree_eq_twice_edges (edge : E → Bool → V) :
    (∑ v : V, SourceItems.degree edge v) = 2 * Fintype.card E := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (E × Bool)))
    (t := (Finset.univ : Finset V))
    (f := fun eb : E × Bool => edge eb.1 eb.2) (by simp)
  simpa only [Finset.card_univ, Fintype.card_prod, Fintype.card_bool,
    SourceItems.degree, Nat.mul_comm] using h.symm

theorem twice_edges_le_degree_vertices (edge : E → Bool → V) (Delta : ℕ)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Delta) :
    2 * Fintype.card E ≤ Delta * Fintype.card V := by
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun v _ => hdegree v)
  rw [sum_degree_eq_twice_edges] at hsum
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.mul_comm] using hsum

theorem edge_density_bounds (edge : E → Bool → V) (Delta : ℕ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Delta) :
    Fintype.card V ≤ 2 * Fintype.card E ∧
      2 * Fintype.card E ≤ Delta * Fintype.card V := by
  exact ⟨SourceConstruction.vertices_le_twice_edges edge hincident,
    twice_edges_le_degree_vertices edge Delta hdegree⟩

theorem edges_pos (edge : E → Bool → V)
    (hincident : ∀ v, ∃ e b, edge e b = v) :
    0 < Fintype.card E := by
  have h := SourceConstruction.vertices_le_twice_edges edge hincident
  have hv : 0 < Fintype.card V := Fintype.card_pos
  omega

theorem vertexTolerance_bounds (edge : E → Bool → V) (Delta : ℕ)
    (gamma : ℚ) (hgamma : 0 < gamma) (hDelta : 0 < Delta)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Delta) :
    gamma / (4 * Delta) ≤
      SourceRationalScheduleScratch.vertexTolerance (V := V) (E := E) gamma Delta ∧
    SourceRationalScheduleScratch.vertexTolerance (V := V) (E := E) gamma Delta
      ≤ gamma / 4 := by
  obtain ⟨hl, hu⟩ := edge_density_bounds edge Delta hincident hdegree
  have hv : (0 : ℚ) < Fintype.card V := by exact_mod_cast Fintype.card_pos (α := V)
  have hD : (0 : ℚ) < Delta := by exact_mod_cast hDelta
  have hlq : (Fintype.card V : ℚ) ≤ 2 * Fintype.card E := by exact_mod_cast hl
  have huq : (2 : ℚ) * Fintype.card E ≤ Delta * Fintype.card V := by
    exact_mod_cast hu
  unfold SourceRationalScheduleScratch.vertexTolerance
  constructor
  · apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [mul_nonneg hgamma.le (sub_nonneg.mpr hlq)]
  · apply (div_le_div_iff₀ (by positivity) (by norm_num)).2
    nlinarith [mul_nonneg hgamma.le (sub_nonneg.mpr huq)]

/-- A graph-only positive rational coefficient for the source deletion budget. -/
def etaConstant (Delta : ℕ) (gamma : ℚ) : ℚ :=
  min (min 1 (gamma / (4 * Delta))) ((1 / 256) * (gamma / 24)) / 65536

theorem etaConstant_pos (Delta : ℕ) (gamma : ℚ)
    (hDelta : 0 < Delta) (hgamma : 0 < gamma) :
    0 < etaConstant Delta gamma := by
  unfold etaConstant
  have hD : (0 : ℚ) < Delta := by exact_mod_cast hDelta
  positivity

theorem eta_bounds (edge : E → Bool → V) (L Delta : ℕ)
    (gamma : ℚ) (hgamma : 0 < gamma) (hDelta : 0 < Delta)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Delta) :
    etaConstant Delta gamma / width L ≤
      SourceRationalScheduleScratch.eta (V := V) (E := E) L gamma Delta ∧
    SourceRationalScheduleScratch.eta (V := V) (E := E) L gamma Delta ≤
      1 / (65536 * width L) := by
  have hvt := (vertexTolerance_bounds edge Delta gamma hgamma hDelta
    hincident hdegree).1
  have hw : (0 : ℚ) < width L := by
    exact_mod_cast (show 0 < width L by unfold width; positivity)
  have hmin : min (min (1 : ℚ) (gamma / (4 * Delta)))
      ((1 / 256) * (gamma / 24)) ≤
      min (min 1 (SourceRationalScheduleScratch.vertexTolerance
        (V := V) (E := E) gamma Delta))
        ((1 / 256) * SourceRationalScheduleScratch.witnessDensity gamma) := by
    rw [SourceRationalScheduleScratch.witnessDensity]
    exact min_le_min_right _ (min_le_min_left _ hvt)
  have htop : min (min (1 : ℚ) (SourceRationalScheduleScratch.vertexTolerance
      (V := V) (E := E) gamma Delta))
      ((1 / 256) * SourceRationalScheduleScratch.witnessDensity gamma) ≤ 1 :=
    (min_le_left _ _).trans (min_le_left _ _)
  constructor
  · unfold etaConstant SourceRationalScheduleScratch.eta
    have hd :
        (min (min (1 : ℚ) (gamma / (4 * Delta)))
          ((1 / 256) * (gamma / 24)) / 65536) / width L =
        min (min (1 : ℚ) (gamma / (4 * Delta)))
          ((1 / 256) * (gamma / 24)) / (65536 * width L) := by ring
    rw [hd]
    exact div_le_div_of_nonneg_right hmin
      (mul_nonneg (by norm_num : (0 : ℚ) ≤ 65536) hw.le)
  · unfold SourceRationalScheduleScratch.eta
    exact div_le_div_of_nonneg_right htop
      (mul_nonneg (by norm_num : (0 : ℚ) ≤ 65536) hw.le)

#print axioms sum_degree_eq_twice_edges
#print axioms edge_density_bounds
#print axioms vertexTolerance_bounds
#print axioms etaConstant_pos
#print axioms eta_bounds

end Paper2.SourceDensityScheduleScratch
