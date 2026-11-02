import CurrentAdditive.DeterministicParameters
import CurrentAdditive.IndexedTemplateSection

/-!
Private continuation of v27 Appendix I `det:schedule` (lines 41–52) and
`det:parameters` (lines 746–825). The source's order-256 template-flag
constant is instantiated exactly. The cutoff depends only on the fixed
graph promise constants, while the public exponent accommodates the input
vertex count. The bounded-degree inequality pays for the edge count in the
graph-width guard. No property of the base matrix or round is a
premise of the numerical schedule.
-/

namespace CurrentAdditive.DeterministicAdmissibility

open CurrentAdditive.DeterministicParameters

/-- Appendix I line 52 fixes this degree for every indexed source call. -/
def sourceIndependenceDegree : ℕ := 8192

theorem source_degree_for_conditioning :
    8 * 1024 = sourceIndependenceDegree := by
  norm_num [sourceIndependenceDegree]

theorem source_degree_for_flag_moment :
    8 * 256 ≤ sourceIndependenceDegree := by
  norm_num [sourceIndependenceDegree]

/-- Appendix I line 594, with `λ = 255/256`. This is a rational number.
It is fixed by the order-256 moment calculation and is independent of the
graph, base matrix, and amplification round. -/
def sourceC128 : ℚ :=
  2 * (64 / ((255 / 256 : ℚ) - 1 / 2) ^ 2) ^ 128

/-- The integer envelope used by the already-proved natural-number cutoff.
It can be evaluated by rational arithmetic. -/
def sourceC128Ceil : ℕ := Nat.ceil sourceC128

theorem sourceC128_le_ceiling : sourceC128 ≤ sourceC128Ceil := by
  exact Nat.le_ceil sourceC128

/-- The cutoff is fixed once degree and density constants are fixed. -/
def sourceCutoffLog (Δ : ℕ) (γ : ℚ) : ℕ :=
  cutoffLog Δ sourceC128Ceil γ

def sourceCutoffSize (Δ : ℕ) (γ : ℚ) : ℕ :=
  N (sourceCutoffLog Δ γ)

/-- The public, computable exponent pads the graph's vertices. The existing
graph-width theorem uses `2*m ≤ Δ*n` and does not require `m ≤ N`. -/
def publicLog (n Δ : ℕ) (γ : ℚ) : ℕ :=
  chosenLog n Δ sourceC128Ceil γ

theorem publicLog_ge_cutoff (n Δ : ℕ) (γ : ℚ) :
    sourceCutoffLog Δ γ ≤ publicLog n Δ γ := by
  exact chosenLog_ge_cutoff n Δ sourceC128Ceil γ

theorem public_schedule (n m Δ : ℕ) (γ : ℚ)
    (hΔ : 0 < Δ) (hγ : 0 < γ) (hm : 0 < m)
    (hdegree : 2 * m ≤ Δ * n) :
    n ≤ N (publicLog n Δ γ) ∧
    Admissible (publicLog n Δ γ) Δ n m sourceC128Ceil γ ∧
    N (publicLog n Δ γ) ≤ 2 * max n (sourceCutoffSize Δ γ) := by
  have hsize := chosen_dyadic_size n Δ sourceC128Ceil γ
  have hn : n ≤ N (publicLog n Δ γ) := hsize.1
  have hAdm := admissible_from_cutoff
    (publicLog n Δ γ) Δ n m sourceC128Ceil γ
    hΔ hγ hm hdegree (publicLog_ge_cutoff n Δ γ) hn
  exact ⟨hn, hAdm, hsize.2⟩

/-- A caller may set a larger public floor, for example the maximum of the
graph's vertex count and an encoded formula's variable count. The
admissibility record continues to refer to the actual graph counts. -/
theorem public_schedule_at_floor (floor n m Δ : ℕ) (γ : ℚ)
    (hΔ : 0 < Δ) (hγ : 0 < γ) (hm : 0 < m)
    (hdegree : 2 * m ≤ Δ * n) (hnfloor : n ≤ floor) :
    floor ≤ N (publicLog floor Δ γ) ∧
    Admissible (publicLog floor Δ γ) Δ n m sourceC128Ceil γ ∧
    N (publicLog floor Δ γ) ≤ 2 * max floor (sourceCutoffSize Δ γ) := by
  have hsize := chosen_dyadic_size floor Δ sourceC128Ceil γ
  have hgraph : n ≤ N (publicLog floor Δ γ) := hnfloor.trans hsize.1
  have hAdm := admissible_from_cutoff
    (publicLog floor Δ γ) Δ n m sourceC128Ceil γ
    hΔ hγ hm hdegree (publicLog_ge_cutoff floor Δ γ) hgraph
  exact ⟨hsize.1, hAdm, hsize.2⟩

/-- The exact source coefficient passes the moment test, not merely its
natural-number envelope. -/
theorem source_moment_check (L Δ n m : ℕ) (γ : ℚ)
    (h : Admissible L Δ n m sourceC128Ceil γ) :
    sourceC128 / (s L : ℚ) ^ 128 ≤ θ L / 4 := by
  have hs : (0 : ℚ) ≤ (s L : ℚ) ^ 128 := by positivity
  exact (div_le_div_of_nonneg_right sourceC128_le_ceiling hs).trans h.moment

/-- The exact source coefficient is the one occurring in the actual
metadata half-template tail theorem, after normalizing by `m^128`. -/
theorem source_tail_expression (m : ℕ) (hm : 0 < m) :
    2 * ((64 : ℝ) * m) ^ 128 /
      (((255 / 256 : ℝ) - 1 / 2) * m) ^ 256 =
      (sourceC128 : ℝ) / (m : ℝ) ^ 128 := by
  have ha : (255 / 256 : ℝ) - 1 / 2 ≠ 0 := by norm_num
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hc : (sourceC128 : ℝ) =
      2 * (64 / (((255 / 256 : ℝ) - 1 / 2) ^ 2)) ^ 128 := by
    norm_num [sourceC128]
  rw [hc]
  field_simp

/-- Numeric guard passed to `incoming_complete_template_section` for the
actual flag stream. Its caller obtains `s≤m` from the dyadic group size. -/
theorem source_flag_tail_guard (L Δ n edges m : ℕ) (γ : ℚ)
    (h : Admissible L Δ n edges sourceC128Ceil γ)
    (hsm : s L ≤ m) :
    2 * ((64 : ℝ) * m) ^ 128 /
      (((255 / 256 : ℝ) - 1 / 2) * m) ^ 256 ≤ (θ L : ℝ) / 4 := by
  have hm : 0 < m := (s_pos L).trans_le hsm
  rw [source_tail_expression m hm]
  have hq := source_moment_check L Δ n edges γ h
  have hr : (sourceC128 : ℝ) / (s L : ℝ) ^ 128 ≤ (θ L : ℝ) / 4 := by
    exact_mod_cast hq
  have hs0 : (0 : ℝ) < (s L : ℝ) ^ 128 := by
    have hh : (0 : ℝ) < (s L : ℝ) := by exact_mod_cast s_pos L
    positivity
  have hsmR : (s L : ℝ) ^ 128 ≤ (m : ℝ) ^ 128 := by
    have hh : (s L : ℝ) ≤ m := by exact_mod_cast hsm
    gcongr
  have hc : (0 : ℝ) ≤ (sourceC128 : ℝ) := by
    norm_num [sourceC128]
  have hdiv : (sourceC128 : ℝ) / (m : ℝ) ^ 128 ≤
      (sourceC128 : ℝ) / (s L : ℝ) ^ 128 := by
    exact div_le_div_of_nonneg_left hc hs0 hsmR
  exact hdiv.trans hr

/-- A conservative decidable integer test. Passing it implies every
manuscript numerical guard; the test itself does not evaluate real powers. -/
def safeTest (L n Δ : ℕ) (γ : ℚ) : Bool :=
  decide (sourceCutoffLog Δ γ ≤ L ∧ n ≤ N L)

theorem safeTest_passes (L n m Δ : ℕ) (γ : ℚ)
    (hΔ : 0 < Δ) (hγ : 0 < γ) (hm : 0 < m)
    (hdegree : 2 * m ≤ Δ * n)
    (h : safeTest L n Δ γ = true) :
    Admissible L Δ n m sourceC128Ceil γ := by
  have hh : sourceCutoffLog Δ γ ≤ L ∧ n ≤ N L := by
    simpa [safeTest] using h
  exact admissible_from_cutoff L Δ n m sourceC128Ceil γ
    hΔ hγ hm hdegree hh.1 hh.2

theorem publicLog_safeTest (n Δ : ℕ) (γ : ℚ) :
    safeTest (publicLog n Δ γ) n Δ γ = true := by
  have hsize := chosen_dyadic_size n Δ sourceC128Ceil γ
  have hn : n ≤ N (publicLog n Δ γ) := by
    simpa only [publicLog] using hsize.1
  simp [safeTest, publicLog_ge_cutoff, hn]

/-- The mathematically first exponent passing the exact source guards
also obeys the paper's two-times bound. Its inherited `Nat.find` definition
is noncomputable because the exact exceptional count uses real powers;
`publicLog` is the constructive choice above. -/
theorem first_exact_source_bound (n m Δ : ℕ) (γ : ℚ)
    (hΔ : 0 < Δ) (hγ : 0 < γ) (hm : 0 < m)
    (hdegree : 2 * m ≤ Δ * n) :
    N (firstAcceptedLog n Δ m sourceC128Ceil γ hΔ hγ hm hdegree) ≤
      2 * max n (sourceCutoffSize Δ γ) := by
  exact firstAccepted_dyadic_bound n Δ m sourceC128Ceil γ
    hΔ hγ hm hdegree

#print axioms sourceC128_le_ceiling
#print axioms source_degree_for_conditioning
#print axioms public_schedule
#print axioms public_schedule_at_floor
#print axioms source_moment_check
#print axioms source_tail_expression
#print axioms source_flag_tail_guard
#print axioms safeTest_passes
#print axioms publicLog_safeTest
#print axioms first_exact_source_bound

end CurrentAdditive.DeterministicAdmissibility
