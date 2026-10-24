import Paper2.YaoStrategies

/-!
# Largest classes of identical early response strategies

Frozen source: Paper 2 v12, `sections/07-yao.tex`, `yao:lift` and
`yao:dominant-class` (lines 286--299).

The classes below are fibers of the early strategy extracted from an actual
protocol. A largest fiber is selected for each vertex. The exact strategy
count bounds its size, and an explicit no-proper-colouring hypothesis gives
an edge whose selected classes have a common strategy. The source reduction
and the remaining projection/sampling arguments are not assumed or proved
here. Empty sample arrays are allowed, with the size inequality then `0 ≤ 0`.
-/

namespace Paper2.Yao.LowerBound

open Workspace.Types.Protocol

universe u v w
variable {V : Type u} {Y : Type v} {E : Type w} {m K : ℕ}

/-- Selector labels at a vertex whose full early response tables equal `σ`.
Both hypothetical replies at each Bob turn are included in this equality. -/
def strategyClass (t : ℕ) (P : Protocol (V × Fin m) Y Bool)
    (v : V) (σ : ResponseStrategy t) : Finset (Fin m) :=
  Finset.univ.filter (fun z => earlyStrategy t P (v, z) = σ)

@[simp] theorem mem_strategyClass (t : ℕ) (P : Protocol (V × Fin m) Y Bool)
    (v : V) (σ : ResponseStrategy t) (z : Fin m) :
    z ∈ strategyClass t P v σ ↔ earlyStrategy t P (v, z) = σ := by
  simp [strategyClass]

/-- The exact fiber partition, including unrealized (empty) strategy fibers. -/
theorem strategyClass_card_sum (t : ℕ) (P : Protocol (V × Fin m) Y Bool) (v : V) :
    ∑ σ : ResponseStrategy t, (strategyClass t P v σ).card = m := by
  simpa [strategyClass] using
    Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin m))
      (Finset.univ : Finset (ResponseStrategy t)) (fun z => earlyStrategy t P (v, z))

/-- A largest fiber exists even when there are no actual sample labels:
the response-strategy alphabet itself is always nonempty. -/
theorem exists_largest_strategyClass (t : ℕ) (P : Protocol (V × Fin m) Y Bool)
    (v : V) :
    ∃ σ : ResponseStrategy t, ∀ τ, (strategyClass t P v τ).card ≤
      (strategyClass t P v σ).card := by
  have hne : (Finset.univ : Finset (ResponseStrategy t)).Nonempty :=
    ⟨earlyStrategy t (.leaf false : Protocol Unit Unit Bool) (), Finset.mem_univ _⟩
  obtain ⟨σ, _, hσ⟩ := Finset.exists_max_image Finset.univ
    (fun σ => (strategyClass t P v σ).card) hne
  exact ⟨σ, fun τ => hσ τ (Finset.mem_univ _)⟩

/-- A selected largest strategy fiber, used only in the lower-bound analysis.
It does not enter the matrix constructor. -/
noncomputable def dominantStrategy (t : ℕ) (P : Protocol (V × Fin m) Y Bool)
    (v : V) : ResponseStrategy t :=
  Classical.choose (exists_largest_strategyClass t P v)

noncomputable def dominantClass (t : ℕ) (P : Protocol (V × Fin m) Y Bool) (v : V) :
    Finset (Fin m) :=
  strategyClass t P v (dominantStrategy t P v)

theorem dominantClass_maximal (t : ℕ) (P : Protocol (V × Fin m) Y Bool)
    (v : V) (σ : ResponseStrategy t) :
    (strategyClass t P v σ).card ≤ (dominantClass t P v).card :=
  Classical.choose_spec (exists_largest_strategyClass t P v) σ

@[simp] theorem mem_dominantClass (t : ℕ) (P : Protocol (V × Fin m) Y Bool)
    (v : V) (z : Fin m) :
    z ∈ dominantClass t P v ↔ earlyStrategy t P (v, z) = dominantStrategy t P v :=
  mem_strategyClass t P v _ z

/-- Manuscript `yao:dominant-class` without rounded natural division:
`m ≤ S * |Z_v|`, for the exact `S = 2^(2^t-1)`. -/
theorem m_le_strategy_count_mul_dominantClass (t : ℕ)
    (P : Protocol (V × Fin m) Y Bool) (v : V) :
    m ≤ 2 ^ (2 ^ t - 1) * (dominantClass t P v).card := by
  calc
    m = ∑ σ : ResponseStrategy t, (strategyClass t P v σ).card :=
      (strategyClass_card_sum t P v).symm
    _ ≤ ∑ _σ : ResponseStrategy t, (dominantClass t P v).card :=
      Finset.sum_le_sum (fun σ _ => dominantClass_maximal t P v σ)
    _ = 2 ^ (2 ^ t - 1) * (dominantClass t P v).card := by
      simp [responseStrategy_card]

/-- Positive sample arrays have a genuinely retained row at every vertex. -/
theorem dominantClass_nonempty (t : ℕ) (P : Protocol (V × Fin m) Y Bool)
    (v : V) (hm : 0 < m) : (dominantClass t P v).Nonempty := by
  have h := m_le_strategy_count_mul_dominantClass t P v
  apply Finset.card_pos.mp
  by_contra hn
  have hz : (dominantClass t P v).card = 0 := by omega
  rw [hz, Nat.mul_zero] at h
  omega

/-- Encode the full response table as one of exactly `2^(2^t-1)` colours. -/
noncomputable def strategyCode (t : ℕ) : ResponseStrategy t ≃ Fin (2 ^ (2 ^ t - 1)) :=
  Fintype.equivFinOfCardEq (responseStrategy_card t)

/-- The explicit source NO promise is applied to the selected strategies.
No vertex of the edge is chosen, so the statement also handles `K=0`
without silently assuming an inhabited edge. -/
theorem exists_monochromatic_dominantStrategy (t : ℕ)
    (P : Protocol (V × Fin m) Y Bool) (edges : E → Fin K ↪ V)
    (hno : ∀ colour : V → Fin (2 ^ (2 ^ t - 1)),
      ∃ e c, ∀ i, colour (edges e i) = c) :
    ∃ e σ, ∀ i, dominantStrategy t P (edges e i) = σ := by
  obtain ⟨e, c, hc⟩ := hno (fun v => strategyCode t (dominantStrategy t P v))
  refine ⟨e, (strategyCode t).symm c, ?_⟩
  intro i
  apply (strategyCode t).injective
  simpa using hc i

/-- All actual labels in the selected largest classes on one real edge
share one full early response strategy. Their proven size bounds are retained.
This is the concrete interface consumed by the lookup restriction step. -/
theorem exists_monochromatic_dominantClasses (t : ℕ)
    (P : Protocol (V × Fin m) Y Bool) (edges : E → Fin K ↪ V)
    (hno : ∀ colour : V → Fin (2 ^ (2 ^ t - 1)),
      ∃ e c, ∀ i, colour (edges e i) = c) :
    ∃ e σ, (∀ i, dominantStrategy t P (edges e i) = σ) ∧
      (∀ i z, z ∈ dominantClass t P (edges e i) → earlyStrategy t P (edges e i, z) = σ) ∧
      (∀ i, m ≤ 2 ^ (2 ^ t - 1) * (dominantClass t P (edges e i)).card) := by
  obtain ⟨e, σ, hσ⟩ := exists_monochromatic_dominantStrategy t P edges hno
  refine ⟨e, σ, hσ, ?_, fun i => m_le_strategy_count_mul_dominantClass t P (edges e i)⟩
  intro i z hz
  exact (mem_dominantClass t P (edges e i) z).mp hz |>.trans (hσ i)

end Paper2.Yao.LowerBound
