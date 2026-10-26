import CurrentAdditive.SmallBiasEscape
/-!
# The source's maximal feasible cut

Source: v27 `sections/07a-small-bias.tex`, `yao:bias-parameters`.
This module constructs the exact maximum appearing in the manuscript and
instantiates the checked all-feasible-cut lookup exclusion theorem.
-/

namespace CurrentAdditive.SmallBias

open Paper2.Yao Workspace.Types.Protocol

variable {Ω Λ : Type*} [Fintype Λ]

/-- The depth in Bob--Alice pairs remaining after the common early prefix. -/
def sourcePairDepth (b t : ℕ) : ℕ := b + 2 * t - 2

/-- Feasibility of following `j` additional Bob--Alice pairs. -/
def sourceCutFeasible (b t j : ℕ) : Prop :=
  2 ^ j * (t + j - 2) ≤ 2 ^ (t + b - 3)

instance sourceCutFeasible_decidable (b t : ℕ) :
    DecidablePred (sourceCutFeasible b t) := by
  intro j
  unfold sourceCutFeasible
  infer_instance

/-- The source's maximal feasible cut. `findGreatest` searches up to `a`;
the proof below shows that no index at or above `a` is feasible. -/
def sourceCutIndex (b t : ℕ) : ℕ :=
  Nat.findGreatest (sourceCutFeasible b t) (sourcePairDepth b t)

def sourceSuffixDepth (b t : ℕ) : ℕ :=
  sourcePairDepth b t - sourceCutIndex b t

private theorem zero_feasible (b t : ℕ) (ht : 4 ≤ t) :
    sourceCutFeasible b t 0 := by
  have hbase : t - 2 ≤ 2 ^ (t - 3) := by
    have hn : t - 3 + 1 = t - 2 := by omega
    have hp : t - 3 < 2 ^ (t - 3) := Nat.lt_two_pow_self
    omega
  have hexp : t - 3 ≤ t + b - 3 := by omega
  have hpow : 2 ^ (t - 3) ≤ 2 ^ (t + b - 3) :=
    pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) hexp
  simpa [sourceCutFeasible] using hbase.trans hpow

/-- No cut at or beyond the complete remaining depth is feasible. -/
theorem no_feasible_beyond_depth (b t j : ℕ) (ht : 4 ≤ t)
    (hj : sourcePairDepth b t ≤ j) : ¬ sourceCutFeasible b t j := by
  intro hf
  have hfactor : 1 ≤ t + j - 2 := by omega
  have hpow : 2 ^ j ≤ 2 ^ (t + b - 3) := by
    have hm := Nat.mul_le_mul_left (2 ^ j) hfactor
    have hlow : 2 ^ j ≤ 2 ^ j * (t + j - 2) := by simpa using hm
    exact hlow.trans hf
  have hexp : j ≤ t + b - 3 :=
    (pow_le_pow_iff_right₀ (by decide : (1 : ℕ) < 2)).mp hpow
  dsimp [sourcePairDepth] at hj
  omega

/-- Exact characterization of the source's `max` notation. -/
theorem sourceCutIndex_spec (b t : ℕ) (ht : 4 ≤ t) :
    sourceCutFeasible b t (sourceCutIndex b t) ∧
      sourceCutIndex b t < sourcePairDepth b t ∧
      ∀ j, sourceCutFeasible b t j → j ≤ sourceCutIndex b t := by
  classical
  have h0 := zero_feasible b t ht
  have hbound : sourceCutIndex b t ≤ sourcePairDepth b t := by
    unfold sourceCutIndex
    exact Nat.findGreatest_le _
  have hfeas : sourceCutFeasible b t (sourceCutIndex b t) := by
    unfold sourceCutIndex
    exact Nat.findGreatest_spec (Nat.zero_le _) h0
  have hlt : sourceCutIndex b t < sourcePairDepth b t := by
    by_contra hn
    exact (no_feasible_beyond_depth b t (sourceCutIndex b t) ht (by omega)) hfeas
  refine ⟨hfeas, hlt, ?_⟩
  intro j hj
  by_cases hja : j ≤ sourcePairDepth b t
  · unfold sourceCutIndex
    exact Nat.le_findGreatest hja hj
  · exact False.elim ((no_feasible_beyond_depth b t j ht (by omega)) hj)

/-- Literal `i=max{j: feasible j}` form of `yao:small-bias-escape`.
The output law may retain duplicate word labels, exactly as in the source. -/
theorem no_short_lookup_source_cut
    (μ : Paper2.FiniteLaw Λ) (word : Λ → Ω → Bool)
    (b t : ℕ) (ht : 4 ≤ t)
    (X : Finset Ω)
    (hX : 2 ^ sourcePairDepth b t + 2 ^ (t + b - 3) + 1 ≤ X.card)
    (hμ : IsSmallBiased μ word
      ((1 / 2 : ℝ) ^
        (2 ^ sourceSuffixDepth b t + t + sourceCutIndex b t + 2)))
    (P : Protocol Ω Λ Bool)
    (hc : IsComplete P ((2 * t - 1) + 2 * sourcePairDepth b t))
    (hP : Alternates .alice P)
    (σ : ResponseStrategy t)
    (hσ : ∀ x ∈ X, earlyStrategy t P x = σ)
    (hlookup : ∀ x ∈ X, ∀ ℓ, P.eval x ℓ = word ℓ x) : False := by
  obtain ⟨hf, hi, -⟩ := sourceCutIndex_spec b t ht
  have ha : sourceCutIndex b t + sourceSuffixDepth b t =
      b + 2 * t - 2 := by
    dsimp [sourceSuffixDepth, sourcePairDepth] at *
    omega
  exact no_short_lookup_v27 μ word b t (sourceCutIndex b t)
    (sourceSuffixDepth b t) ht ha hf X hX hμ P hc hP σ hσ hlookup

#print axioms CurrentAdditive.SmallBias.sourceCutIndex_spec
#print axioms CurrentAdditive.SmallBias.no_short_lookup_source_cut

end CurrentAdditive.SmallBias
