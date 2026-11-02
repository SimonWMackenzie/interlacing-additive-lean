import CurrentAdditive.SmallBiasStopping
import Paper2.YaoEventsNormalization

/-!
# Arbitrary short protocols and retained lookup rows

Source: v27 `sections/07-yao.tex`, `yao:lift`, and
`sections/07a-small-bias.tex`, `yao:small-bias-escape`.
This is the actual cost-to-complete-depth normalization bridge, using
Paper2's checked padding and early-strategy preservation theorem.
-/

namespace CurrentAdditive.SmallBias

open Paper2.Yao Workspace.Types.Protocol

variable {Ω Λ : Type*} [Fintype Λ]

/-- Small bias survives an injective reindexing of lookup coordinates. -/
theorem smallBias_comp_injective {Ω' : Type*} (μ : Paper2.FiniteLaw Λ)
    (word : Λ → Ω → Bool) (ε : ℝ) (hμ : IsSmallBiased μ word ε)
    (f : Ω' → Ω) (hf : Function.Injective f) :
    IsSmallBiased μ (fun ℓ x => word ℓ (f x)) ε := by
  classical
  intro S hS
  have hchar (ℓ : Λ) :
      parityChar S (fun x => word ℓ (f x)) = parityChar (S.image f) (word ℓ) := by
    unfold parityChar
    rw [Finset.prod_image hf.injOn]
  have hne : (S.image f).Nonempty := hS.image f
  simpa only [parityCorr, hchar] using hμ (S.image f) hne

/-- A protocol of cost at most the v27 forbidden depth is padded and
normalized before applying the source's maximal-cut theorem. No complete
tree, final-bit convention, or suffix catalogue is a premise here. -/
theorem no_short_lookup_bounded_cost
    (μ : Paper2.FiniteLaw Λ) (word : Λ → Ω → Bool)
    (b t : ℕ) (ht : 4 ≤ t)
    (X : Finset Ω)
    (hX : 2 ^ sourcePairDepth b t + 2 ^ (t + b - 3) + 1 ≤ X.card)
    (hμ : IsSmallBiased μ word
      ((1 / 2 : ℝ) ^
        (2 ^ sourceSuffixDepth b t + t + sourceCutIndex b t + 2)))
    (P : Protocol Ω Λ Bool)
    (hcost : P.cost ≤ 2 * (b + 3 * t - 3) + 1)
    (ha : Alternates .alice P)
    (σ : ResponseStrategy t)
    (hσ : ∀ x ∈ X, earlyStrategy t P x = σ)
    (hlookup : ∀ x ∈ X, ∀ ℓ, P.eval x ℓ = word ℓ x) : False := by
  let r := b + 3 * t - 3
  have hguard : 2 * t < 2 * r + 1 := by dsimp [r]; omega
  obtain ⟨Q, hcQ, haQ, _, hsQ, heQ⟩ :=
    exists_normalized_preserving_strategy t r P ha hcost hguard
  have hd : 2 * r + 1 = (2 * t - 1) + 2 * sourcePairDepth b t := by
    dsimp [r, sourcePairDepth]
    omega
  have hcQ' : IsComplete Q ((2 * t - 1) + 2 * sourcePairDepth b t) := by
    simpa only [hd] using hcQ
  exact no_short_lookup_source_cut μ word b t ht X hX hμ Q hcQ' haQ σ
    (by intro x hx; exact (hsQ x).trans (hσ x hx))
    (by intro x hx ℓ; exact (heQ x ℓ).trans (hlookup x hx ℓ))

#print axioms CurrentAdditive.SmallBias.smallBias_comp_injective
#print axioms CurrentAdditive.SmallBias.no_short_lookup_bounded_cost

/-- The v12 payload-short-failure predicate is impossible for any labelled
array list whose original uniform law satisfies the v27 bias bound. The
proof restricts bias to the actual retained payload positions, then uses
the bounded-cost normalization above. -/
theorem no_payloadShortProtocolFailure_of_small_bias
    {X : Type*} [Fintype X] [DecidableEq X]
    (b t n : ℕ) (ht : 4 ≤ t)
    (μ : Paper2.FiniteLaw (Fin n)) (W : Fin n → X → Bool)
    (hμ : IsSmallBiased μ W
      ((1 / 2 : ℝ) ^
        (2 ^ sourceSuffixDepth b t + t + sourceCutIndex b t + 2))) :
    ¬ payloadShortProtocolFailure (b + 3 * t - 3) t
      (payloadMinimum b t) n W := by
  classical
  intro hfail
  obtain ⟨J, hJ, P, hcost, ha, ⟨σ, hσ⟩, hlookup⟩ := hfail
  have hmin : payloadMinimum b t =
      2 ^ sourcePairDepth b t + 2 ^ (t + b - 3) + 1 := by
    have he : b + (t - 4) + 1 = t + b - 3 := by omega
    unfold payloadMinimum payloadDelta sourcePairDepth
    rw [← he, pow_succ]
    omega
  have hJ' : 2 ^ sourcePairDepth b t + 2 ^ (t + b - 3) + 1 ≤
      (Finset.univ : Finset J).card := by
    simpa only [Finset.card_univ, Fintype.card_coe, hmin] using hJ
  have hμJ : IsSmallBiased μ (fun ℓ (x : J) => W ℓ x.val)
      ((1 / 2 : ℝ) ^
        (2 ^ sourceSuffixDepth b t + t + sourceCutIndex b t + 2)) :=
    smallBias_comp_injective μ W _ hμ Subtype.val Subtype.val_injective
  exact no_short_lookup_bounded_cost μ (fun ℓ (x : J) => W ℓ x.val)
    b t ht Finset.univ hJ' hμJ P hcost ha σ
    (by intro x _; exact hσ x)
    (by intro x _ ℓ; exact hlookup x ℓ)

#print axioms CurrentAdditive.SmallBias.no_payloadShortProtocolFailure_of_small_bias

end CurrentAdditive.SmallBias
