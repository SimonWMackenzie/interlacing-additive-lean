import Paper2.YaoCapacity
import CurrentAdditive.SmallBiasPatterns

/-!
# An actual short-protocol exclusion at the unadvanced cut

Source: v27 `sections/07a-small-bias.tex`, `yao:small-bias-escape`, in the
endpoint case `i = 0`. The finite family of possible output columns comes
from the actual normalized alternating protocol via `YaoCapacity`.

This deliberately leaves the general `i > 0` rectangle-retention argument
and the source stopping-rule arithmetic for a later module.
-/

namespace CurrentAdditive.SmallBias

open Paper2.Yao Workspace.Types.Protocol

variable {Ω Λ : Type*} [Fintype Λ]

/-- The initial-cut (`i=0`) form of the v27 protocol contradiction.
`hnum` is exactly the remaining numerical comparison between the verified
capacity and the small-bias pattern mass. The protocol, its output patterns,
and all column labels are actual objects, rather than a covering certificate. -/
theorem no_short_lookup_initial_cut
    (μ : Paper2.FiniteLaw Λ) (word : Λ → Ω → Bool)
    (ε : ℝ) (hε : 0 ≤ ε) (hμ : IsSmallBiased μ word ε)
    (I : Finset Ω) (t a : ℕ) (ht : 1 ≤ t)
    (P : StrictProtocol Ω Λ .alice)
    (hc : IsComplete P.toProtocol ((2 * t - 1) + 2 * a))
    (hn : CanonicalLastLeaves ((2 * t - 1) + 2 * a) P.toProtocol)
    (σ : ResponseStrategy t)
    (hσ : ∀ x : Ω, earlyStrategy t P.toProtocol x = σ)
    (hlookup : ∀ x ∈ I, ∀ ℓ, P.eval x ℓ = word ℓ x)
    (hnum : (2 ^ (2 ^ a + t - 2) : ℝ) *
      ((1 / 2 : ℝ) ^ I.card + ε) < 1) : False := by
  classical
  let F := columnCatalogue P.toProtocol
  have hF : F.card ≤ 2 ^ (2 ^ a + t - 2) :=
    common_strategy_capacity t a ht P.toProtocol hc P.alternates hn σ hσ
  have hcover : ∀ ℓ : Λ, ∃ z ∈ F, ∀ j ∈ I, word ℓ j = z j := by
    intro ℓ
    refine ⟨fun j => P.eval j ℓ, actualColumn_mem_catalogue P.toProtocol ℓ, ?_⟩
    intro j hj
    exact (hlookup j hj ℓ).symm
  have hall : μ.prob (fun ℓ => ∃ z ∈ F, ∀ j ∈ I, word ℓ j = z j) = 1 := by
    have h : (fun ℓ => ∃ z ∈ F, ∀ j ∈ I, word ℓ j = z j) = (fun _ => True) := by
      funext ℓ
      exact propext ⟨fun _ => trivial, fun _ => hcover ℓ⟩
    rw [h]
    exact μ.prob_true
  have hprob := patterns_prob_le μ word ε hε hμ I F
  have hfactor : 0 ≤ (1 / 2 : ℝ) ^ I.card + ε := by positivity
  have hcard : (F.card : ℝ) ≤ (2 ^ (2 ^ a + t - 2) : ℝ) := by exact_mod_cast hF
  have hmul := mul_le_mul_of_nonneg_right hcard hfactor
  rw [hall] at hprob
  linarith

private theorem initial_cut_numeric (d k : ℕ) (hk : d + 1 ≤ k) :
    (2 ^ d : ℝ) * ((1 / 2 : ℝ) ^ k + (1 / 2 : ℝ) ^ (d + 4)) < 1 := by
  have hbase : 0 ≤ (1 / 2 : ℝ) := by norm_num
  have hle : (1 / 2 : ℝ) ^ k ≤ (1 / 2 : ℝ) ^ (d + 1) :=
    pow_le_pow_of_le_one hbase (by norm_num) hk
  have hcancel (r : ℕ) :
      (2 ^ d : ℝ) * (1 / 2 : ℝ) ^ (d + r) = (1 / 2 : ℝ) ^ r := by
    rw [pow_add, ← mul_assoc]
    have hunit : (2 ^ d : ℝ) * (1 / 2 : ℝ) ^ d = 1 := by
      rw [← mul_pow]
      norm_num
    rw [hunit, one_mul]
  have hfirst : (2 ^ d : ℝ) * (1 / 2 : ℝ) ^ k ≤ 1 / 2 := by
    calc
      _ ≤ (2 ^ d : ℝ) * (1 / 2 : ℝ) ^ (d + 1) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
      _ = 1 / 2 := by rw [hcancel 1]; norm_num
  have hsecond : (2 ^ d : ℝ) * (1 / 2 : ℝ) ^ (d + 4) = 1 / 16 := by
    rw [hcancel 4]
    norm_num
  nlinarith

/-- Source `yao:small-bias-escape`, actual protocol contradiction at `i=0`.
Here `Q=2^a`, the source bias is `2^-(Q+t+2)`, and the retained row count
is at least `Q+t-1`; the latter is the row threshold given by the source
stopping-rule calculation in this endpoint case. -/
theorem no_short_lookup_initial_cut_v27
    (μ : Paper2.FiniteLaw Λ) (word : Λ → Ω → Bool)
    (I : Finset Ω) (t a : ℕ) (ht : 1 ≤ t)
    (hrows : 2 ^ a + t - 1 ≤ I.card)
    (hμ : IsSmallBiased μ word ((1 / 2 : ℝ) ^ (2 ^ a + t + 2)))
    (P : StrictProtocol Ω Λ .alice)
    (hc : IsComplete P.toProtocol ((2 * t - 1) + 2 * a))
    (hn : CanonicalLastLeaves ((2 * t - 1) + 2 * a) P.toProtocol)
    (σ : ResponseStrategy t)
    (hσ : ∀ x : Ω, earlyStrategy t P.toProtocol x = σ)
    (hlookup : ∀ x ∈ I, ∀ ℓ, P.eval x ℓ = word ℓ x) : False := by
  let d := 2 ^ a + t - 2
  have hA : 1 ≤ 2 ^ a := Nat.one_le_pow a 2 (by decide)
  have hd : d + 1 ≤ I.card := by dsimp [d]; omega
  have he : d + 4 = 2 ^ a + t + 2 := by dsimp [d]; omega
  have hnum : (2 ^ (2 ^ a + t - 2) : ℝ) *
      ((1 / 2 : ℝ) ^ I.card + (1 / 2 : ℝ) ^ (2 ^ a + t + 2)) < 1 := by
    simpa only [d, he] using initial_cut_numeric d I.card hd
  exact no_short_lookup_initial_cut μ word _ (by positivity) hμ I t a ht
    P hc hn σ hσ hlookup hnum

#print axioms CurrentAdditive.SmallBias.no_short_lookup_initial_cut
#print axioms CurrentAdditive.SmallBias.no_short_lookup_initial_cut_v27

end CurrentAdditive.SmallBias
