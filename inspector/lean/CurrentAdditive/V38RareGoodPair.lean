import CurrentAdditive.V38Moments
import CurrentAdditive.DeterministicSuffixLongSource

/-!
For the long rare-event suffix, select the exceptional set once from the
fixed event `Y`. Every later retained column set `K ⊆ Y` uses that same set.
The exact 8192-wise source law is never replaced by a conditioned product.
-/

namespace V38RareBoost

open Paper2
open CurrentAdditive
open CurrentAdditive.SuffixLong
open CurrentAdditive.SuffixLongSource

variable {Z S : Type*} [Fintype Z] [Fintype S]

theorem long_good_pair_after_fixed_conditioning
    (source : FiniteLaw S) (ν : FiniteLaw Z)
    {q : ℕ} (decode : S → Fin q → Z)
    (hwise : IsDWise 8192 source decode ν)
    (Y : Set S) (v τ : ℝ)
    (hv : 0 < v) (hv1 : v ≤ 1) (hτ : 0 < τ)
    (hY : v ≤ source.prob (· ∈ Y)) :
    ∃ E : Finset (Fin q), E.card ≤ V38Moments.exceptionCount v τ ∧
      (∀ J : Finset (Fin q),
        J ⊆ Finset.univ \ E → J.card ≤ 8 →
          projectionTV (condition source (· ∈ Y) (hv.trans_le hY))
            ν decode J ≤ V38Moments.epsilon v τ) ∧
      ∀ (b : ℕ) (hb : 5 ≤ b) (Good : Finset (Fin q))
        (hGood : 2^b + 1 ≤ Good.card),
        (∀ j ∈ Good, j ∉ E) →
        ∀ K : Set S, K ⊆ Y →
          1 / (2 : ℝ)^(b+1) ≤
            source.prob (· ∈ K) / source.prob (· ∈ Y) →
          ∃ i : Fin (2^(b-1)), (9/25 : ℝ) ≤
            (ν.iid 2).prob (· ∈ pairImage decode
              (sourceGoodSelector hb Good hGood) K i) := by
  obtain ⟨E, hcard, hTV⟩ :=
    V38Moments.conditioning_outside_exception
      source ν decode hwise Y v τ hv hτ hY
  refine ⟨E, hcard, hTV, ?_⟩
  intro b hb Good hGood hOutside K hK hcond
  let e := sourceGoodSelector hb Good hGood
  have he : Function.Injective e :=
    sourceGoodSelector_injective hb Good hGood
  have hgood (t : Fin (2*2^(b-1))) : e t ∉ E :=
    hOutside _ (sourceGoodSelector_mem hb Good hGood t)
  have hfourNat := (long_suffix_block_arithmetic b hb).2.2
  have hfour : (2 : ℝ)^(b+1) = 4 * (2^(b-1) : ℝ) := by
    exact_mod_cast hfourNat.symm
  have hcond' : 1/(4*(2^(b-1) : ℝ)) ≤
      source.prob (· ∈ K) / source.prob (· ∈ Y) := by
    simpa only [hfour] using hcond
  exact FiniteV35.pair_projections_good_source_epsilon
    source ν (long_suffix_block_arithmetic b hb).1 decode hwise
    e he Y K v τ hv hv1 hτ hY hK E hgood
    (by simpa only [V38Moments.epsilon_eq_old,
        FiniteV35Conditioning.paperEpsilon_eq] using hTV)
    (by simpa only [Nat.cast_pow] using hcond')

#print axioms long_good_pair_after_fixed_conditioning

end V38RareBoost
