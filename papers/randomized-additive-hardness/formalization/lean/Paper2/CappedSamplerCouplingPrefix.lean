import Paper2.CappedSampler
import Paper2.ProductProjections

/-!
# Fixed-width fair-bit blocks for adaptive capped sampling

Frozen source: v12 Appendix D, bounded random tapes paragraph (U15).
A state-dependent sampler can use the initial bits of a fixed-width block.
Discarding the unused suffix leaves precisely the required independent law,
including the zero-bit case. This is a marginal-law lemma, not an assumption
of independence after conditioning on successful execution.
-/

namespace Paper2

open scoped BigOperators

namespace FiniteLaw

/-- Transport a finite real-valued sum using the masses of all point fibres. -/
theorem sum_mul_comp_of_fibres {α β : Type*} [Fintype α] [Fintype β]
    (μ : FiniteLaw α) (ν : FiniteLaw β) (f : α → β)
    (hf : ∀ b, μ.prob (fun a => f a = b) = ν.weight b) (g : β → ℝ) :
    (∑ a, μ.weight a * g (f a)) = ∑ b, ν.weight b * g b := by
  classical
  calc
    _ = ∑ a, ∑ b, if f a = b then μ.weight a * g b else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      simp
    _ = ∑ b, ∑ a, if f a = b then μ.weight a * g b else 0 :=
      Finset.sum_comm
    _ = ∑ b, μ.prob (fun a => f a = b) * g b := by
      apply Finset.sum_congr rfl
      intro b _
      rw [prob, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp
    _ = _ := by simp_rw [hf]

end FiniteLaw

namespace CappedSampler

/-- Keep the first `b` bits of a `B`-bit block. -/
def prefixBits {b B : ℕ} (hb : b ≤ B) (x : Fin B → Bool) : Fin b → Bool :=
  fun i => x (Fin.castLE hb i)

/-- The retained prefix is a fresh fair-bit block, for every joint event. -/
theorem fairBits_prefix_prob {b B : ℕ} (hb : b ≤ B) (E : (Fin b → Bool) → Prop) :
    (fairBits B).prob (fun x => E (prefixBits hb x)) = (fairBits b).prob E := by
  have he : Function.Injective (Fin.castLE hb) := by
    intro i j hij
    exact Fin.ext (congrArg (fun k : Fin B => k.val) hij)
  exact FiniteLaw.pi_prob_restrict (fun _ : Fin B => fairBit) (Fin.castLE hb) he E

/-- Keep exactly the required prefix of each attempt in a bounded tape. -/
def prefixBitTape {b B : ℕ} (hb : b ≤ B) : (R : ℕ) → BitTape B R → BitTape b R
  | 0, _ => ()
  | R + 1, x => (prefixBits hb x.1, prefixBitTape hb R x.2)

/-- Prefix restriction preserves the full independent block law, not just
the individual bit marginals. -/
theorem bitTape_prefix_prob {b B : ℕ} (hb : b ≤ B) (R : ℕ)
    (E : BitTape b R → Prop) :
    (bitTapeLaw B R).prob (fun x => E (prefixBitTape hb R x)) =
      (bitTapeLaw b R).prob E := by
  induction R with
  | zero => rfl
  | succ R ih =>
    change ((fairBits B).prod (bitTapeLaw B R)).prob
      (fun x => E (prefixBits hb x.1, prefixBitTape hb R x.2)) =
      ((fairBits b).prod (bitTapeLaw b R)).prob E
    have hright : ((fairBits b).prod (bitTapeLaw b R)).prob E =
        ∑ a, (fairBits b).weight a * (bitTapeLaw b R).prob (fun y => E (a, y)) := by
      classical
      simp only [FiniteLaw.prob, FiniteLaw.prod, Fintype.sum_prod_type, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro y _
      split_ifs <;> simp
    rw [hright, FiniteLaw.prod_prob (fairBits B) (bitTapeLaw B R)
      (fun x y => E (prefixBits hb x, prefixBitTape hb R y))]
    calc
      _ = ∑ a, (fairBits B).weight a *
          (bitTapeLaw b R).prob (fun y => E (prefixBits hb a, y)) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [ih (fun y => E (prefixBits hb a, y))]
      _ = _ := by
        apply FiniteLaw.sum_mul_comp_of_fibres (fairBits B) (fairBits b) (prefixBits hb)
          ?_ (fun x => (bitTapeLaw b R).prob (fun y => E (x, y)))
        intro y
        rw [fairBits_prefix_prob hb (fun x => x = y)]
        exact FiniteLaw.prob_singleton _ y

/-- A state-dependent denominator can be implemented from a fixed-width block. -/
def runWideBits (D B R : ℕ) (hB : Nat.clog 2 D ≤ B) (t : BitTape B R) :
    Option (Fin D) := runBits D R (prefixBitTape hB R t)

/-- Every event in the wide-block implementation has the intended draw law. -/
theorem runWideBits_prob (D B R : ℕ) (hB : Nat.clog 2 D ≤ B)
    (E : Option (Fin D) → Prop) :
    (bitTapeLaw B R).prob (fun t => E (runWideBits D B R hB t)) =
      (bitTapeLaw (Nat.clog 2 D) R).prob (fun t => E (runBits D R t)) :=
  bitTape_prefix_prob hB R (fun t => E (runBits D R t))

/-- Uniform failure bound for every legal state-dependent denominator. -/
theorem runWideBits_failure_le (D B R : ℕ) (hD : 0 < D)
    (hB : Nat.clog 2 D ≤ B) :
    (bitTapeLaw B R).prob (fun t => runWideBits D B R hB t = none) ≤
      (1 / 2 : ℝ) ^ R := by
  rw [runWideBits_prob D B R hB (fun x => x = none)]
  exact bit_failure_le D R hD

/-- Every accepted value has the same exact truncated-geometric mass. -/
theorem runWideBits_accepted_exact (D B R : ℕ) (hD : 0 < D)
    (hB : Nat.clog 2 D ≤ B) (a : Fin D) :
    (bitTapeLaw B R).prob (fun t => runWideBits D B R hB t = some a) =
      (1 - rejectionMass D (ticketSize D) ^ R) / D := by
  rw [runWideBits_prob D B R hB (fun x => x = some a)]
  exact bit_accepted_exact D R hD a

end CappedSampler
end Paper2

#print axioms Paper2.CappedSampler.bitTape_prefix_prob
#print axioms Paper2.CappedSampler.runWideBits_failure_le
#print axioms Paper2.CappedSampler.runWideBits_accepted_exact
