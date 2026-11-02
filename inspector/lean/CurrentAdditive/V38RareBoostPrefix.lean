import CurrentAdditive.RestrictionBridge

/-!
The actual arbitrary-speaker rare-event prefix. It is independent of the
base profile. The suffix theorem is the separate local
obligation: this file proves that it suffices for the full rare boost, with
the same original conditional law and no post-prefix independence premise.
-/

namespace V38RareBoost

open Paper2
open CurrentAdditive.ArbitraryPrefix

variable {X Z S : Type*} [Fintype X] [Fintype Z] [Fintype S]

theorem rareboost_from_suffix
    (μ : FiniteLaw X)
    (F : X → Z → Bool) (source : FiniteLaw S)
    {q : ℕ} (decode : S → Fin q → Z)
    (Good : Finset (Fin q)) (Rows : Fin q → Set X) (Y K : Set S)
    (d a : ℕ) (x : ℝ)
    (ha : 1 ≤ a) (hx : 0 < x)
    (hscale : (2 : ℝ)^a * x ≤ 1)
    (hcount : 2^(a-1) + 1 ≤ Good.card)
    (hrow : ∀ i ∈ Good, (2 : ℝ)^a * x ≤ μ.prob (· ∈ Rows i))
    (hY : 0 < source.prob (· ∈ Y)) (hK : K ⊆ Y)
    (hcond : (1/2 : ℝ) ≤ source.prob (· ∈ K) / source.prob (· ∈ Y))
    (hSuffix : ∀ (b : ℕ) (Q : Finset (Fin q)) (R : Fin q → Set X)
        (C : Set S),
      Q ⊆ Good →
      2^b + 1 ≤ Q.card →
      (∀ i ∈ Q, (2 : ℝ)^(b+1) * x ≤ μ.prob (· ∈ R i)) →
      (2 : ℝ)^(b+1) * x ≤ 1 →
      C ⊆ K →
      1 / (2 : ℝ)^(b+1) ≤ source.prob (· ∈ C) / source.prob (· ∈ Y) →
      d+1 ≤ Compression.restrictionD
        (fun a s => F a.2 (decode s a.1)) (rowRectangle Q R) C) :
    d+a ≤ Compression.restrictionD
      (fun a s => F a.2 (decode s a.1))
      (rowRectangle Good Rows) K := by
  let G : (Fin q × X) → S → Bool :=
    fun a s => F a.2 (decode s a.1)
  let D := Compression.restrictionD G (rowRectangle Good Rows) K
  by_contra hn
  change ¬ (d+a ≤ D) at hn
  have hD : D ≤ d+a-1 := by omega
  obtain ⟨A, B, Good', Rows', K', P', hab, hcount', hrow', hcond',
    hGoodsub, hRowssub, hKsub, hKY, hcost, heval⟩ :=
    rare_prefix_state μ source G Good Rows Y K d a x
      ha hx hcount hrow hY hK hcond hD
  have hscale' : (2 : ℝ)^(B+1) * x ≤ 1 := by
    have hp : (2 : ℝ)^(B+1) ≤ (2 : ℝ)^a :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    exact (mul_le_mul_of_nonneg_right hp hx.le).trans hscale
  have hlower := hSuffix B Good' Rows' K' hGoodsub hcount' hrow' hscale'
    hKsub hcond'
  have hupper : Compression.restrictionD G
      (rowRectangle Good' Rows') K' ≤ d :=
    residual_restriction_upper G Good' Rows' K' P' d hcost heval
  change d+1 ≤ Compression.restrictionD G
    (rowRectangle Good' Rows') K' at hlower
  omega

#print axioms rareboost_from_suffix

end V38RareBoost
