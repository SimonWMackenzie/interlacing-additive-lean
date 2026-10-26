import CurrentAdditive.FourWiseMoment

namespace CurrentAdditive.FourthMoment

open Paper2
open scoped BigOperators

/-- Appendix H's exact eight-coordinate pair-tail consequence, expressed
after the independent bridge has supplied four-wise laws for the pair tests.
The carrier of the actual source remains indexed. -/
theorem exact_pair_tail_of_four_wise
    {Ω : Type*} [Fintype Ω] {m : ℕ}
    (ρ : FiniteLaw Ω) (Z : Fin m → Ω → Bool)
    (μ : Fin m → FiniteLaw Bool) (K : Ω → Prop)
    (hm : 8 ≤ m)
    (hsmall : ∀ i, (μ i).prob (fun b => b = true) < 9/25)
    (hK : ∀ ω, K ω → ∀ i, Z i ω = true)
    (hjoint : ∀ (s : Finset (Fin m)), s.card ≤ 4 →
      ∀ E : (s → Bool) → Prop,
        ρ.prob (fun ω => E (fun j : s => Z j.val ω)) =
          (FiniteLaw.pi (fun j : s => μ j.val)).prob E) :
    ρ.prob K ≤
        ((m : ℝ)/4 + 3*(m : ℝ)^2/16) /
          ((16/25 : ℝ)^4 * (m : ℝ)^4) ∧
      ρ.prob K < 9/(50*(m : ℝ)) := by
  classical
  let S (ω : Ω) := ∑ i : Fin m, boolCentered μ i (Z i ω)
  let a : ℝ := (16/25 : ℝ) * m
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have ha : 0 < a := mul_pos (by norm_num) hmR
  have hsource : ∀ ω, K ω → a ≤ S ω := by
    intro ω hω
    have hpoints : ∀ i : Fin m, (16/25 : ℝ) ≤ boolCentered μ i (Z i ω) := by
      intro i
      have hz := hK ω hω i
      have hp := hsmall i
      simp only [boolCentered, hz, ↓reduceIte]
      linarith
    calc
      a = ∑ _i : Fin m, (16/25 : ℝ) := by simp [a, mul_comm]
      _ ≤ ∑ i : Fin m, boolCentered μ i (Z i ω) :=
        Finset.sum_le_sum (fun i _ => hpoints i)
  have hmoment : expect ρ (fun ω => (S ω)^4) ≤
      (m : ℝ)/4 + 3*(m : ℝ)^2/16 := by
    simpa only [S, Fintype.card_fin] using
      fourth_bound_of_four_wise ρ Z μ hjoint
  have hmarkov := event_le_fourth_moment ρ S K a ha hsource
  have hden : (0 : ℝ) < (16/25 : ℝ)^4 * (m : ℝ)^4 := by positivity
  have ha4 : a^4 = (16/25 : ℝ)^4 * (m : ℝ)^4 := by simp [a, mul_pow]
  rw [ha4] at hmarkov
  have hbound : ρ.prob K ≤
      ((m : ℝ)/4 + 3*(m : ℝ)^2/16) /
        ((16/25 : ℝ)^4 * (m : ℝ)^4) := by
    apply (le_div_iff₀ hden).2
    simpa only [mul_comm] using hmarkov.trans hmoment
  exact ⟨hbound, hbound.trans_lt (exact_pair_numeric m (by exact_mod_cast hm))⟩

#print axioms exact_pair_tail_of_four_wise

end CurrentAdditive.FourthMoment
