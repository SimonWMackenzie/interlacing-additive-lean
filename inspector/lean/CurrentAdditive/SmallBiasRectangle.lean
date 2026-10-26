import CurrentAdditive.SmallBiasPrefix

/-!
# The actual v27 cut rectangle

Source: v27 `sections/07a-small-bias.tex`, equation `yao:cut-rectangle`.
This theorem composes a common early strategy prefix with `i` actual
Bob--Alice branch choices. It measures all column mass under one original
law and preserves exact protocol evaluation on the resulting rectangle.
-/

namespace CurrentAdditive.SmallBias

open Paper2.Yao Workspace.Types.Protocol

variable {Ω Λ : Type*} [Fintype Λ]

/-- The source's cut rectangle, before choosing `k` rows or counting suffix
patterns. The row bound is multiplicative rather than rounded; integrality
may be applied after the cut. -/
theorem actual_cut_rectangle
    (μ : Paper2.FiniteLaw Λ) (t i h : ℕ) (ht : 1 ≤ t)
    (P : Protocol Ω Λ Bool)
    (hc : IsComplete P ((2 * t - 1) + 2 * (i + h)))
    (ha : Alternates .alice P)
    (X : Finset Ω) (Y : Λ → Prop)
    (σ : ResponseStrategy t)
    (hσ : ∀ x ∈ X, earlyStrategy t P x = σ) :
    ∃ (X' : Finset Ω) (Y' : Λ → Prop) (Q : Protocol Ω Λ Bool),
      X' ⊆ X ∧
      (∀ ℓ, Y' ℓ → Y ℓ) ∧
      X.card ≤ 2 ^ i * X'.card ∧
      μ.prob Y ≤ (2 ^ (t - 1 + i) : ℝ) * μ.prob Y' ∧
      IsComplete Q (2 * h) ∧ Alternates .bob Q ∧
      (∀ x ∈ X', ∀ ℓ, Y' ℓ → P.eval x ℓ = Q.eval x ℓ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  have hc' : IsComplete P (2 * k + 1 + 2 * (i + h)) := by
    simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc
  obtain ⟨Y₀, T, hY₀, hmass₀, hc₀, ha₀, heval₀⟩ :=
    common_prefix_retains μ k (i + h) P hc' ha X Y σ hσ
  have hcT : IsComplete T (2 * i + 2 * h) := by
    simpa [Nat.mul_add] using hc₀
  obtain ⟨X', Y', Q, hX', hY', hcard, hmass, hcQ, haQ, heval⟩ :=
    rectangle_after_pairs μ i h T hcT ha₀ X Y₀
  refine ⟨X', Y', Q, hX', (fun ℓ h => hY₀ ℓ (hY' ℓ h)), hcard,
    ?_, hcQ, haQ, ?_⟩
  · calc
      μ.prob Y ≤ (2 ^ k : ℝ) * μ.prob Y₀ := hmass₀
      _ ≤ (2 ^ k : ℝ) * ((2 ^ i : ℝ) * μ.prob Y') :=
        mul_le_mul_of_nonneg_left hmass (by positivity)
      _ = (2 ^ ((k + 1) - 1 + i) : ℝ) * μ.prob Y' := by
        simp [pow_add, mul_assoc]
  · intro x hx ℓ hℓ
    exact (heval₀ x (hX' hx) ℓ (hY' ℓ hℓ)).trans
      (heval x hx ℓ hℓ)

#print axioms CurrentAdditive.SmallBias.actual_cut_rectangle

end CurrentAdditive.SmallBias
