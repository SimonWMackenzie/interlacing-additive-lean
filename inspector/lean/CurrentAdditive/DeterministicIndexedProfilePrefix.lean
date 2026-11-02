import CurrentAdditive.DeterministicIndexedStreamConditioning
import CurrentAdditive.RestrictionBridge

/-! The arbitrary-protocol prefix theorem on the generated, indexed M₁ and T
matrices. Each hypothesis is an actual short restriction protocol premise, not
an assumed source profile or an opaque certificate. -/

namespace CurrentAdditive.DeterministicIndexedMatrix

open Paper2 Workspace.Types.CommComplexity Workspace.Types.Protocol

variable {X Y : Type*} [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

namespace Sources

/-- What a short protocol for an M₁ rectangle would leave after its prefix.
The evaluation clause names the generated indexed entry function itself. -/
theorem M₁_exact_prefix
    (R₀ : X → Y → Bool) (Q : Finset (Fin q₁))
    (R : Fin q₁ → Set X) (C : Set src.gamma.Label)
    (d a : ℕ) (x : ℝ) (ha : 1 ≤ a) (hx : 0 < x)
    (hQ : 2 ^ (a-1) + 1 ≤ Q.card)
    (hR : ∀ i ∈ Q, (2 : ℝ)^a * x ≤ μX.toFiniteLaw.prob (· ∈ R i))
    (hC : (9/25 : ℝ) ≤ src.gamma.law.toFiniteLaw.prob (· ∈ C))
    (hD : Paper2.Compression.restrictionD (M₁ src R₀)
      (CurrentAdditive.ArbitraryPrefix.rowRectangle Q R) C ≤ d+a-1) :
    ∃ (A B : ℕ) (Q' : Finset (Fin q₁)) (R' : Fin q₁ → Set X)
      (C' : Set src.gamma.Label)
      (P' : Protocol (Fin q₁ × X) src.gamma.Label Bool),
      A + B = a-1 ∧ 2 ^ B + 1 ≤ Q'.card ∧
      (∀ i ∈ Q', (2 : ℝ)^(B+1) * x ≤ μX.toFiniteLaw.prob (· ∈ R' i)) ∧
      (9/25 : ℝ) / ((2 : ℝ)^B) ≤ src.gamma.law.toFiniteLaw.prob (· ∈ C') ∧
      Q' ⊆ Q ∧ (∀ i ∈ Q', R' i ⊆ R i) ∧ C' ⊆ C ∧
      P'.cost ≤ d ∧
      (∀ i ∈ Q', ∀ u ∈ R' i, ∀ γ ∈ C',
        P'.eval (i,u) γ = R₀ u (Paper2.SourceMatrix.head (gammaWord src γ) i)) := by
  simpa [M₁_entry] using
    CurrentAdditive.ArbitraryPrefix.exact_prefix_state
      μX.toFiniteLaw src.gamma.law.toFiniteLaw (M₁ src R₀)
      Q R C d a x ha hx hQ hR hC hD

/-- The same protocol prefix on T, whose row blocks are the actual q₂
positions and whose columns remain distinct inner-source labels. -/
theorem T_exact_prefix
    (R₀ : X → Y → Bool) (Q : Finset (Fin q₂))
    (R : Fin q₂ → Set src.gamma.Label) (C : Set src.inner.Label)
    (d a : ℕ) (x : ℝ) (ha : 1 ≤ a) (hx : 0 < x)
    (hQ : 2 ^ (a-1) + 1 ≤ Q.card)
    (hR : ∀ i ∈ Q, (2 : ℝ)^a * x ≤ src.gamma.law.toFiniteLaw.prob (· ∈ R i))
    (hC : (9/25 : ℝ) ≤ src.inner.law.toFiniteLaw.prob (· ∈ C))
    (hD : Paper2.Compression.restrictionD
      (fun (a : Fin q₂ × src.gamma.Label) (z : src.inner.Label) =>
        T src R₀ z a)
      (CurrentAdditive.ArbitraryPrefix.rowRectangle Q R) C ≤ d+a-1) :
    ∃ (A B : ℕ) (Q' : Finset (Fin q₂))
      (R' : Fin q₂ → Set src.gamma.Label) (C' : Set src.inner.Label)
      (P' : Protocol (Fin q₂ × src.gamma.Label) src.inner.Label Bool),
      A + B = a-1 ∧ 2 ^ B + 1 ≤ Q'.card ∧
      (∀ i ∈ Q', (2 : ℝ)^(B+1) * x ≤
        src.gamma.law.toFiniteLaw.prob (· ∈ R' i)) ∧
      (9/25 : ℝ) / ((2 : ℝ)^B) ≤ src.inner.law.toFiniteLaw.prob (· ∈ C') ∧
      Q' ⊆ Q ∧ (∀ i ∈ Q', R' i ⊆ R i) ∧ C' ⊆ C ∧
      P'.cost ≤ d ∧
      (∀ i ∈ Q', ∀ γ ∈ R' i, ∀ z ∈ C',
        P'.eval (i,γ) z = M₁ src R₀ (src.inner.decode z i) γ) := by
  simpa [T_entry] using
    CurrentAdditive.ArbitraryPrefix.exact_prefix_state
      src.gamma.law.toFiniteLaw src.inner.law.toFiniteLaw
      (fun (a : Fin q₂ × src.gamma.Label) (z : src.inner.Label) =>
        T src R₀ z a)
      Q R C d a x ha hx hQ hR hC hD

end Sources

end CurrentAdditive.DeterministicIndexedMatrix
