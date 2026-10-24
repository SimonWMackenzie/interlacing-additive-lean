import Paper2.A4Shells
import Paper2.A4Asymptotics

/-!
# Unit 4 (Paper A), segment A4-S10 (T24 part): the growing-gap midpoint shell

Owner lane `owner:a-unit4-shell` (private, 25 September 2026).
Source: lock v12 `06-reduction.tex`, proof of `thm:quantitative` ("Thus for every fixed
`c<1/12` the gap `k` eventually exceeds twice the proposed error. The midpoint test from
\cref{intro:corollary} decides the formula with bounded error.").

Composition of A4-S7 (`gap_exceeds_twice_error`, `_square`) with the law-generic T02 error
shell: beyond an explicit `N₀`, an estimator with additive error `c·log₂T/log₂log₂T` (rectangular
or square printed count `T`) and per-run success `≥ 2/3` makes the median midpoint test at gap
`k = ⌊N/⌈log₂N⌉²⌋` err with probability `≤ 1/100` (YES) and `≤ 2^-11 + 1/100 < 1/3` (NO).

**HYP shell: does not close a ledger row** (T24, T03, D04 stay open). NOT included: the
running-time half `n^{O(k+1)} = 2^{o(N)}`, the machine assembly, the DRAFT D04 contradiction.
-/

namespace Paper2.Unit4Shell.ShellsT24

open Paper2 Paper2.FiniteLaw Paper2.Unit4Shell.Asymptotics Paper2.Unit4Shell.Shells

/-- **T24 midpoint shell (rectangular and square outputs).** Does not close a ledger row. -/
theorem T24_midpoint_shell (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ) (p : ℕ)
    (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12) (square : Bool) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (n m : ℕ) [NeZero n] (edge : Fin m → Bool → Fin n),
      (∀ v, ∃ e b, edge e b = v) → (∀ v, SourceItems.degree edge v ≤ Δ) →
      N ≤ m → 2 * m ≤ Δ * n → n ≤ N * (Nat.clog 2 (N + 2)) ^ p →
      let T : ℕ := if square then printedTsq n m Δ γ (kOf N) else printedT n m Δ γ (kOf N)
      let a : ℝ := c * (Real.logb 2 T / Real.logb 2 (Real.logb 2 T))
      ∀ {α β : Type} [Fintype α] [Fintype β] (ρ : FiniteLaw β) (μ : FiniteLaw α)
        (cost : β → ℕ) (Bud : ℕ) (est : β → α → ℝ),
        (∀ b, 2 / 3 ≤ μ.prob (fun t => |est b t - cost b| ≤ a)) →
        ((∀ b, cost b ≤ Bud) →
          (ρ.prod (μ.iid Amplification.reps)).prob
            (fun x => ¬ accepts est Bud (kOf N) x) ≤ 1 / 100) ∧
        (ρ.prob (fun b => ¬ cost b = Bud + kOf N) ≤ (1 / 2) ^ 11 →
          (ρ.prod (μ.iid Amplification.reps)).prob
            (fun x => accepts est Bud (kOf N) x) ≤ (1 / 2) ^ 11 + 1 / 100 ∧
          (1 / 2 : ℝ) ^ 11 + 1 / 100 < 1 / 3) := by
  cases square
  · obtain ⟨N₀, hN₀⟩ := gap_exceeds_twice_error Δ γ hγ hΔ p c hc0 hc
    refine ⟨N₀, ?_⟩
    intro N hN n m _ edge hinc hdeg hNm hmn hsize T a α β _ _ ρ μ cost Bud est hμ
    have hgap := hN₀ N hN n m edge hinc hdeg hNm hmn hsize
    have hk : 2 * a < (kOf N : ℝ) := by
      simp only [a, T, Bool.false_eq_true, ↓reduceIte]
      linarith [hgap]
    exact T02_error_shell ρ μ cost Bud (kOf N) a hk est hμ
  · obtain ⟨N₀, hN₀⟩ := gap_exceeds_twice_error_square Δ γ hγ hΔ p c hc0 hc
    refine ⟨N₀, ?_⟩
    intro N hN n m _ edge hinc hdeg hNm hmn hsize T a α β _ _ ρ μ cost Bud est hμ
    have hgap := hN₀ N hN n m edge hinc hdeg hNm hmn hsize
    have hk : 2 * a < (kOf N : ℝ) := by
      simp only [a, T, ↓reduceIte]
      linarith [hgap]
    exact T02_error_shell ρ μ cost Bud (kOf N) a hk est hμ

end Paper2.Unit4Shell.ShellsT24
