import CurrentAdditive.V38Fin2Exact
import Lean.Util.CollectAxioms

/-! Selected v39 main.tex `lem:product-blocks`.
The dyadic parameter is written u=2^a. This is the literal iid
specialization of the already proved original-law eight-wise theorem,
with precisely the selected two-threshold profile. -/

namespace CurrentAdditive.V39ProductBlocks

open Paper2 Paper2.SourceMatrix CurrentAdditive.ArbitraryPrefix

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem full_product_blocks
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (M : X → Y → Bool) {q : ℕ}
    (Good : Finset (Fin q)) (Rows : Fin q → Set X)
    (K : Set (Fin q → Y)) (H a : ℕ) (x : ℝ)
    (ha : 1 ≤ a) (hH : 2 ≤ H) (hx : 0 < x)
    (hscale : (2 : ℝ)^a*x ≤ 1)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile M
      μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (hcount : 2^(a-1)+1 ≤ Good.card)
    (hrow : ∀ i ∈ Good, (2 : ℝ)^a*x ≤ μ.toFiniteLaw.prob (· ∈ Rows i))
    (hK : (9/25 : ℝ) ≤ (ν.iid q).toFiniteLaw.prob (· ∈ K)) :
    H+a ≤ Compression.restrictionD (fullInterlace M q)
      (rowRectangle Good Rows) K := by
  have hwise : IsDWise 8 (ν.iid q).toFiniteLaw
      (fun z : Fin q → Y => z) ν.toFiniteLaw := by
    intro J _hJ E
    rw [PositiveRationalLaw.toFiniteLaw_iid]
    exact FiniteLaw.pi_prob_restrict (fun _ : Fin q => ν.toFiniteLaw)
      (fun j : J => j.val) Subtype.val_injective E
  exact V38Fin2Exact.exactboost μ ν M (ν.iid q).toFiniteLaw
    (fun z : Fin q → Y => z) hwise Good Rows K H a x
    ha hH hx hscale hprofile hcount hrow hK

theorem two_full_product_blocks
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (M : X → Y → Bool) {q : ℕ}
    (Good : Finset (Fin q)) (Rows : Fin q → Set X)
    (K : Set (Fin q → Y)) (H : ℕ) (x : ℝ)
    (hH : 2 ≤ H) (hx : 0 < x) (hscale : 2*x ≤ 1)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile M
      μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (hcount : 2 ≤ Good.card)
    (hrow : ∀ i ∈ Good, 2*x ≤ μ.toFiniteLaw.prob (· ∈ Rows i))
    (hK : (9/25 : ℝ) ≤ (ν.iid q).toFiniteLaw.prob (· ∈ K)) :
    H+1 ≤ Compression.restrictionD (fullInterlace M q)
      (rowRectangle Good Rows) K := by
  apply full_product_blocks μ ν M Good Rows K H 1 x (by omega) hH hx
  · simpa using hscale
  · exact hprofile
  · simpa using hcount
  · simpa using hrow
  · exact hK

#print axioms full_product_blocks
#print axioms two_full_product_blocks

end CurrentAdditive.V39ProductBlocks

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  for (name, _) in env.constants.toList do
    if (`CurrentAdditive.V39ProductBlocks).isPrefixOf name then
      count := count + 1
      for axiomName in (← Lean.collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Forbidden axiom {axiomName} in {name}"
  if count == 0 then throwError "Empty product-block audit"
  logInfo m!"Full-product block specialization audit: {count} declarations; only permitted axioms."
