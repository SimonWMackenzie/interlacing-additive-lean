import CurrentAdditive.V38TwoHigh
import CurrentAdditive.DeterministicSuffixSmall

/-!
Transfer the v38 two-threshold full-product two-block lower bound to actual
retained labels of an arbitrary indexed tuple source. The representatives
used for this transfer need not preserve label weights.
-/

namespace V38RareBoost

open Paper2

variable {X Z S : Type*} [Fintype X] [Fintype Z] [Fintype S]

theorem indexed_two_block_high
    (μ : FiniteLaw X) (ν : FiniteLaw Z)
    (F : X → Z → Bool) {q : ℕ} (decode : S → Fin q → Z)
    (e : Fin 2 → Fin q) (R : Set (Fin q × X)) (K : Set S)
    (d : ℕ) (x : ℝ) (hd : 2 ≤ d) (hx : 0 < x)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile F μ ν x (d : ℤ))
    (hrow : ∀ j : Fin 2, 2 * x ≤ μ.prob
      (fun a => (e j, a) ∈ R))
    (hmass : (9 / 25 : ℝ) ≤ (ν.iid 2).prob
      (fun c => ∃ s ∈ K, (fun j => decode s (e j)) = c)) :
    d + 1 ≤ Compression.restrictionD
      (fun a s => F a.2 (decode s a.1)) R K := by
  let U : Set (Fin 2 × X) := {a | (e a.1, a.2) ∈ R}
  let V : Set (Fin 2 → Z) := (fun s j => decode s (e j)) '' K
  have hr : ∀ j : Fin 2, 2 * x ≤ μ.prob (fun a => (j,a) ∈ U) := by
    intro j
    simpa only [U, Set.mem_setOf_eq] using hrow j
  have hc : (9 / 25 : ℝ) ≤ (ν.iid 2).prob (· ∈ V) := by
    simpa only [V, Set.mem_image] using hmass
  have hfull := Paper2.V38SmallBlocks.two_block_high
    F μ ν x d hd hx hprofile U V hr hc
  exact hfull.trans
    (CurrentAdditive.SuffixSmall.selected_projection_cost_le_indexed
      F decode e R K)

#print axioms indexed_two_block_high

end V38RareBoost
