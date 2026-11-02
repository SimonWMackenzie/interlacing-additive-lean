import Mathlib

/-!
# Parameterized NP route: weighted-frontier transcription pilot

This file isolates the numerical argument in `lem:dense-weighted-frontier`
from Section 8 of the active autoformalization source.  The protocol-routing
layer need only establish the explicit conservation/capacity hypotheses below.
-/

namespace EthInapproximability.ParameterizedNP

open scoped BigOperators

/-- **Generic weighted-frontier inequality.** Let `alice` be the frontier
nodes that stop at an Alice query.  At every other frontier node the routed
weight fits in its capacity.  If the total deficit is at most `b`, the total
signed excess is at least `w - 2*b`, and `w > b/(1-θ)`, then an Alice node
has both template mass at least `θ` times capacity and strictly positive
signed excess.

This is the abstract real-valued core of
`routes/parameterized-np/autoformalization/sections/08-dense-stage4.tex`,
lines carrying `eq:frontier-conservation` through
`lem:dense-weighted-frontier`.  The manuscript uses `θ = 3/4`.
-/
theorem weightedFrontier
    {ι : Type*} [Fintype ι]
    (alice : Set ι) (κ h z : ι → ℝ) (θ b w : ℝ)
    (hθhalf : 1 / 2 < θ) (hθone : θ < 1)
    (hκ : ∀ v, 0 ≤ κ v) (hz : ∀ v, 0 ≤ z v)
    (hz_le_h : ∀ v, z v ≤ h v)
    (hisolation : ∀ v, v ∉ alice → h v + z v ≤ κ v)
    (hdeficit : ∑ v, (κ v - h v) ≤ b)
    (hexcess : w - 2 * b ≤ ∑ v, (h v + z v - κ v))
    (hweight : b / (1 - θ) < w) :
    ∃ v ∈ alice, θ * κ v ≤ h v ∧ 0 < h v + z v - κ v := by
  classical
  by_contra hnone
  have hnoWitness :
      ∀ v, v ∈ alice →
        ¬ (θ * κ v ≤ h v ∧ 0 < h v + z v - κ v) := by
    intro v hv hboth
    exact hnone ⟨v, hv, hboth⟩
  -- Positive bonus weight rules out template mass above capacity.
  have hh_le_capacity : ∀ v, h v ≤ κ v := by
    intro v
    by_cases hv : v ∈ alice
    · by_contra hnot
      have hhgt : κ v < h v := lt_of_not_ge hnot
      have hhigh : θ * κ v ≤ h v := by
        have : θ * κ v ≤ κ v := by nlinarith [hκ v]
        exact this.trans hhgt.le
      have hpositive : 0 < h v + z v - κ v := by nlinarith [hz v]
      exact hnoWitness v hv ⟨hhigh, hpositive⟩
    · nlinarith [hisolation v hv, hz v]
  -- Split off exactly the Alice nodes below the target template density.
  let low : Finset ι :=
    Finset.univ.filter (fun v => v ∈ alice ∧ h v < θ * κ v)
  let excess : ι → ℝ := fun v => h v + z v - κ v
  let deficit : ι → ℝ := fun v => κ v - h v
  let ratio : ℝ := (2 * θ - 1) / (1 - θ)
  -- The ratio is nonnegative because `1/2 < θ < 1`.
  have hden : 0 < 1 - θ := by linarith
  have hratio_nonneg : 0 ≤ ratio := by
    dsimp [ratio]
    exact div_nonneg (by linarith) hden.le
  have hdeficit_nonneg : ∀ v, 0 ≤ deficit v := by
    intro v
    dsimp [deficit]
    linarith [hh_le_capacity v]
  -- Outside `low`, the negated witness or isolation capacity kills excess.
  have houtside_nonpos : ∀ v, v ∉ low → excess v ≤ 0 := by
    intro v hvlow
    by_cases hva : v ∈ alice
    · have hhigh : θ * κ v ≤ h v := by
        have : ¬ h v < θ * κ v := by
          intro hlt
          exact hvlow (by simp [low, hva, hlt])
        exact le_of_not_gt this
      have hnpos : ¬ 0 < excess v := by
        intro hpos
        exact hnoWitness v hva ⟨hhigh, by simpa [excess] using hpos⟩
      exact le_of_not_gt hnpos
    · simpa [excess] using hisolation v hva
  -- Each low-node excess is paid for by its capacity deficit.
  have hlow_bound : ∀ v ∈ low, excess v ≤ ratio * deficit v := by
    intro v hv
    have hvdata := Finset.mem_filter.mp hv
    have htemplate : h v < θ * κ v := hvdata.2.2
    have hexcess_le : excess v ≤ 2 * h v - κ v := by
      dsimp [excess]
      linarith [hz_le_h v]
    have hstrict : 2 * h v - κ v < ratio * deficit v := by
      dsimp [ratio, deficit]
      rw [div_mul_eq_mul_div]
      rw [lt_div_iff₀ hden]
      nlinarith
    exact hexcess_le.trans hstrict.le
  -- Non-low contributions are nonpositive, so discard them.
  have htotal_to_low :
      (∑ v, excess v) ≤ (∑ v ∈ low, excess v) := by
    have hterm : ∀ v ∈ (Finset.univ : Finset ι),
        excess v ≤ if v ∈ low then excess v else 0 := by
      intro v _
      by_cases hv : v ∈ low
      · simp [hv]
      · simpa [hv] using houtside_nonpos v hv
    have hsum := Finset.sum_le_sum hterm
    simpa [Finset.sum_ite_irrel] using hsum
  -- Sum the pointwise deficit payments.
  have hlow_to_deficit :
      (∑ v ∈ low, excess v) ≤ ratio * (∑ v ∈ low, deficit v) := by
    calc
      (∑ v ∈ low, excess v) ≤ (∑ v ∈ low, ratio * deficit v) :=
        Finset.sum_le_sum hlow_bound
      _ = ratio * (∑ v ∈ low, deficit v) := by rw [Finset.mul_sum]
  -- All deficits are nonnegative, so restriction to `low` can only decrease.
  have hsubset : low ⊆ (Finset.univ : Finset ι) := by simp
  have hlow_deficit_le :
      (∑ v ∈ low, deficit v) ≤ (∑ v, deficit v) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun v _ _ => hdeficit_nonneg v)
  -- Combine the local accounting with the global deficit bound.
  have htotal_upper : (∑ v, excess v) ≤ ratio * b := by
    calc
      (∑ v, excess v) ≤ (∑ v ∈ low, excess v) := htotal_to_low
      _ ≤ ratio * (∑ v ∈ low, deficit v) := hlow_to_deficit
      _ ≤ ratio * (∑ v, deficit v) :=
        mul_le_mul_of_nonneg_left hlow_deficit_le hratio_nonneg
      _ ≤ ratio * b := mul_le_mul_of_nonneg_left hdeficit hratio_nonneg
  -- The excess lower bound now contradicts `w > b/(1-θ)`.
  have hwupper : w ≤ b / (1 - θ) := by
    have : w - 2 * b ≤ ratio * b := by
      exact hexcess.trans htotal_upper
    dsimp [ratio] at this
    field_simp [ne_of_gt hden] at this ⊢
    nlinarith
  exact (not_le_of_gt hweight) hwupper

/-- The exact `θ = 3/4` numerical form used by
`lem:dense-weighted-frontier`: the route's hypothesis `w > 4*b` forces an
Alice frontier node with at least three quarters of its capacity and positive
excess. -/
theorem weightedFrontier_threeQuarters
    {ι : Type*} [Fintype ι]
    (alice : Set ι) (κ h z : ι → ℝ) (b w : ℝ)
    (hκ : ∀ v, 0 ≤ κ v) (hz : ∀ v, 0 ≤ z v)
    (hz_le_h : ∀ v, z v ≤ h v)
    (hisolation : ∀ v, v ∉ alice → h v + z v ≤ κ v)
    (hdeficit : ∑ v, (κ v - h v) ≤ b)
    (hexcess : w - 2 * b ≤ ∑ v, (h v + z v - κ v))
    (hweight : 4 * b < w) :
    ∃ v ∈ alice, (3 / 4 : ℝ) * κ v ≤ h v ∧
      0 < h v + z v - κ v := by
  apply weightedFrontier alice κ h z (3 / 4 : ℝ) b w
    (by norm_num) (by norm_num) hκ hz hz_le_h hisolation hdeficit hexcess
  calc
    b / (1 - (3 / 4 : ℝ)) = 4 * b := by ring
    _ < w := hweight

end EthInapproximability.ParameterizedNP
