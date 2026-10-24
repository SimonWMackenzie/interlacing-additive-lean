import EthInapproximability.CurrentPaper.ExactCoordinateControl
import EthInapproximability.CurrentPaper.ExactResidualIndexing

/-!
# Real-density restriction profiles of the sampled coordinate matrix

Source: locked v8 `E-exact-details.tex`, robustness conclusion in
`lem:exact-coordinate-restrictions`.  Arbitrary retained row sets in `Q`
supply enough coordinate blocks by counting.  Transposing gives the two
one-copy profiles of the literal `Qᵀ`, at the original real row density.

The inputs are the two proved profiles and the early-leaf nonconstancy bound
for `Pbarᵀ`, balancedness of the actual indexed second family, and displayed
scalar stopping/counting gates. No lower bound for `Q` is a hypothesis.
-/

namespace EthInapproximability.CurrentPaper.ExactSecondProfiles

open NPCC Workspace.Types.CommComplexity Workspace.Types.Interlace
open ExactConstruction ExactCoordinateControl ExactResidualIndexing

/-- The literal transpose of the sampled coordinate matrix. -/
def secondTranspose {a d N₁ N₂ : ℕ} (ha : 2 ≤ a)
    (C₁ : FirstFamily a N₁) (C₂ : SecondFamily a d N₂) :
    Fin N₂ → (Fin d × Fin N₁) → Bool :=
  fun z r => secondMatrix ha C₁ C₂ r z

/-- Alice announces the coordinate, then the indexing protocol runs there.
This is the literal selector upper bound, including the final answer bit. -/
theorem secondMatrix_upper {a d k N₁ N₂ : ℕ} (ha : 2 ≤ a)
    (C₁ : FirstFamily a N₁) (C₂ : SecondFamily a d N₂) (hwidth : d = 2 ^ k) :
    D (secondMatrix ha C₁ C₂) ≤ a + 1 + k := by
  subst d
  have hupper : D (secondMatrix ha C₁ C₂) ≤ k + (a + 1) := by
    apply comp_le_partition _ k (a + 1) Prod.fst
    intro α
    rw [← comp_transpose]
    apply comp_le_of_row_types_succ _ a (fun z => C₂ z α)
    intro z z' heq
    funext r
    simp only [secondMatrix, r.property]
    rw [heq]
  omega

section Profiles

variable {a d N₁ N₂ H m R : ℕ} {x h ε yzero : ℝ}
    (ha : 2 ≤ a) (hN₁ : 0 < N₁)
    (C₁ : FirstFamily a N₁) (C₂ : SecondFamily a d N₂)
    (hwidth : d = 2 ^ R * 2 ^ m)
    (hH : 2 ≤ H) (hm : 2 ^ 20 ≤ m) (hx : 0 < x)
    (hrow : (2 : ℝ) ^ m * x ≤ 1) (hε : 0 ≤ ε) (hh : 0 < h)
    (h1 : H ≤ Dfamily
      (interlaceFun (fun ℓ i => duplicatedFirstMatrix ha C₁ i ℓ) 1)
      (bracketGE (Fin N₁) (Fin (width a)) 1 x (3 / 5)))
    (h2 : H - 1 ≤ Dfamily
      (interlaceFun (fun ℓ i => duplicatedFirstMatrix ha C₁ i ℓ) 1)
      (bracketGE (Fin N₁) (Fin (width a)) 1 x (3 / 10)))
    (hone : 1 ≤ Dfamily
      (interlaceFun (fun ℓ i => duplicatedFirstMatrix ha C₁ i ℓ) 1)
      (bracketGE (Fin N₁) (Fin (width a)) 1 x yzero))
    (hS : IsBalancedFamily (2 ^ m) C₂ ε)
    (hgateOne : yzero ≤ yLoss ε (2 ^ m) h (H + (R + m)))
    (hgateSeed : HardSeed.columnDensity ((2 : ℝ) ^ m) ≤
      h * (2 : ℝ) ^ (-((H + m : ℕ) : ℝ)) / (1 + ε))

include hN₁ hwidth hH hm hx hrow hε hh h1 h2 hone hS hgateOne hgateSeed

/-- A restriction of `Qᵀ` at row density `h` and column density `β`
has the certified cost at any allowed residual width. The good-block count
and its denominator condition are explicit scalar gates. -/
theorem transpose_subgame_lower {β : ℝ}
    (R' : ℕ) (hR' : R' ≤ R)
    (hsmall : (2 : ℝ) ^ (R' + m) * x < 1)
    (hcount : 2 ^ R' * HardSeed.copyCount m ≤
      ⌈(d : ℝ) * (β - (2 : ℝ) ^ (R' + m) * x) /
        (1 - (2 : ℝ) ^ (R' + m) * x)⌉₊)
    (J : Finset (Fin N₂)) (I : Finset (Fin d × Fin N₁))
    (hJ : (N₂ : ℝ) * h ≤ J.card)
    (hI : ((d : ℝ) * N₁) * β ≤ I.card) :
    H + (R' + m) ≤ D (subgame (secondTranspose ha C₁ C₂) J I) := by
  classical
  letI : Nonempty (Fin N₁) := ⟨⟨0, hN₁⟩⟩
  have hd : 0 < d := by rw [hwidth]; positivity
  have hv : 1 ≤ 2 ^ R' * HardSeed.copyCount m := by
    have hp := (HardSeed.copyCount_bounds (show 5 ≤ m by omega)).1
    have hpos : 0 < HardSeed.copyCount m := by omega
    exact Nat.succ_le_iff.mpr (Nat.mul_pos (by positivity) hpos)
  have hblock := exact_coordinateBlockLowerBound (z := h) ha hN₁ C₁ C₂ hwidth hH hm hx
    hrow hε hh h1 h2 hone hS hgateOne hgateSeed
    0 R' (2 ^ R' * HardSeed.copyCount m)
    ⌈(2 : ℝ) ^ (R' + m) * x * (N₁ : ℝ)⌉₊
    (by omega) hR' (le_refl _) (le_refl _) (by simp)
  have hbound := lowerBound_of_denseRows (secondMatrix ha C₁ C₂) Finset.univ
    hd (by positivity : 0 < (2 : ℝ) ^ (R' + m) * x) hsmall hv
    (by simp only [Fintype.card_fin]; ring_nf; exact le_refl _) hcount hblock
    I J (by simpa only [Fintype.card_fin, mul_comm, mul_left_comm, mul_assoc] using hI)
    (Finset.subset_univ _) (by simpa [mul_comm] using hJ)
  have htranspose : D (subgame (secondTranspose ha C₁ C₂) J I) =
      D (subgame (secondMatrix ha C₁ C₂) I J) :=
    comp_transpose (subgame (secondMatrix ha C₁ C₂) I J)
  rw [htranspose]
  exact hbound

/-- The same literal restriction estimate in the one-copy family interface
used by the two-bound amplifier and the real-density bin theorem. -/
theorem transpose_oneCopy_lower {β : ℝ} (hN₂ : 0 < N₂)
    (hh1 : h ≤ 1) (hβ1 : β ≤ 1)
    (R' : ℕ) (hR' : R' ≤ R)
    (hsmall : (2 : ℝ) ^ (R' + m) * x < 1)
    (hcount : 2 ^ R' * HardSeed.copyCount m ≤
      ⌈(d : ℝ) * (β - (2 : ℝ) ^ (R' + m) * x) /
        (1 - (2 : ℝ) ^ (R' + m) * x)⌉₊) :
    H + (R' + m) ≤ Dfamily (interlaceFun (secondTranspose ha C₁ C₂) 1)
      (bracketGE (Fin N₂) (Fin d × Fin N₁) 1 h β) := by
  letI : Nonempty (Fin N₂) := ⟨⟨0, hN₂⟩⟩
  apply oneCopy_family_lower_of_subgame (secondTranspose ha C₁ C₂) hh1 hβ1
  intro J I hJ hI
  exact transpose_subgame_lower ha hN₁ C₁ C₂ hwidth hH hm hx hrow hε hh
    h1 h2 hone hS hgateOne hgateSeed R' hR' hsmall hcount J I
    (by simpa only [Fintype.card_fin] using hJ)
    (by simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] using hI)

/-- The two required profiles of `Qᵀ` at the same real row density `h`.
The second cost is the predecessor of the first. In the paper the level is
`H = a+1`, while `R+m = log₂ d` and `h = (log₂ d)⁻³`. -/
theorem transpose_profiles (hN₂ : 0 < N₂) (hR : 1 ≤ R) (hh1 : h ≤ 1)
    (hsmall : (2 : ℝ) ^ (R + m) * x < 1)
    (hfull : 2 ^ R * HardSeed.copyCount m ≤
      ⌈(d : ℝ) * ((3 / 5 : ℝ) - (2 : ℝ) ^ (R + m) * x) /
        (1 - (2 : ℝ) ^ (R + m) * x)⌉₊)
    (hhalf : 2 ^ (R - 1) * HardSeed.copyCount m ≤
      ⌈(d : ℝ) * ((3 / 10 : ℝ) - (2 : ℝ) ^ (R - 1 + m) * x) /
        (1 - (2 : ℝ) ^ (R - 1 + m) * x)⌉₊) :
    H + (R + m) ≤ Dfamily (interlaceFun (secondTranspose ha C₁ C₂) 1)
      (bracketGE (Fin N₂) (Fin d × Fin N₁) 1 h (3 / 5)) ∧
    H + (R + m) - 1 ≤ Dfamily (interlaceFun (secondTranspose ha C₁ C₂) 1)
      (bracketGE (Fin N₂) (Fin d × Fin N₁) 1 h (3 / 10)) := by
  have hsmallHalf : (2 : ℝ) ^ (R - 1 + m) * x < 1 :=
    (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)) hx.le).trans_lt hsmall
  constructor
  · exact transpose_oneCopy_lower ha hN₁ C₁ C₂ hwidth hH hm hx hrow hε hh
      h1 h2 hone hS hgateOne hgateSeed hN₂ hh1 (by norm_num)
      R (le_refl _) hsmall hfull
  · have hh := transpose_oneCopy_lower ha hN₁ C₁ C₂ hwidth hH hm hx hrow hε hh
      h1 h2 hone hS hgateOne hgateSeed hN₂ hh1 (by norm_num : (3 / 10 : ℝ) ≤ 1)
      (R - 1) (Nat.sub_le R 1) hsmallHalf hhalf
    have heq : H + (R - 1 + m) = H + (R + m) - 1 := by omega
    rwa [heq] at hh

/-- The same construction has the exact selector cost once its certified
base level is the indexing level `a+1`.  This uses the full-width profile
and the explicit selector protocol above, on the very same matrix. -/
theorem secondMatrix_cost (hHlevel : H = a + 1) (hh1 : h ≤ 1)
    (hsmall : (2 : ℝ) ^ (R + m) * x < 1)
    (hfull : 2 ^ R * HardSeed.copyCount m ≤
      ⌈(d : ℝ) * ((3 / 5 : ℝ) - (2 : ℝ) ^ (R + m) * x) /
        (1 - (2 : ℝ) ^ (R + m) * x)⌉₊) :
    D (secondMatrix ha C₁ C₂) = a + 1 + (R + m) ∧
      D (secondTranspose ha C₁ C₂) = a + 1 + (R + m) := by
  classical
  have hsub := transpose_subgame_lower ha hN₁ C₁ C₂ hwidth hH hm hx hrow hε hh
    h1 h2 hone hS hgateOne hgateSeed R (le_refl _) hsmall hfull
    Finset.univ Finset.univ
    (by simpa only [Finset.card_univ, Fintype.card_fin] using
      mul_le_of_le_one_right (Nat.cast_nonneg N₂) hh1)
    (by
      simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
      nlinarith [mul_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
        (Nat.cast_nonneg N₁ : (0 : ℝ) ≤ N₁)])
  have hlower := hsub.trans (D_mapNodes_le (secondTranspose ha C₁ C₂)
    (fun z : ↥(Finset.univ : Finset (Fin N₂)) => z.val)
    (fun r : ↥(Finset.univ : Finset (Fin d × Fin N₁)) => r.val))
  rw [hHlevel] at hlower
  have htranspose : D (secondTranspose ha C₁ C₂) = D (secondMatrix ha C₁ C₂) :=
    comp_transpose (secondMatrix ha C₁ C₂)
  rw [htranspose] at hlower
  have hupper := secondMatrix_upper ha C₁ C₂ (show d = 2 ^ (R + m) by
    simpa only [pow_add] using hwidth)
  exact ⟨le_antisymm hupper hlower, htranspose.trans (le_antisymm hupper hlower)⟩

end Profiles

end EthInapproximability.CurrentPaper.ExactSecondProfiles
