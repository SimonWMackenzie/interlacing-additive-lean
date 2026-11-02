import EthInapproximability.CurrentPaper.ExactResidualIndexing

/-!
# Restriction profiles of the duplicated first indexing matrix

Source: locked v8 `E-exact-details.tex`, `lem:exact-residual-indexing`.
The two extra row labels cost at most two distinct coordinates. Transposing
an actual restriction then supplies the one-copy bounds needed by the
coordinate matrix. The inputs below are sampler balancedness and scalar
rank/stopping/size gates; no restriction-complexity bound is assumed.
-/

namespace EthInapproximability.CurrentPaper.ExactFirstProfiles

open NPCC Workspace.Types.CommComplexity Workspace.Types.Interlace
open ExactConstruction ExactResidualIndexing

/-- The literal transpose of the duplicated first matrix. -/
def firstTranspose {a N : ℕ} (ha : 2 ≤ a) (C₁ : FirstFamily a N) :
    Fin N → Fin (width a) → Bool :=
  fun j i => duplicatedFirstMatrix ha C₁ i j

/-- The manuscript's `w >= 128` absorbs both duplicate labels at both
profile densities when the stopping width is exactly `9t/16`. -/
theorem profile_row_gates {w R t p : ℕ} (hw : 128 ≤ w) (hR : 1 ≤ R)
    (hwidth : w = 2 ^ R * t) (hp : 16 * p = 9 * t) :
    ((2 ^ R * p + 2 : ℕ) : ℝ) ≤ (3 / 5 : ℝ) * (w : ℝ) ∧
    ((2 ^ (R - 1) * p + 2 : ℕ) : ℝ) ≤ (3 / 10 : ℝ) * (w : ℝ) := by
  have hfull : 16 * (2 ^ R * p) = 9 * w := by
    have heq := congrArg (fun n : ℕ => 2 ^ R * n) hp
    rw [hwidth]
    nlinarith [heq]
  have hpow : 2 ^ (R - 1) * 2 = (2 : ℕ) ^ R := by
    rw [← pow_succ, Nat.sub_add_cancel hR]
  have hhalf : 32 * (2 ^ (R - 1) * p) = 9 * w := by
    calc
      32 * (2 ^ (R - 1) * p) = 16 * ((2 ^ (R - 1) * 2) * p) := by ring
      _ = 9 * w := by rw [hpow]; exact hfull
  have hfullReal : (16 : ℝ) * ((2 ^ R * p : ℕ) : ℝ) = 9 * (w : ℝ) := by
    exact_mod_cast hfull
  have hhalfReal : (32 : ℝ) * ((2 ^ (R - 1) * p : ℕ) : ℝ) = 9 * (w : ℝ) := by
    exact_mod_cast hhalf
  have hwReal : (128 : ℝ) ≤ w := by exact_mod_cast hw
  push_cast
  constructor <;> push_cast at hfullReal hhalfReal <;> nlinarith

/-- A plain transposed restriction preserves the original sampler labels.
Its row-label loss is charged before invoking the residual-indexing theorem. -/
theorem transpose_subgame_lower {a t R m p N : ℕ} {x y h z ε ρ β : ℝ}
    (ha : 2 ≤ a) (C₁ : FirstFamily a N) (hwidth : width a = 2 ^ R * t)
    (hS : IsBalancedFamily t C₁ ε) (ht : 0 < t) (hm : 1 ≤ m)
    (hx : 0 < x) (hx1 : x ≤ 1) (hy : 1/2 < y) (hy1 : y ≤ 1)
    (hh : 0 < h) (hε : 0 ≤ ε) (hz1 : z ≤ 1)
    (hp1 : t ≤ 2 * p) (hp2 : p ≤ t)
    (hgateRank : 2 ^ (2 ^ (m - 1)) < ⌈(2 : ℝ) ^ p * z⌉₊)
    (hgateOne : y ≤ yLoss ε t h (R + (m + 1)))
    (hgateSeed : z ≤ h * (2 : ℝ) ^ (-((m + 1 : ℕ) : ℝ)) / (1 + ε))
    (R' : ℕ) (hR' : R' ≤ R) (hrow : (2 : ℝ) ^ R' * x ≤ 1)
    (hρ : h ≤ ρ) (hβ : ((2 ^ R' * p + 2 : ℕ) : ℝ) ≤ β * (width a : ℝ))
    (J : Finset (Fin N)) (I : Finset (Fin (width a)))
    (hJ : (N : ℝ) * ρ ≤ J.card) (hI : (width a : ℝ) * β ≤ I.card) :
    m + 1 + R' ≤ D (subgame (firstTranspose ha C₁) J I) := by
  classical
  have hIlarge : 2 ^ R' * p + 2 ≤ I.card := by
    have hreal : ((2 ^ R' * p + 2 : ℕ) : ℝ) ≤ (I.card : ℝ) :=
      hβ.trans (by simpa [mul_comm] using hI)
    exact_mod_cast hreal
  have hdistinct : 2 ^ R' * p ≤ (I.image (duplicateLabel a ha)).card := by
    have hloss := duplicate_image_card_loss a ha I
    omega
  have hlabels : h * (N : ℝ) ≤ J.card := by
    exact (mul_le_mul_of_nonneg_right hρ (Nat.cast_nonneg N)).trans
      (by simpa [mul_comm] using hJ)
  have hlower := firstMatrix_residual ha C₁ hwidth hS ht hm hx hx1 hy hy1
    hh hε hz1 hp1 hp2 hgateRank hgateOne hgateSeed R' hR'
    (I.image (duplicateLabel a ha)) J hdistinct hrow hlabels
  rw [← D_duplicate_subgame ha C₁ I J] at hlower
  have htranspose : D (subgame (firstTranspose ha C₁) J I) =
      D (subgame (duplicatedFirstMatrix ha C₁) I J) := by
    exact comp_transpose (subgame (duplicatedFirstMatrix ha C₁) I J)
  rw [htranspose]
  exact hlower

/-- One-copy profile for the actual transpose. Its only quantitative inputs
are the displayed residual-indexing and retained-density gates. -/
theorem transpose_oneCopy_lower {a t R m p N : ℕ} {x y h z ε ρ β : ℝ}
    (ha : 2 ≤ a) (C₁ : FirstFamily a N) (hN : 0 < N)
    (hwidth : width a = 2 ^ R * t)
    (hS : IsBalancedFamily t C₁ ε) (ht : 0 < t) (hm : 1 ≤ m)
    (hx : 0 < x) (hx1 : x ≤ 1) (hy : 1/2 < y) (hy1 : y ≤ 1)
    (hh : 0 < h) (hε : 0 ≤ ε) (hz1 : z ≤ 1)
    (hp1 : t ≤ 2 * p) (hp2 : p ≤ t)
    (hgateRank : 2 ^ (2 ^ (m - 1)) < ⌈(2 : ℝ) ^ p * z⌉₊)
    (hgateOne : y ≤ yLoss ε t h (R + (m + 1)))
    (hgateSeed : z ≤ h * (2 : ℝ) ^ (-((m + 1 : ℕ) : ℝ)) / (1 + ε))
    (R' : ℕ) (hR' : R' ≤ R) (hrow : (2 : ℝ) ^ R' * x ≤ 1)
    (hρ : h ≤ ρ) (hρ1 : ρ ≤ 1) (hβ1 : β ≤ 1)
    (hβ : ((2 ^ R' * p + 2 : ℕ) : ℝ) ≤ β * (width a : ℝ)) :
    m + 1 + R' ≤ Dfamily (interlaceFun (firstTranspose ha C₁) 1)
      (bracketGE (Fin N) (Fin (width a)) 1 ρ β) := by
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  apply oneCopy_family_lower_of_subgame (firstTranspose ha C₁) hρ1 hβ1
  intro J I hJ hI
  exact transpose_subgame_lower ha C₁ hwidth hS ht hm hx hx1 hy hy1
    hh hε hz1 hp1 hp2 hgateRank hgateOne hgateSeed R' hR' hrow hρ hβ
    J I (by simpa using hJ) (by simpa using hI)

/-- Both manuscript profiles and the exact full cost, derived together for
the same duplicated first matrix. The two numerical row gates explicitly
pay for the lost duplicate labels at the full and half residual widths. -/
theorem transpose_profiles {a t R m p N : ℕ} {x y h z ε ρ : ℝ}
    (ha : 2 ≤ a) (C₁ : FirstFamily a N) (hN : 0 < N)
    (haeq : a = m + R) (hR : 1 ≤ R) (hwidth : width a = 2 ^ R * t)
    (hS : IsBalancedFamily t C₁ ε) (ht : 0 < t) (hm : 1 ≤ m)
    (hx : 0 < x) (hx1 : x ≤ 1) (hy : 1/2 < y) (hy1 : y ≤ 1)
    (hh : 0 < h) (hε : 0 ≤ ε) (hz1 : z ≤ 1)
    (hp1 : t ≤ 2 * p) (hp2 : p ≤ t)
    (hgateRank : 2 ^ (2 ^ (m - 1)) < ⌈(2 : ℝ) ^ p * z⌉₊)
    (hgateOne : y ≤ yLoss ε t h (R + (m + 1)))
    (hgateSeed : z ≤ h * (2 : ℝ) ^ (-((m + 1 : ℕ) : ℝ)) / (1 + ε))
    (hrow : (2 : ℝ) ^ R * x ≤ 1) (hρ : h ≤ ρ) (hρ1 : ρ ≤ 1)
    (hfull : ((2 ^ R * p + 2 : ℕ) : ℝ) ≤ (3 / 5 : ℝ) * (width a : ℝ))
    (hhalf : ((2 ^ (R - 1) * p + 2 : ℕ) : ℝ) ≤
      (3 / 10 : ℝ) * (width a : ℝ)) :
    D (firstTranspose ha C₁) = a + 1 ∧
    a + 1 ≤ Dfamily (interlaceFun (firstTranspose ha C₁) 1)
      (bracketGE (Fin N) (Fin (width a)) 1 ρ (3 / 5)) ∧
    a ≤ Dfamily (interlaceFun (firstTranspose ha C₁) 1)
      (bracketGE (Fin N) (Fin (width a)) 1 ρ (3 / 10)) := by
  classical
  have hfullProfile := transpose_oneCopy_lower ha C₁ hN hwidth hS ht hm
    hx hx1 hy hy1 hh hε hz1 hp1 hp2 hgateRank hgateOne hgateSeed
    R (le_refl _) hrow hρ hρ1 (by norm_num : (3 / 5 : ℝ) ≤ 1) hfull
  have hrowHalf : (2 : ℝ) ^ (R - 1) * x ≤ 1 :=
    (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.sub_le R 1)) hx.le).trans hrow
  have hhalfProfile := transpose_oneCopy_lower ha C₁ hN hwidth hS ht hm
    hx hx1 hy hy1 hh hε hz1 hp1 hp2 hgateRank hgateOne hgateSeed
    (R - 1) (Nat.sub_le R 1) hrowHalf hρ hρ1
    (by norm_num : (3 / 10 : ℝ) ≤ 1) hhalf
  have hfullWidth : ((2 ^ R * p + 2 : ℕ) : ℝ) ≤ (1 : ℝ) * (width a : ℝ) :=
    hfull.trans (mul_le_mul_of_nonneg_right (by norm_num) (Nat.cast_nonneg _))
  have hcost := transpose_subgame_lower ha C₁ hwidth hS ht hm hx hx1 hy hy1
    hh hε hz1 hp1 hp2 hgateRank hgateOne hgateSeed
    R (le_refl _) hrow (hρ.trans hρ1) hfullWidth Finset.univ Finset.univ
    (by simp) (by simp)
  have hcostLower : a + 1 ≤ D (firstTranspose ha C₁) := by
    have hmap := D_mapNodes_le (firstTranspose ha C₁)
      (fun j : ↥(Finset.univ : Finset (Fin N)) => j.val)
      (fun i : ↥(Finset.univ : Finset (Fin (width a))) => i.val)
    have hbound := hcost.trans hmap
    simpa [haeq, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbound
  have hcostUpper : D (firstTranspose ha C₁) ≤ a + 1 := by
    have htranspose : D (firstTranspose ha C₁) = D (duplicatedFirstMatrix ha C₁) :=
      comp_transpose (duplicatedFirstMatrix ha C₁)
    rw [htranspose]
    exact D_duplicatedFirstMatrix_le ha C₁
  refine ⟨le_antisymm hcostUpper hcostLower, ?_, ?_⟩
  · simpa [haeq, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfullProfile
  · have heq : m + 1 + (R - 1) = a := by omega
    rwa [heq] at hhalfProfile

end EthInapproximability.CurrentPaper.ExactFirstProfiles
