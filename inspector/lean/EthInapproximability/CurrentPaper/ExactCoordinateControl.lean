import EthInapproximability.CurrentPaper.CertifiedStopping
import EthInapproximability.CurrentPaper.ExactConstruction
import EthInapproximability.CurrentPaper.IndexedProjection
import EthInapproximability.CurrentPaper.ProtocolSeparation
import EthInapproximability.CurrentPaper.TerminalExcess

/-!
# Coordinate restrictions in the exact reduction

Source: v8 `E-exact-details.tex`, `lem:exact-coordinate-restrictions` and
`lem:exact-structure`. The scalar stopping point is supplied by the current
two-bound hard-seed theorem. Unlike the ETH specialization, the nonconstancy
input is at an independently specified column fraction `yzero`, which may
be much smaller than `3/5`. All sampled columns remain indexed labels.

The numerical cutoff and the one-copy estimates for the actual duplicated
indexing matrix are separate inputs. No sampled coordinate restriction or
protocol-separation conclusion is assumed by `coordinateRestriction`.
-/

noncomputable section

namespace EthInapproximability.CurrentPaper.ExactCoordinateControl

open NPCC Workspace.Types.CommComplexity Workspace.Types.Interlace
open Workspace.Types.Protocol
open ProtocolSeparation

/-- The coordinate stopping argument, allowing the paper's weak early-leaf
nonconstancy bound rather than requiring nonconstancy at fraction `3/5`.
Here `d = 2^R * 2^m`, and `x = d^(-2)` in the exact reduction. -/
theorem coordinateRestriction {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq Y] [Nonempty X] [Nonempty Y]
    (f : X → Y → Bool) {H m R : ℕ} {x h ε yzero : ℝ}
    (hH : 2 ≤ H) (hm : 2 ^ 20 ≤ m) (hx : 0 < x)
    (hrow : (2 : ℝ) ^ m * x ≤ 1) (hε : 0 ≤ ε) (hh : 0 < h)
    (h1 : H ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (3 / 5)))
    (h2 : H - 1 ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (3 / 10)))
    (hone : 1 ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x yzero))
    {L : ℕ} (S : Fin L → Fin (2 ^ R * 2 ^ m) → Y)
    (hS : IsBalancedFamily (2 ^ m) S ε)
    (hgateOne : yzero ≤ yLoss ε (2 ^ m) h (H + (R + m)))
    (hgateSeed : HardSeed.columnDensity ((2 : ℝ) ^ m) ≤
      h * (2 : ℝ) ^ (-((H + m : ℕ) : ℝ)) / (1 + ε))
    (a R' : ℕ) (ha : a ≤ 1) (hR' : R' ≤ R)
    (Rs : Finset (Fin (2 ^ R * 2 ^ m) × X)) (Cs : Finset (Fin L))
    (hRs : ∃ Qs : Finset (Fin (2 ^ R * 2 ^ m)),
      Qs.card = 2 ^ R' * HardSeed.copyCount m ∧
      IsEquipartitionedGE Rs Qs
        ⌈(2 : ℝ) ^ (R' + m) * x * (Fintype.card X : ℝ)⌉₊)
    (hCs : h * (2 : ℝ) ^ (-(a : ℝ)) * (L : ℝ) ≤ (Cs.card : ℝ)) :
    H + (R' + m) ≤ D (subgame (relaxedInterlace f S) Rs Cs) := by
  have hgamma : (3 / 5 : ℝ) ≤ 1 / Real.sqrt 2 := by
    rw [le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))]
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have hhalf : H - 1 ≤ Dfamily (interlaceFun f 1)
      (bracketGE X Y 1 x ((3 / 5 : ℝ) / 2)) := by
    convert h2 using 1; norm_num
  have hseed := HardSeed.hardSeed_cost f hH hm hx
    (by norm_num : (0 : ℝ) < 3 / 5) hgamma h1 hhalf hrow
  obtain ⟨_, hpLow, hpHigh⟩ := HardSeed.copyCount_bounds (show 5 ≤ m by omega)
  have hxGrow : x ≤ (2 : ℝ) ^ m * x := by
    simpa using mul_le_mul_of_nonneg_right
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hx.le
  have hRs' : ∃ Qs : Finset (Fin (2 ^ R * 2 ^ m)),
      Qs.card = 2 ^ R' * HardSeed.copyCount m ∧
      IsEquipartitionedGE Rs Qs
        ⌈(2 : ℝ) ^ R' * ((2 : ℝ) ^ m * x) * (Fintype.card X : ℝ)⌉₊ := by
    simpa [pow_add, mul_assoc] using hRs
  have hgateOne' : yzero ≤ yLoss ε (2 ^ m) h (R + (H + m)) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hgateOne
  have hs := CertifiedStopping.scalar_stopping f hε (2 ^ m) R (H + m)
    (by positivity) S hS (HardSeed.copyCount m) hx hxGrow hrow hh hpLow hpHigh
    hone hgateOne' hseed hgateSeed a R' ha hR' Rs Cs hRs' hCs
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs

/-- More blocks and more retained rows only help the coordinate restriction.
The threshold is a natural ceiling, so there is no silent rounding step. -/
theorem coordinateBlockLowerBound {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq Y] [Nonempty X] [Nonempty Y]
    (f : X → Y → Bool) {H m R : ℕ} {x h ε yzero z : ℝ}
    (hH : 2 ≤ H) (hm : 2 ^ 20 ≤ m) (hx : 0 < x)
    (hrow : (2 : ℝ) ^ m * x ≤ 1) (hε : 0 ≤ ε) (hh : 0 < h)
    (h1 : H ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (3 / 5)))
    (h2 : H - 1 ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (3 / 10)))
    (hone : 1 ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x yzero))
    {L : ℕ} (S : Fin L → Fin (2 ^ R * 2 ^ m) → Y)
    (hS : IsBalancedFamily (2 ^ m) S ε)
    (hgateOne : yzero ≤ yLoss ε (2 ^ m) h (H + (R + m)))
    (hgateSeed : HardSeed.columnDensity ((2 : ℝ) ^ m) ≤
      h * (2 : ℝ) ^ (-((H + m : ℕ) : ℝ)) / (1 + ε))
    (a R' p T : ℕ) (ha : a ≤ 1) (hR' : R' ≤ R)
    (hp : 2 ^ R' * HardSeed.copyCount m ≤ p)
    (hT : ⌈(2 : ℝ) ^ (R' + m) * x * (Fintype.card X : ℝ)⌉₊ ≤ T)
    (hz : h * (2 : ℝ) ^ (-(a : ℝ)) ≤ z) :
    BlockLowerBound (relaxedInterlace f S) Prod.fst Finset.univ p T z
      (H + (R' + m)) := by
  classical
  intro Rs Cs Qs _ hCs hQs hRows
  obtain ⟨Qs', hsub, hcard⟩ := Finset.exists_subset_card_eq (hp.trans hQs)
  apply coordinateRestriction f hH hm hx hrow hε hh h1 h2 hone S hS
    hgateOne hgateSeed a R' ha hR' Rs Cs
  · exact ⟨Qs', hcard, fun i hi => hT.trans (hRows i (hsub hi))⟩
  · have hCs' : z * (L : ℝ) ≤ (Cs.card : ℝ) := by simpa using hCs
    exact (mul_le_mul_of_nonneg_right hz (Nat.cast_nonneg L)).trans hCs'

/-- Transport the numerical width equality before performing the stopping
proof. In particular `q` can be the paper's single coordinate width `2^k`;
no matrix is replaced by an unrelated function with a matching cost. -/
theorem coordinateBlockLowerBound_of_width {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq Y] [Nonempty X] [Nonempty Y]
    (f : X → Y → Bool) {H m R q : ℕ} {x h ε yzero z : ℝ}
    (hwidth : q = 2 ^ R * 2 ^ m)
    (hH : 2 ≤ H) (hm : 2 ^ 20 ≤ m) (hx : 0 < x)
    (hrow : (2 : ℝ) ^ m * x ≤ 1) (hε : 0 ≤ ε) (hh : 0 < h)
    (h1 : H ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (3 / 5)))
    (h2 : H - 1 ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (3 / 10)))
    (hone : 1 ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x yzero))
    {L : ℕ} (S : Fin L → Fin q → Y)
    (hS : IsBalancedFamily (2 ^ m) S ε)
    (hgateOne : yzero ≤ yLoss ε (2 ^ m) h (H + (R + m)))
    (hgateSeed : HardSeed.columnDensity ((2 : ℝ) ^ m) ≤
      h * (2 : ℝ) ^ (-((H + m : ℕ) : ℝ)) / (1 + ε))
    (a R' p T : ℕ) (ha : a ≤ 1) (hR' : R' ≤ R)
    (hp : 2 ^ R' * HardSeed.copyCount m ≤ p)
    (hT : ⌈(2 : ℝ) ^ (R' + m) * x * (Fintype.card X : ℝ)⌉₊ ≤ T)
    (hz : h * (2 : ℝ) ^ (-(a : ℝ)) ≤ z) :
    BlockLowerBound (relaxedInterlace f S) Prod.fst Finset.univ p T z
      (H + (R' + m)) := by
  subst q
  exact coordinateBlockLowerBound f hH hm hx hrow hε hh h1 h2 hone S hS
    hgateOne hgateSeed a R' p T ha hR' hp hT hz

/-- Total retained row density supplies the specified number of good
coordinate blocks. This is the counting step for robustness of `Q^T`.
Both the number of blocks and the per-block floor retain their ceilings. -/
theorem denseRows_supply {X : Type*} [Fintype X] [Nonempty X]
    {q v : ℕ} (hq : 0 < q) {R : Finset (Fin q × X)} {β x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) (hv : 1 ≤ v)
    (hR : β * ((q : ℝ) * (Fintype.card X : ℝ)) ≤ R.card)
    (hcount : v ≤ ⌈(q : ℝ) * (β - x) / (1 - x)⌉₊) :
    ∃ Q : Finset (Fin q), Q.card = v ∧
      IsEquipartitionedGE R Q ⌈(Fintype.card X : ℝ) * x⌉₊ := by
  have hdenpos : 0 < (q : ℝ) * (Fintype.card X : ℝ) := by
    have : 0 < Fintype.card X := Fintype.card_pos
    positivity
  have hβ : β ≤ (R.card : ℝ) / ((q : ℝ) * (Fintype.card X : ℝ)) :=
    (le_div_iff₀ hdenpos).mpr hR
  apply IndexedProjection.enough_good_blocks hx0 hx1 hv
  apply hcount.trans
  apply Nat.ceil_mono
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (sub_le_sub_right hβ x) (Nat.cast_nonneg q))
    (by linarith)

/-- A block-restriction estimate applies to arbitrary dense row sets after
the actual good blocks have been selected; the same retained column labels
are used, with no separate marginal choice. -/
theorem lowerBound_of_denseRows {X Y : Type*} [Fintype X] [Nonempty X]
    {q v T B : ℕ} (F : (Fin q × X) → Y → Bool) (C₀ : Finset Y)
    {β x z : ℝ} (hq : 0 < q) (hx0 : 0 < x) (hx1 : x < 1) (hv : 1 ≤ v)
    (hT : T ≤ ⌈(Fintype.card X : ℝ) * x⌉₊)
    (hcount : v ≤ ⌈(q : ℝ) * (β - x) / (1 - x)⌉₊)
    (hbound : BlockLowerBound F Prod.fst C₀ v T z B)
    (R : Finset (Fin q × X)) (C : Finset Y)
    (hR : β * ((q : ℝ) * (Fintype.card X : ℝ)) ≤ R.card)
    (hCsub : C ⊆ C₀) (hC : z * (C₀.card : ℝ) ≤ C.card) :
    B ≤ D (subgame F R C) := by
  obtain ⟨Q, hQ, hRows⟩ := denseRows_supply hq hx0 hx1 hv hR hcount
  exact hbound R C Q hCsub hC (by omega) (fun i hi => hT.trans (hRows i hi))

/-- The stopping theorem applied to the literal coordinate matrix `Q` of
the exact reduction. The only source-matrix premises concern `Pbar^T`;
neither the desired Q-bound nor any prescribed protocol shape is assumed. -/
theorem exact_coordinateBlockLowerBound
    {a d N₁ N₂ H m R : ℕ} (ha : 2 ≤ a) (hN₁ : 0 < N₁)
    (C₁ : ExactConstruction.FirstFamily a N₁)
    (C₂ : ExactConstruction.SecondFamily a d N₂)
    {x h ε yzero z : ℝ} (hwidth : d = 2 ^ R * 2 ^ m)
    (hH : 2 ≤ H) (hm : 2 ^ 20 ≤ m) (hx : 0 < x)
    (hrow : (2 : ℝ) ^ m * x ≤ 1) (hε : 0 ≤ ε) (hh : 0 < h)
    (h1 : H ≤ Dfamily
      (interlaceFun (fun ℓ i => ExactConstruction.duplicatedFirstMatrix ha C₁ i ℓ) 1)
      (bracketGE (Fin N₁) (Fin (ExactConstruction.width a)) 1 x (3 / 5)))
    (h2 : H - 1 ≤ Dfamily
      (interlaceFun (fun ℓ i => ExactConstruction.duplicatedFirstMatrix ha C₁ i ℓ) 1)
      (bracketGE (Fin N₁) (Fin (ExactConstruction.width a)) 1 x (3 / 10)))
    (hone : 1 ≤ Dfamily
      (interlaceFun (fun ℓ i => ExactConstruction.duplicatedFirstMatrix ha C₁ i ℓ) 1)
      (bracketGE (Fin N₁) (Fin (ExactConstruction.width a)) 1 x yzero))
    (hS : IsBalancedFamily (2 ^ m) C₂ ε)
    (hgateOne : yzero ≤ yLoss ε (2 ^ m) h (H + (R + m)))
    (hgateSeed : HardSeed.columnDensity ((2 : ℝ) ^ m) ≤
      h * (2 : ℝ) ^ (-((H + m : ℕ) : ℝ)) / (1 + ε))
    (j R' p T : ℕ) (hj : j ≤ 1) (hR' : R' ≤ R)
    (hp : 2 ^ R' * HardSeed.copyCount m ≤ p)
    (hT : ⌈(2 : ℝ) ^ (R' + m) * x * (N₁ : ℝ)⌉₊ ≤ T)
    (hz : h * (2 : ℝ) ^ (-(j : ℝ)) ≤ z) :
    BlockLowerBound (ExactConstruction.secondMatrix ha C₁ C₂) Prod.fst
      Finset.univ p T z (H + (R' + m)) := by
  letI : Nonempty (Fin N₁) := ⟨⟨0, hN₁⟩⟩
  have hw : 0 < ExactConstruction.width a := by
    unfold ExactConstruction.width
    positivity
  letI : Nonempty (Fin (ExactConstruction.width a)) := ⟨⟨0, hw⟩⟩
  exact coordinateBlockLowerBound_of_width
    (fun ℓ i => ExactConstruction.duplicatedFirstMatrix ha C₁ i ℓ)
    hwidth hH hm hx hrow hε hh h1 h2 hone C₂ hS hgateOne hgateSeed
    j R' p T hj hR' hp (by simpa using hT) hz

end EthInapproximability.CurrentPaper.ExactCoordinateControl
