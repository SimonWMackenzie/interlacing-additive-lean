import EthInapproximability.CurrentPaper.AlignedProtectedProfiles
import EthInapproximability.CurrentPaper.IndexedProjection

/-!
# The first amplification interlace and its two profiles

Source: locked v8 `03-parameterized-construction.tex`,
`eq:paper-M1-definition` and `eq:paper-M1-robust`.
The matrix is literally `Construction.firstMatrix`, including its unused
tail coordinates. The input has exactly the two bounds in `IsRobustAt`.
The profile proofs use full-product counting and the current hard-seed
theorem independently at exponents `a` and `a-1`.
-/

noncomputable section

namespace EthInapproximability.CurrentPaper.AmplificationFirstProfiles

open NPCC Workspace.Types.CommComplexity Workspace.Types.Interlace
open Construction

universe u
variable {X Y : Type u} [Fintype X] [Fintype Y]

/-- The actual first matrix with the parties exchanged. -/
def firstTranspose (R : X → Y → Bool) (a s : ℕ) :
    FirstColumns a s Y → FirstRows a X → Bool :=
  fun c r => firstMatrix R a s r c

/-- Sending the first coordinate costs at most `a` bits. -/
theorem firstMatrix_upper [Nonempty Y] (R : X → Y → Bool) (a s : ℕ) :
    D (firstMatrix R a s) ≤ D R + a := by
  classical
  let row : FirstRows a X → Fin (2 ^ a) × X := fun r =>
    (⟨r.1.val, lt_of_lt_of_le r.1.isLt (Nat.sub_le _ _)⟩, r.2)
  let col : FirstColumns a s Y → Fin (2 ^ a) → Y := fun c i =>
    if hi : i.val < qOne a then c (firstCoordinate a s ⟨i.val, hi⟩)
    else Classical.arbitrary Y
  have heq : firstMatrix R a s =
      fun r c => interlaceFun R (2 ^ a) (row r) (col c) := by
    funext r c
    simp [firstMatrix, interlaceFun, row, col, r.1.isLt]
  rw [heq]
  exact (D_mapNodes_le _ row col).trans
    (EthInapproximability.ParameterizedNP.powerOfTwoInterlace_upper R a)

/-- Density alone supplies the ceiling count needed by block extraction. -/
theorem goodBlocks_of_density [Nonempty X] {q p : ℕ} {α β : ℝ}
    (hq : 0 < q) (hα : 0 < α) (hαβ : α < β) (hβ : β ≤ 1)
    (hp : 1 ≤ p)
    (hcount : p ≤ ⌈(q : ℝ) * (β - α) / (1 - α)⌉₊)
    (A : Finset (Fin q × X))
    (hA : ((q : ℝ) * Fintype.card X) * β ≤ A.card) :
    ∃ Q : Finset (Fin q), Q.card = p ∧
      IsEquipartitionedGE A Q ⌈(Fintype.card X : ℝ) * α⌉₊ := by
  have hden : (0 : ℝ) < (q : ℝ) * Fintype.card X := by
    exact mul_pos (Nat.cast_pos.mpr hq)
      (Nat.cast_pos.mpr (Fintype.card_pos (α := X)))
  have hβA : β ≤ (A.card : ℝ) / ((q : ℝ) * Fintype.card X) :=
    (le_div_iff₀ hden).mpr (by simpa [mul_comm] using hA)
  apply IndexedProjection.enough_good_blocks hα (hαβ.trans_le hβ) hp
  apply hcount.trans (Nat.ceil_mono ?_)
  apply div_le_div_of_nonneg_right _ (by linarith)
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right hβA α) (Nat.cast_nonneg q)

/-- The actual transposed restriction inherits the current small-density
bound. All additional hypotheses are explicit scalar extraction gates.
The density comparison is a sufficient form of the printed strict ceiling
test; the unused tail is kept in the full-product label enumeration. -/
theorem transpose_subgame_lower [Nonempty X] [Nonempty Y]
    (R : X → Y → Bool) {a s b₀ m : ℕ} {ρ β : ℝ}
    (hR : IsRobustAt R b₀) (hq : 0 < qOne a) (hm : 2 ^ 20 ≤ m)
    (hαβ : (2 : ℝ) ^ m * (2 : ℝ) ^ (-(b₀ : ℝ)) < β)
    (hβ : β ≤ 1)
    (hcount : HardSeed.copyCount m ≤
      ⌈(qOne a : ℝ) *
        (β - (2 : ℝ) ^ m * (2 : ℝ) ^ (-(b₀ : ℝ))) /
        (1 - (2 : ℝ) ^ m * (2 : ℝ) ^ (-(b₀ : ℝ)))⌉₊)
    (hcol : HardSeed.columnDensity ((2 : ℝ) ^ m) ≤ ρ)
    (J : Finset (FirstColumns a s Y)) (A : Finset (FirstRows a X))
    (hJ : (Fintype.card (FirstColumns a s Y) : ℝ) * ρ ≤ J.card)
    (hA : (Fintype.card (FirstRows a X) : ℝ) * β ≤ A.card) :
    D R + m ≤ D (subgame (firstTranspose R a s) J A) := by
  classical
  let α := (2 : ℝ) ^ m * (2 : ℝ) ^ (-(b₀ : ℝ))
  have hα : 0 < α := by dsimp [α]; positivity
  have hp : 1 ≤ HardSeed.copyCount m := by
    unfold HardSeed.copyCount
    have := Nat.one_le_pow (m - 5) 2 (by omega)
    omega
  obtain ⟨Q, hQcard, hQ⟩ := goodBlocks_of_density hq hα hαβ hβ hp hcount A
    (by simpa [Fintype.card_prod, Fintype.card_fin] using hA)
  let e : Fin (HardSeed.copyCount m) ≃ ↥Q :=
    (finCongr hQcard.symm).trans (Finset.equivFin Q).symm
  let E : Fin (Fintype.card (FirstColumns a s Y)) ≃ FirstColumns a s Y :=
    (Fintype.equivFin _).symm
  let S : Fin (Fintype.card (FirstColumns a s Y)) → Fin (qOne a) → Y :=
    fun j i => E j (firstCoordinate a s i)
  have hS : IsBalancedFamily (HardSeed.copyCount m) S 0 :=
    (AlignedProtectedProfiles.fullProduct_balanced (HardSeed.copyCount m) E).projection
      (firstCoordinate a s) (by
        intro i j hij
        apply Fin.ext
        exact congrArg (fun z : Fin (firstLength a s) => z.val) hij)
  let K := J.image E.symm
  have hK : K.card = J.card := Finset.card_image_of_injective _ E.symm.injective
  obtain ⟨RC, hRC, _, _, hcost⟩ := IndexedProjection.balanced_projection R
    (by omega : 0 < HardSeed.copyCount m) (le_refl _) hS (by norm_num) e hQ
    (show HardSeed.columnDensity ((2 : ℝ) ^ m) *
        (Fintype.card (FirstColumns a s Y) : ℝ) ≤ K.card from by
      rw [hK]
      exact (mul_le_mul_of_nonneg_right hcol (Nat.cast_nonneg _)).trans
        (by simpa [mul_comm] using hJ))
  have hRC' : RC ∈ bracketGE X Y (HardSeed.copyCount m) α
      (HardSeed.columnDensity ((2 : ℝ) ^ m)) := by simpa using hRC
  have hgamma : (3 / 5 : ℝ) ≤ 1 / Real.sqrt 2 := by
    rw [le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))]
    have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have hhalf : D R - 1 ≤ Dfamily (interlaceFun R 1)
      (bracketGE X Y 1 ((2 : ℝ) ^ (-(b₀ : ℝ))) ((3 / 5 : ℝ) / 2)) := by
    convert hR.2.2.2 using 1
    norm_num
  have hseed := HardSeed.hardSeed_cost R hR.2.1 hm
    (by positivity : 0 < (2 : ℝ) ^ (-(b₀ : ℝ)))
    (by norm_num : (0 : ℝ) < 3 / 5) hgamma hR.2.2.1 hhalf
    (hαβ.le.trans hβ)
  have hmember : Dfamily (interlaceFun R (HardSeed.copyCount m))
      (bracketGE X Y (HardSeed.copyCount m) α
        (HardSeed.columnDensity ((2 : ℝ) ^ m))) ≤
      D (subgame (interlaceFun R (HardSeed.copyCount m)) RC.1 RC.2) :=
    Nat.sInf_le ⟨RC, hRC', rfl⟩
  have hKmem (j : ↥K) : E j.val ∈ J := by
    obtain ⟨c, hc, heq⟩ := Finset.mem_image.mp j.property
    rw [← heq, E.apply_symm_apply]
    exact hc
  let κ : ↥K → ↥J := fun j => ⟨E j.val, hKmem j⟩
  have hmap : D (subgame (relaxedInterlace R S) A K) ≤
      D (subgame (firstMatrix R a s) A J) :=
    D_mapNodes_le (subgame (firstMatrix R a s) A J) (fun r : ↥A => r) κ
  have ht : D (subgame (firstTranspose R a s) J A) =
      D (subgame (firstMatrix R a s) A J) :=
    comp_transpose (subgame (firstMatrix R a s) A J)
  rw [ht]
  exact hseed.trans (hmember.trans (hcost.trans hmap))

/-- One-copy form of the literal transpose restriction bound. -/
theorem transpose_oneCopy_lower [Nonempty X] [Nonempty Y]
    (R : X → Y → Bool) {a s b₀ m : ℕ} {ρ β : ℝ}
    (hR : IsRobustAt R b₀) (hq : 0 < qOne a) (hm : 2 ^ 20 ≤ m)
    (hαβ : (2 : ℝ) ^ m * (2 : ℝ) ^ (-(b₀ : ℝ)) < β)
    (hβ : β ≤ 1) (hρ : ρ ≤ 1)
    (hcount : HardSeed.copyCount m ≤
      ⌈(qOne a : ℝ) *
        (β - (2 : ℝ) ^ m * (2 : ℝ) ^ (-(b₀ : ℝ))) /
        (1 - (2 : ℝ) ^ m * (2 : ℝ) ^ (-(b₀ : ℝ)))⌉₊)
    (hcol : HardSeed.columnDensity ((2 : ℝ) ^ m) ≤ ρ) :
    D R + m ≤ Dfamily (interlaceFun (firstTranspose R a s) 1)
      (bracketGE (FirstColumns a s Y) (FirstRows a X) 1 ρ β) := by
  apply ExactResidualIndexing.oneCopy_family_lower_of_subgame _ hρ hβ
  intro J A hJ hA
  exact transpose_subgame_lower R hR hq hm hαβ hβ hcount hcol J A hJ hA

/-- Exact first-matrix cost and the two profiles required by the second
interlace, from the source's two-bound robustness and scalar gates only. -/
theorem transpose_profiles [Nonempty X] [Nonempty Y]
    (R : X → Y → Bool) {a s b₀ b₁ : ℕ}
    (hR : IsRobustAt R b₀) (hq : 0 < qOne a) (hm : 2 ^ 20 ≤ a - 1)
    (hαβ : ∀ j : Fin 2,
      (2 : ℝ) ^ (a - j.val) * (2 : ℝ) ^ (-(b₀ : ℝ)) <
        (3 / 5 : ℝ) / 2 ^ j.val)
    (hcount : ∀ j : Fin 2, HardSeed.copyCount (a - j.val) ≤
      ⌈(qOne a : ℝ) *
        ((3 / 5 : ℝ) / 2 ^ j.val -
          (2 : ℝ) ^ (a - j.val) * (2 : ℝ) ^ (-(b₀ : ℝ))) /
        (1 - (2 : ℝ) ^ (a - j.val) * (2 : ℝ) ^ (-(b₀ : ℝ)))⌉₊)
    (hcol : ∀ j : Fin 2, HardSeed.columnDensity ((2 : ℝ) ^ (a - j.val)) ≤
      (2 : ℝ) ^ (-(b₁ : ℝ))) :
    D (firstMatrix R a s) = D R + a ∧
    D R + a ≤ Dfamily (interlaceFun (firstTranspose R a s) 1)
      (bracketGE (FirstColumns a s Y) (FirstRows a X) 1
        ((2 : ℝ) ^ (-(b₁ : ℝ))) (3 / 5)) ∧
    D R + a - 1 ≤ Dfamily (interlaceFun (firstTranspose R a s) 1)
      (bracketGE (FirstColumns a s Y) (FirstRows a X) 1
        ((2 : ℝ) ^ (-(b₁ : ℝ))) (3 / 10)) := by
  have hρ : (2 : ℝ) ^ (-(b₁ : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (neg_nonpos.mpr (Nat.cast_nonneg _))
  have hα0 := hαβ 0
  have hc0 := hcount 0
  have hz0 := hcol 0
  norm_num only [Fin.val_zero, Nat.sub_zero, pow_zero, div_one] at hα0 hc0 hz0
  have hα1 := hαβ 1
  have hc1 := hcount 1
  have hz1 := hcol 1
  norm_num only [Fin.val_one, pow_one] at hα1 hc1 hz1
  have ha : 1 ≤ a := by omega
  have hm0 : 2 ^ 20 ≤ a := hm.trans (Nat.sub_le _ _)
  have hfull := transpose_oneCopy_lower (s := s) R hR hq hm0 hα0
    (by norm_num : (3 / 5 : ℝ) ≤ 1) hρ hc0 hz0
  have hhalf := transpose_oneCopy_lower (s := s) R hR hq hm hα1
    (by norm_num : (3 / 10 : ℝ) ≤ 1) hρ hc1 hz1
  have hwhole := transpose_subgame_lower (s := s) R hR hq hm0 hα0
    (by norm_num : (3 / 5 : ℝ) ≤ 1) hc0 hz0 Finset.univ Finset.univ
    (by
      simp only [Finset.card_univ]
      exact mul_le_of_le_one_right (Nat.cast_nonneg _) hρ)
    (by
      simp only [Finset.card_univ]
      exact mul_le_of_le_one_right (Nat.cast_nonneg _) (by norm_num))
  have hmap : D (subgame (firstTranspose R a s) Finset.univ Finset.univ) ≤
      D (firstTranspose R a s) := D_mapNodes_le _ Subtype.val Subtype.val
  have ht : D (firstTranspose R a s) = D (firstMatrix R a s) :=
    comp_transpose (firstMatrix R a s)
  have hlower := hwhole.trans hmap
  rw [ht] at hlower
  refine ⟨le_antisymm (firstMatrix_upper R a s) hlower, hfull, ?_⟩
  have heq : D R + (a - 1) = D R + a - 1 := by omega
  rw [heq] at hhalf
  exact hhalf

/-- The literal accepted parameter schedule discharges every scalar gate
in the first-interlace proof. The sole communication premise concerns the
source matrix `R`, at the incoming robustness depth. -/
theorem scheduled_first_profiles [Nonempty X] [Nonempty Y]
    (R : X → Y → Bool) (i : Parameters.Input) (hi : Parameters.Accepted i)
    (hR : IsRobustAt R i.incomingDepth) :
    D (firstMatrix R (Parameters.firstExponent i) (Parameters.bins i)) =
      D R + Parameters.firstExponent i ∧
    D R + Parameters.firstExponent i ≤ Dfamily
      (interlaceFun (firstTranspose R (Parameters.firstExponent i) (Parameters.bins i)) 1)
      (bracketGE (FirstColumns (Parameters.firstExponent i) (Parameters.bins i) Y)
        (FirstRows (Parameters.firstExponent i) X) 1
        ((2 : ℝ) ^ (-(Parameters.firstDepth i : ℝ))) (3 / 5)) ∧
    D R + Parameters.firstExponent i - 1 ≤ Dfamily
      (interlaceFun (firstTranspose R (Parameters.firstExponent i) (Parameters.bins i)) 1)
      (bracketGE (FirstColumns (Parameters.firstExponent i) (Parameters.bins i) Y)
        (FirstRows (Parameters.firstExponent i) X) 1
        ((2 : ℝ) ^ (-(Parameters.firstDepth i : ℝ))) (3 / 10)) := by
  have hm := (ParameterGates.hard_seed_exponent_domains i).2.2.1
  apply transpose_profiles R hR (Parameters.firstWidth_pos i) hm
  · intro j
    have hgate := (ParameterGates.first_extraction_gate i hi j.val (by omega)).2.1
    simpa only [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_natCast, div_eq_mul_inv] using hgate
  · intro j
    have hjm : 5 ≤ Parameters.firstExponent i - j.val := by
      have hj : j.val ≤ 1 := by omega
      norm_num at hm
      omega
    rw [HardSeed.copyCount_eq hjm]
    have hgate := (ParameterGates.first_extraction_gate i hi j.val (by omega)).2.2
    simpa only [qOne, Parameters.firstWidth,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast,
      div_eq_mul_inv, mul_assoc] using hgate
  · intro j
    exact ParameterGates.first_chi_gate i j.val (by omega)

end EthInapproximability.CurrentPaper.AmplificationFirstProfiles
