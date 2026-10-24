import EthInapproximability.CurrentPaper.AlignedProtectedProfiles

/-!
# Parameter-specialized assembly of the scale-aligned profiles

Source: frozen v8 `A-stage4-details.tex`, `eq:paper-scale-aligned-dense` and
the ensuing transposition argument.  This interface deliberately displays the
actual near-full restriction theorem as an input.  Its producer is the global
row-count proof, not the reference-only moderate-profile argument.
-/

noncomputable section
open scoped Classical

namespace EthInapproximability.CurrentPaper.ConcreteAlignedProfiles

open NPCC Workspace.Types.CommComplexity Workspace.Types.Interlace
open Parameters Construction AlignedProtectedProfiles ExactResidualIndexing
open EthInapproximability.ParameterizedNP

variable {X Ref Y : Type*} [Fintype X] [Fintype Ref] [Fintype Y]
  [DecidableEq Y] [Nonempty X] [Nonempty Ref] [Nonempty Y]

/-- All three profiles and exact cost of the same transposed outer interlace.
The public parameter formulas discharge every scalar alignment gate. -/
theorem profiles (N : X → Y → Bool) (e : Ref ↪ X) (i : Input)
    (hc : 0 < i.sourceConstant)
    (hprop : (Fintype.card Ref : ℝ) = (91 / 92 : ℝ) * Fintype.card X)
    (h1 : certificateCost i - 1 ≤
      Dfamily (interlaceFun (fun r y => N (e r) y) 1)
        (bracketGE Ref Y 1 ((2 : ℝ) ^ (-(tailDepth i : ℝ))) (3 / 5)))
    (h2 : certificateCost i - 2 ≤
      Dfamily (interlaceFun (fun r y => N (e r) y) 1)
        (bracketGE Ref Y 1 ((2 : ℝ) ^ (-(tailDepth i : ℝ))) (3 / 10)))
    (hupper : D N ≤ certificateCost i)
    (hnear : ∀ (A : Finset (Fin (outerWidth i) × X))
      (S : Finset (Fin (outerWidth i) → Y)),
      (1 - (columnLoss i : ℝ)) * (outerWidth i : ℝ) * Fintype.card X ≤ A.card →
      (retainedFraction i : ℝ) * (Fintype.card Y : ℝ) ^ outerWidth i ≤ S.card →
      certificateCost i + outerExponent i ≤ D (subgame (interlaceFun N (outerWidth i)) A S)) :
    let W := Function.swap (interlaceFun N (outerWidth i))
    let C := certificateCost i + outerExponent i
    D W = C ∧
    C ≤ Dfamily (interlaceFun W 1)
      (bracketGE (Fin (outerWidth i) → Y) (Fin (outerWidth i) × X) 1
        (retainedFraction i : ℝ) (1 - (columnLoss i : ℝ))) ∧
    C - 1 ≤ Dfamily (interlaceFun W 1)
      (bracketGE (Fin (outerWidth i) → Y) (Fin (outerWidth i) × X) 1
        (retainedFraction i : ℝ) (3 / 5)) ∧
    C - 2 ≤ Dfamily (interlaceFun W 1)
      (bracketGE (Fin (outerWidth i) → Y) (Fin (outerWidth i) × X) 1
        (retainedFraction i : ℝ) (3 / 10)) := by
  classical
  let W := Function.swap (interlaceFun N (outerWidth i))
  have hθ : (retainedFraction i : ℝ) ≤ 1 := by
    have hQ : (1 : ℚ) ≤ restorationWidth i := by exact_mod_cast restorationWidth_pos i
    have h : retainedFraction i ≤ (1 : ℚ) := by
      unfold retainedFraction
      apply (div_le_one (by positivity)).mpr
      linarith
    exact_mod_cast h
  have hδ : (0 : ℝ) ≤ (columnLoss i : ℝ) := by
    have hh : (0 : ℚ) ≤ columnLoss i := le_of_lt (columnLoss_pos i hc)
    exact_mod_cast hh
  have hn : certificateCost i + outerExponent i ≤ Dfamily (interlaceFun W 1)
      (bracketGE (Fin (outerWidth i) → Y) (Fin (outerWidth i) × X) 1
        (retainedFraction i : ℝ) (1 - (columnLoss i : ℝ))) := by
    apply oneCopy_family_lower_of_subgame W hθ (by linarith)
    intro S A hS hA
    have ht : D (subgame W S A) = D (subgame (interlaceFun N (outerWidth i)) A S) :=
      comp_transpose _
    rw [ht]
    apply hnear A S
    · simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul,
        mul_comm, mul_left_comm, mul_assoc] using hA
    · simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, mul_comm] using hS
  have hmod := aligned_moderate_profiles_parameters N e i hprop h1 h2
  have hup : D W ≤ certificateCost i + outerExponent i := by
    change D (fun γ r => interlaceFun N (outerWidth i) r γ) ≤ _
    rw [comp_transpose]
    exact (powerOfTwoInterlace_upper N (outerExponent i)).trans
      (Nat.add_le_add_right hupper _)
  have hlo : certificateCost i + outerExponent i ≤ D W := by
    have hall := hnear Finset.univ Finset.univ
      (by
        simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
        have hh := mul_le_of_le_one_left
          (show (0 : ℝ) ≤ outerWidth i * Fintype.card X by positivity)
          (show 1 - (columnLoss i : ℝ) ≤ 1 by linarith)
        simpa only [mul_assoc] using hh)
      (by
        simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
        exact mul_le_of_le_one_left (by positivity) hθ)
    have hsub := D_mapNodes_le (interlaceFun N (outerWidth i))
      (fun r : ↥(Finset.univ : Finset (Fin (outerWidth i) × X)) => r.val)
      (fun γ : ↥(Finset.univ : Finset (Fin (outerWidth i) → Y)) => γ.val)
    change certificateCost i + outerExponent i ≤
      D (fun γ r => interlaceFun N (outerWidth i) r γ)
    rw [comp_transpose]
    exact hall.trans hsub
  exact ⟨le_antisymm hup hlo, hn, hmod.1, hmod.2⟩

end EthInapproximability.CurrentPaper.ConcreteAlignedProfiles
