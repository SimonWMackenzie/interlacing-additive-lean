import EthInapproximability.CurrentPaper.ProtectedRoutedBound
import EthInapproximability.CurrentPaper.AmplificationInnerProfiles

/-!
# Literal parameter instantiation of the protected ordinary-child inputs

Source: frozen v8 `A-stage4-details.tex`,
`lem:paper-protected-routed-closure`, and `F-parameter-choices.tex`.
Every ordinary-child profile, balance condition, and scalar gate is derived
from the accepted literal parameter formulas and the source matrix's own
robustness and cost. No constructed-matrix profile is assumed.
-/

namespace EthInapproximability.CurrentPaper.ProtectedScheduledOrdinary

open NPCC Workspace.Types.CommComplexity Workspace.Types.Interlace
open Parameters Construction AmplificationInnerProfiles AmplificationFirstProfiles

noncomputable section

theorem dense_stopping_gates (i : Input) :
    (3 / 5 : ℝ) ≤ yLoss (1 / (100 * (balanceOrder i : ℝ)))
      (balanceOrder i) (998 / 1000) (i.cost + firstExponent i + secondExponent i) ∧
    HardSeed.columnDensity (balanceOrder i : ℝ) ≤
      (998 / 1000 : ℝ) * (2 : ℝ) ^
        (-((i.cost + firstExponent i + balanceExponent i : ℕ) : ℝ)) /
          (1 + 1 / (100 * (balanceOrder i : ℝ))) := by
  have ht : (1 : ℝ) ≤ balanceOrder i := by exact_mod_cast balanceOrder_pos i
  have hloss : 1 ≤ ParameterGates.lossBudget i := by
    unfold ParameterGates.lossBudget
    omega
  have hh : (2 : ℝ) ^ (-(ParameterGates.lossBudget i : ℝ)) ≤ 998 / 1000 := by
    calc
      _ ≤ (2 : ℝ) ^ (-(1 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (neg_le_neg (by exact_mod_cast hloss))
      _ ≤ _ := by norm_num
  have hε : (1 : ℝ) / (100 * (balanceOrder i : ℝ)) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    linarith
  exact ParameterGates.all_stopping_gates i (le_refl _) (Nat.le_add_left _ _)
    hh (by positivity) hε

theorem dense_projected_density (i : Input) :
    (9 / 25 : ℝ) ≤ (998 / 1000) /
      (2 * (1 + 1 / (100 * (balanceOrder i : ℝ)))) := by
  have ht : (1 : ℝ) ≤ balanceOrder i := by exact_mod_cast balanceOrder_pos i
  have hε : (1 : ℝ) / (100 * (balanceOrder i : ℝ)) ≤ 1 / 100 := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 100)).mpr
    linarith
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (1 + 1 / (100 * (balanceOrder i : ℝ))))]
  nlinarith

/-- The family is the very same indexed sampler, transported only along
the asserted equality of finite coordinate counts. -/
theorem scheduled_ordinary (i : Input) (hc : 0 < i.sourceConstant) (ha : Accepted i)
    (f : Fin i.rows → Fin i.columns → Bool)
    (hf : IsRobustAt f i.incomingDepth) (hcost : D f = i.cost)
    (R : ℕ) (hsum : R + balanceExponent i = secondExponent i)
    (hwidth : secondWidth i = 2 ^ R * 2 ^ balanceExponent i) :
    ProtectedRoutedBound.OrdinaryInputs (H := i.cost + firstExponent i)
      (firstTranspose f (firstExponent i) (bins i))
      (fun l α => scheduledFamily i ha l (Fin.cast hwidth.symm α))
      ((2 : ℝ) ^ (-(firstDepth i : ℝ))) (998 / 1000)
      (1 / (100 * (balanceOrder i : ℝ))) := by
  classical
  letI : NeZero i.rows := ⟨by have := ha.1; omega⟩
  letI : NeZero i.columns := ⟨by have := ha.2.1; omega⟩
  have hp := scheduled_first_profiles f i ha hf
  rw [hcost] at hp
  have hscalar := AmplificationSecondGates.scalar_gates i hc ha
  have ha2 : 2 ≤ firstExponent i := by
    have := (ParameterGates.hard_seed_exponent_domains i).2.2.1
    omega
  have hb : IsBalancedFamily (balanceOrder i) (scheduledFamily i ha)
      (1 / (100 * (balanceOrder i : ℝ))) :=
    ParameterGates.actualSecondFamily_balanced i hc ha
  have ht := hb.projection (Fin.cast hwidth.symm) (by
    intro a b hab
    apply Fin.ext
    exact congrArg (fun z : Fin (secondWidth i) => z.val) hab)
  have hg := dense_stopping_gates i
  refine ⟨by omega, AmplificationSecondGates.balanceExponent_floor i,
    by positivity, hscalar.2.2.2.1, by positivity, by norm_num,
    hp.2.1, hp.2.2, ht, dense_projected_density i, ?_, ?_⟩
  · simpa only [hsum, balanceOrder] using hg.1
  · simpa only [balanceOrder, Nat.cast_pow, Nat.cast_ofNat] using hg.2

end

end EthInapproximability.CurrentPaper.ProtectedScheduledOrdinary
