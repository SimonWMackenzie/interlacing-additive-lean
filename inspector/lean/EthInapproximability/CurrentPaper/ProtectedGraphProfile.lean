import EthInapproximability.CurrentPaper.Foundations
import EthInapproximability.CurrentPaper.ProtectedSourceSchedule

/-!
# Scheduled communication profile for the additional graph copies

Source: frozen v8 `03-parameterized-construction.tex`,
`eq:paper-local-capacity`. The two input bounds in `IsRobustAt` supply the
`qOne a + 3 = 2^a + 1` copy lower bound at the actual scheduled source-row
fraction. The half-column form is its monotonicity consequence used by the
protected local-copy extraction.

The acceptance test supplies the depth guard. No communication lower-bound
premise beyond actual robustness is introduced. This does not yet prove the
geometric extraction or the protected-matrix profile itself.
-/

namespace EthInapproximability.CurrentPaper.ProtectedGraphProfile

open NPCC
open Workspace.Types.CommComplexity Workspace.Types.Interlace
open Parameters ProtectedSourceSchedule

/-- The literal additional-copy estimate at the paper's density `9/25`. -/
theorem local_capacity {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (f : X → Y → Bool) (i : Input)
    (hi : Accepted i) (hf : IsRobustAt f i.incomingDepth) :
    D f + firstExponent i + 1 ≤
      Dfamily (interlaceFun f (Construction.qOne (firstExponent i) + 3))
        (bracketGE X Y (Construction.qOne (firstExponent i) + 3)
          (sourceFraction i) (9 / 25)) := by
  have hs : 1 ≤ scale i := (by norm_num : 1 ≤ 2 ^ 24).trans (scale_floor i)
  have ha : 1 ≤ firstExponent i := by unfold firstExponent; nlinarith
  have hk : firstExponent i + 1 ≤ i.incomingDepth := by
    have := hi.2.2.1
    omega
  have h := (hf.classicalAmplification (firstExponent i + 1) (by omega) hk).1
  have ht := h.trans (min_le_left _ _)
  rw [show firstExponent i + 1 - 1 = firstExponent i by omega] at ht
  rw [Construction.qOne_add_three _ ha]
  simpa only [Nat.cast_add, Nat.cast_one, ← sourceFraction_eq_rpow,
    Nat.add_assoc] using ht

/-- The same local profile on restrictions retaining at least half the
columns. The target family is nonempty, so family-minimum monotonicity is
applied in its actual guarded form. -/
theorem local_capacity_half {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (f : X → Y → Bool) (i : Input)
    (hi : Accepted i) (hf : IsRobustAt f i.incomingDepth) :
    D f + firstExponent i + 1 ≤
      Dfamily (interlaceFun f (Construction.qOne (firstExponent i) + 3))
        (bracketGE X Y (Construction.qOne (firstExponent i) + 3)
          (sourceFraction i) (1 / 2)) := by
  classical
  have hb : (1 : ℝ) ≤ bins i := by exact_mod_cast bins_pos i
  have hx : sourceFraction i ≤ 1 :=
    (sourceFraction_le i hi).trans ((div_le_one (by positivity)).mpr (by linarith))
  refine (local_capacity f i hi hf).trans ?_
  exact Dfamily.anti_mono _
    (bracketGE.anti_mono_params _ (le_refl _) (by norm_num : (9 / 25 : ℝ) ≤ 1 / 2))
    (bracketGE.nonempty _ _ _ hx (by norm_num) Fintype.card_pos)

end EthInapproximability.CurrentPaper.ProtectedGraphProfile
