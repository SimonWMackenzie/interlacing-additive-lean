import Paper2.ReferenceRunCorrectness
import Paper2.ReferenceTerminalCapacity
import Paper2.ReferenceSchedule
import Paper2.ReferenceSourceInitial

/-!
# The original unpadded protocol cannot stop on a live reference

This runner starts from the ambient extension of the original restricted
protocol, with no Alice padding. The conclusion concerns every physical leaf
of that original runner, not a structurally padded surrogate.
-/

namespace Paper2.ReferenceOriginalLeaves

open Workspace.Types.Protocol ReferenceCertificateTree ReferenceCertificates
open Paper2.SourceSupportFrontier

variable {A K Rw : Type*} [Fintype A] [Fintype K] [Fintype Rw] {w : ℕ}

theorem unpadded_run_leaf_active_empty
    (μ : PositiveRationalLaw A) (ν : PositiveRationalLaw K)
    (F : A → K → Bool) (M : Rw → (Fin w → K) → Bool)
    (input : Fin w → A → Rw) (O : Set (Fin w → K))
    (s : State Rw (Fin w → K) (Fin w) A)
    (E0 : Finset (Fin w)) (r H : ℕ) (x eta : ℝ)
    (hw : w = 2 ^ r) (hH : 1 ≤ H) (hx : 0 < x) (heta : eta < 2 / 5)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (hsingle : ∀ S : Finset (Fin w), S.card = 1 → Disjoint S E0 →
      1 - eta ≤ ProductProjections.projectionMass
        (fun _ => ν.toFiniteLaw) (· ∈ O) S)
    (hactive : s.family.active = Finset.univ \ E0)
    (hreach : ∀ i ∈ s.family.active, ∀ a ∈ s.family.support i,
      input i a ∈ s.rows)
    (hfloor : ∀ i ∈ s.family.active,
      ReferenceSchedule.floor w x 0 ≤
        SourceSupportStep.mass μ.toFiniteLaw (s.family.support i))
    (hcompute : ∀ row ∈ s.rows, ∀ y ∈ O, s.protocol.eval row y = M row y)
    (hentry : ∀ i a, input i a ∈ s.rows → ∀ y ∈ O,
      M (input i a) y = F a (y i)) :
    ∀ v : (run μ.toFiniteLaw input (ReferenceSchedule.floor w x) 0 r s).Leaves,
      ((run μ.toFiniteLaw input (ReferenceSchedule.floor w x) 0 r s).state v).protocol.cost = 0 →
      ((run μ.toFiniteLaw input (ReferenceSchedule.floor w x) 0 r s).state v).family.active = ∅ := by
  classical
  let floor := ReferenceSchedule.floor w x
  let T := run μ.toFiniteLaw input floor 0 r s
  have hrunFloor := run_floor μ.toFiniteLaw input floor
    (ReferenceSchedule.floor_half w x) 0 r s hfloor
  have hrunReach := run_reaches μ.toFiniteLaw input floor 0 r s hreach
  have hrunSets := run_sets_subset μ.toFiniteLaw input floor 0 r s
  intro v hleaf
  ext i
  simp
  intro hi
  let node := T.state v
  have hdepth := ReferenceRunCorrectness.depth_le μ.toFiniteLaw input floor 0 r s v
  have hnodeavoid : Disjoint node.family.active E0 := by
    apply Finset.disjoint_left.mpr
    intro j hj hjE
    have hj0 := (hrunSets v).1 hj
    rw [hactive] at hj0
    exact (Finset.mem_sdiff.mp hj0).2 hjE
  have hgood : 1 - eta ≤ ProductProjections.projectionMass
      (fun _ => ν.toFiniteLaw) (· ∈ O) ({i} : Finset (Fin w)) := by
    apply hsingle
    · simp
    · exact Finset.disjoint_left.mpr (by
        intro j hj hjE
        have : j = i := Finset.mem_singleton.mp hj
        subst j
        exact (Finset.disjoint_left.mp hnodeavoid hi) hjE)
  have hnodefloor : ∀ j ∈ node.family.active,
      x ≤ μ.toFiniteLaw.prob (· ∈ (node.family.support j : Set A)) := by
    intro j hj
    have hf := hrunFloor v j hj
    have heq : floor ((T.route v).length) =
        2 * (2 : ℝ) ^ (r - (T.route v).length) * x :=
      ReferenceSchedule.floor_dyadic x hw hdepth
    have hf' : 2 * (2 : ℝ) ^ (r - (T.route v).length) * x ≤
        μ.toFiniteLaw.prob (· ∈ (node.family.support j : Set A)) := by
      simpa only [Nat.zero_add, ← heq, SourceSupportStep.mass] using hf
    have hp : (1 : ℝ) ≤ 2 ^ (r - (T.route v).length) := by
      exact one_le_pow₀ (by norm_num)
    have hm := mul_le_mul_of_nonneg_right hp (le_of_lt hx)
    nlinarith [hf', hm]
  have hnodeentry : ∀ j a, input j a ∈ node.rows → ∀ y ∈ O,
      M (input j a) y = F a (y j) := by
    intro j a ha y hy
    exact hentry j a
      (ReferenceRunCorrectness.rows_subset μ.toFiniteLaw input floor 0 r s v ha)
      y hy
  have hnodecompute := ReferenceRunCorrectness.computes_on_original_rectangle
    μ.toFiniteLaw input floor 0 r s M O hcompute v
  exact ReferenceTerminalCapacity.original_early_leaf_impossible
    μ ν F M input node.rows O node.protocol hnodecompute hnodeentry
    node.family i hi H x eta hH heta hnodefloor (hrunReach v) hgood
    hprofile hleaf

end Paper2.ReferenceOriginalLeaves

#print axioms Paper2.ReferenceOriginalLeaves.unpadded_run_leaf_active_empty
