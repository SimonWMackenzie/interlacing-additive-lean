import Paper2.ReferenceOwners
import Paper2.ReferenceSchedule

/-!
# Original reference loss along unsplit owner paths

Frozen Paper 2 v12, `sections/05-restoration.tex`, lines 388--399,
`eq:reference-loss`. The same ambient reference law is used throughout.
Loss is derived by following the actual query fibres. The later source
specialization must still supply the initial deletion and numerical margin.
-/

namespace Paper2.ReferenceOwnerLoss

open ReferenceCertificateTree ReferenceCertificates ReferenceOwners SourceSupportStep
open scoped BigOperators

variable {A C I W : Type*} [Fintype W]

theorem run_unsplit_loss (μ : FiniteLaw W) (input : I → W → A)
    (floor : ℕ → ℝ) (hhalf : ∀ d, floor d = 2 * floor (d + 1))
    (d fuel : ℕ) (s : State A C I W) :
    ∀ v : (run μ input floor d fuel s).Leaves,
      ∀ i ∈ ((run μ input floor d fuel s).state v).family.unsplit,
        mass μ (s.family.support i) -
          mass μ (((run μ input floor d fuel s).state v).family.support i) ≤
            floor d - floor (d + ((run μ input floor d fuel s).route v).length) := by
  apply run_invariant μ input floor
    (fun depth t => ∀ i ∈ t.family.unsplit,
      mass μ (s.family.support i) - mass μ (t.family.support i) ≤ floor d - floor depth)
    _ d fuel s (by intro i _; simp)
  intro depth t query left right _ ht b i hi
  have hip : i ∈ t.family.unsplit :=
    ReferenceCertificates.child_unsplit_subset μ t.family
      (fun i w => query (input i w)) (floor (depth + 1)) b hi
  have hp := ht i hip
  have hs := ReferenceCertificates.unsplit_loss μ t.family
    (fun i w => query (input i w)) (floor (depth + 1)) b i hi
  change mass μ (s.family.support i) -
    mass μ ((ReferenceCertificates.child μ t.family
      (fun i w => query (input i w)) (floor (depth + 1)) b).support i) ≤ _
  linarith [hhalf depth]

theorem final_unsplit_loss (μ : FiniteLaw W) (input : I → W → A)
    (w r : ℕ) (x : ℝ) (hw : w = 2 ^ r) (s : State A C I W)
    (v : (run μ input (ReferenceSchedule.floor w x) 0 r s).Leaves)
    (hfinal : ((run μ input (ReferenceSchedule.floor w x) 0 r s).route v).length = r)
    (i : I) (hi : i ∈ ((run μ input (ReferenceSchedule.floor w x) 0 r s).state v).family.unsplit) :
    mass μ (s.family.support i) -
      mass μ (((run μ input (ReferenceSchedule.floor w x) 0 r s).state v).family.support i) ≤
        2 * ((w : ℝ) - 1) * x := by
  have h := run_unsplit_loss μ input (ReferenceSchedule.floor w x)
    (ReferenceSchedule.floor_half w x) 0 r s v i hi
  rw [Nat.zero_add, hfinal, ReferenceSchedule.floor_zero,
    ReferenceSchedule.floor_dyadic x hw (le_refl r)] at h
  simp only [Nat.sub_self, pow_zero, mul_one] at h
  linarith

/-- Distinct original coordinates prevent repeated charging of initial
deletion when losses are summed over physical owner positions. -/
theorem sum_defects_le {J : Type*} [Fintype I] [Fintype J]
    (μ : FiniteLaw W) (initial : I → Finset W) (retained : J → Finset W)
    (origin : J → I) (hinj : Function.Injective origin) (L : ℝ)
    (hloss : ∀ j, mass μ (initial (origin j)) - mass μ (retained j) ≤ L) :
    (∑ j, (1 - mass μ (retained j))) ≤
      (∑ i, (1 - mass μ (initial i))) + Fintype.card J * L := by
  classical
  have hnonneg (i : I) : 0 ≤ 1 - mass μ (initial i) := by
    have h := μ.prob_le_one (fun z => z ∈ initial i)
    exact sub_nonneg.mpr h
  have himage : (∑ j : J, (1 - mass μ (initial (origin j)))) ≤
      ∑ i : I, (1 - mass μ (initial i)) := by
    calc
      _ = ∑ i ∈ Finset.univ.image origin, (1 - mass μ (initial i)) := by
        rw [Finset.sum_image]
        intro a _ b _ he
        exact hinj he
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ => hnonneg i)
  calc
    _ ≤ ∑ j : J, ((1 - mass μ (initial (origin j))) + L) := by
      apply Finset.sum_le_sum
      intro j _
      linarith [hloss j]
    _ = (∑ j : J, (1 - mass μ (initial (origin j)))) + Fintype.card J * L := by
      simp [Finset.sum_add_distrib]
    _ ≤ _ := by linarith

theorem run_owner_defects [Fintype I]
    (μ : FiniteLaw W) (input : I → W → A)
    (w r : ℕ) (x : ℝ) (hw : w = 2 ^ r) (s : State A C I W) :
    let T := run μ input (ReferenceSchedule.floor w x) 0 r s
    let F := fun v : T.Leaves => (T.state v).family
    let final := fun v : T.Leaves => (T.route v).length = r
    let Owners := {v : T.Leaves // v ∈ ownerNodes F final}
    (∑ v : Owners, (1 - mass μ ((T.state v.val).family.support (origin F final v)))) ≤
      (∑ i : I, (1 - mass μ (s.family.support i))) +
        Fintype.card Owners * (2 * ((w : ℝ) - 1) * x) := by
  dsimp only
  apply sum_defects_le μ _ _ _
    (run_origin_injective μ input (ReferenceSchedule.floor w x) r s)
  intro v
  apply final_unsplit_loss μ input w r x hw s v.val
  · exact ((mem_ownerNodes _ _ _).mp v.property).1
  · exact origin_mem _ _ v

end Paper2.ReferenceOwnerLoss

#print axioms Paper2.ReferenceOwnerLoss.run_unsplit_loss
#print axioms Paper2.ReferenceOwnerLoss.final_unsplit_loss
#print axioms Paper2.ReferenceOwnerLoss.sum_defects_le
#print axioms Paper2.ReferenceOwnerLoss.run_owner_defects
