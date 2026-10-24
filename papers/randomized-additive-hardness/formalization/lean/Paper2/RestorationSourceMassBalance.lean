import Paper2.RestorationRowPartition
import Paper2.ReferenceInitial

/-!
# Actual deleted and outgoing population mass

Frozen v12 Section 5, lines 450--469. Missing rows at a physical destination
are either originally deleted or originally retained and routed elsewhere.
The source mixture then gives the exact identity used to force protected
mass to leave each owner. No outgoing-mass identity is assumed.
-/

namespace Paper2.RestorationSourceMassBalance

open ReferenceCertificateTree ReferenceCertificateProtocol SourceMatrix SourceLaws
open scoped BigOperators

variable {A C I W Z : Type*} [Fintype W] [Fintype Z]

theorem missing_eq_deleted_add_outgoing (μ : FiniteLaw W) (input : I → W → A)
    (floor : ℕ → ℝ) (d fuel : ℕ) (s : State A C I W)
    (ν : FiniteLaw Z) (embed : Z → A)
    (v : (run μ input floor d fuel s).Leaves) :
    1 - ν.prob (fun z => embed z ∈ ((run μ input floor d fuel s).state v).rows) =
      ν.prob (fun z => embed z ∉ s.rows) +
      ν.prob (fun z => embed z ∈ s.rows ∧
        destination μ input floor d fuel s (embed z) ≠ v) := by
  classical
  rw [← SourceProjectionRetention.probability_complement]
  unfold FiniteLaw.prob
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hr : embed z ∈ s.rows
  · have hm := rows_iff_destination μ input floor d fuel s (embed z) hr v
    by_cases hv : destination μ input floor d fuel s (embed z) = v
    · have hrow := hm.mpr hv.symm
      simp [hr, hv, hrow]
    · have hrow : embed z ∉ ((run μ input floor d fuel s).state v).rows :=
        fun h => hv (hm.mp h).symm
      simp [hr, hv, hrow]
  · have hrow : embed z ∉ ((run μ input floor d fuel s).state v).rows :=
      fun h => hr (ReferenceRunCorrectness.rows_subset μ input floor d fuel s v h)
    simp [hr, hrow]

section Source

variable {Y : Type*} [Fintype Y] {q₁ q₂ t w : ℕ} [NeZero q₂]

/-- Initial protected deletion in units of one source copy. -/
noncomputable def protectedDeleted (ν : PositiveRationalLaw Y)
    (R0 : Set (Fin w × TaggedColumn q₁ q₂ t Y)) (i : Fin w) : ℝ :=
  (1 / 256 : ℝ) * (fixedTailLaw ν q₁ q₂ t).toFiniteLaw.prob
    (fun z => (i, .fixedTail z) ∉ R0) +
  (1 / 256 : ℝ) * (outerLaw ν q₁ q₂ t).toFiniteLaw.prob
    (fun z => (i, .diagonal z) ∉ R0)

theorem protectedDeleted_nonneg (ν : PositiveRationalLaw Y)
    (R0 : Set (Fin w × TaggedColumn q₁ q₂ t Y)) (i : Fin w) :
    0 ≤ protectedDeleted ν R0 i := by
  unfold protectedDeleted
  exact add_nonneg (mul_nonneg (by norm_num) (FiniteLaw.prob_nonneg _ _))
    (mul_nonneg (by norm_num) (FiniteLaw.prob_nonneg _ _))

/-- All initially deleted protected populations are paid once by the
original retained-row mass bound, even before owners are selected. -/
theorem total_protected_deleted_le (ν : PositiveRationalLaw Y) (hw : 0 < w)
    (R0 : Set (Fin w × TaggedColumn q₁ q₂ t Y)) (eta : ℝ)
    (hR : 1 - eta / (16 * w) ≤
      (ReferenceInitial.firstRowLaw ν hw).prob (· ∈ R0)) :
    (∑ i : Fin w, protectedDeleted ν R0 i) ≤ eta / 16 := by
  have hcomp : (ReferenceInitial.firstRowLaw ν hw).prob (fun z => z ∉ R0) ≤
      eta / (16 * w) := by
    rw [SourceProjectionRetention.probability_complement]
    linarith
  rw [ReferenceInitial.firstRowLaw_prob ν hw (fun i Z => (i, Z) ∉ R0)] at hcomp
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hsum : (∑ i : Fin w, (taggedLaw ν q₁ q₂ t).toFiniteLaw.prob
      (fun Z => (i, Z) ∉ R0)) ≤ eta / 16 := by
    apply (div_le_div_iff_of_pos_right hwR).mp
    convert hcomp using 1; ring
  apply le_trans _ hsum
  apply Finset.sum_le_sum
  intro i _
  rw [tagged_prob]
  have hn := (rawLaw ν q₁ q₂ t).toFiniteLaw.prob_nonneg
    (fun Z => (i, .unrestricted Z) ∉ R0)
  dsimp only [protectedDeleted]
  linarith

/-- The literal mixture identity at any physical destination. The last
two probabilities are the outgoing protected populations; the first
protected term records their initial deletion. -/
theorem owner_missing_identity
    (μ : FiniteLaw W) (input : I → W → (Fin w × TaggedColumn q₁ q₂ t Y))
    (floor : ℕ → ℝ) (d fuel : ℕ)
    (s : State (Fin w × TaggedColumn q₁ q₂ t Y) C I W)
    (ν : PositiveRationalLaw Y)
    (v : (run μ input floor d fuel s).Leaves) (i : Fin w) :
    1 - (taggedLaw ν q₁ q₂ t).toFiniteLaw.prob
      (fun Z => (i, Z) ∈ ((run μ input floor d fuel s).state v).rows) =
      (127 / 128 : ℝ) * (1 - (rawLaw ν q₁ q₂ t).toFiniteLaw.prob
        (fun Z => (i, .unrestricted Z) ∈ ((run μ input floor d fuel s).state v).rows)) +
      protectedDeleted ν s.rows i +
      (1 / 256 : ℝ) * (fixedTailLaw ν q₁ q₂ t).toFiniteLaw.prob
        (fun Z => (i, .fixedTail Z) ∈ s.rows ∧
          destination μ input floor d fuel s (i, .fixedTail Z) ≠ v) +
      (1 / 256 : ℝ) * (outerLaw ν q₁ q₂ t).toFiniteLaw.prob
        (fun Z => (i, .diagonal Z) ∈ s.rows ∧
          destination μ input floor d fuel s (i, .diagonal Z) ≠ v) := by
  have hf := missing_eq_deleted_add_outgoing μ input floor d fuel s
    (fixedTailLaw ν q₁ q₂ t).toFiniteLaw (fun Z => (i, .fixedTail Z)) v
  have hd := missing_eq_deleted_add_outgoing μ input floor d fuel s
    (outerLaw ν q₁ q₂ t).toFiniteLaw (fun Z => (i, .diagonal Z)) v
  rw [tagged_prob]
  dsimp only [protectedDeleted]
  linarith

end Source

end Paper2.RestorationSourceMassBalance

#print axioms Paper2.RestorationSourceMassBalance.missing_eq_deleted_add_outgoing
#print axioms Paper2.RestorationSourceMassBalance.total_protected_deleted_le
#print axioms Paper2.RestorationSourceMassBalance.owner_missing_identity
