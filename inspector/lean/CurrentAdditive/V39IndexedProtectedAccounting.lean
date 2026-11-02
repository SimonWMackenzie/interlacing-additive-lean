import CurrentAdditive.V38IndexedTwoTag
import CurrentAdditive.V39ProtectedAccounting
import Paper2.RestorationRowPartition

/-! Actual two-family protected mass at a deterministic Alice frontier.
All events use the original laws. No probability is reassigned after a row
has survived or reached a particular destination. -/

namespace CurrentAdditive.V39IndexedProtectedAccounting

open Paper2 Paper2.SourceMatrix
open scoped BigOperators

variable {X Y I T : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I]
  {q₁ q₂ s w : ℕ} [NeZero q₁] [NeZero s] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : CurrentAdditive.DeterministicIndexedMatrix.Sources
    (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

variable {D : Type*} [Fintype D]


noncomputable def referenceLoss
    (keep : V38IndexedTwoTag.Column src → Prop)
    (dest : V38IndexedTwoTag.Column src → D) (own : D) : ℝ :=
  1 - (CurrentAdditive.DeterministicIndexedMatrix.Sources.ordinaryLaw src).toFiniteLaw.prob
    (fun Z => keep (.inl Z) ∧ dest (.inl Z) = own)

noncomputable def protectedDeleted
    (keep : V38IndexedTwoTag.Column src → Prop) : ℝ :=
  (1/256 : ℝ) * (CurrentAdditive.DeterministicIndexedMatrix.Sources.diagonalLaw src).toFiniteLaw.prob
    (fun j => ¬ keep (.inr j))

noncomputable def protectedOutgoing
    (keep : V38IndexedTwoTag.Column src → Prop)
    (dest : V38IndexedTwoTag.Column src → D) (own : D) : ℝ :=
  (1/256 : ℝ) * (CurrentAdditive.DeterministicIndexedMatrix.Sources.diagonalLaw src).toFiniteLaw.prob
    (fun j => keep (.inr j) ∧ dest (.inr j) ≠ own)

private theorem three_way_probability {Z : Type*} [Fintype Z]
    (μ : FiniteLaw Z) (keep : Z → Prop) (dest : Z → D) (own : D) :
    μ.prob (fun z => keep z ∧ dest z = own) + μ.prob (fun z => ¬ keep z) +
      μ.prob (fun z => keep z ∧ dest z ≠ own) = 1 := by
  classical
  unfold FiniteLaw.prob
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  calc
    _ = ∑ z, μ.weight z := by
      apply Finset.sum_congr rfl
      intro z _
      by_cases hk : keep z <;> by_cases hd : dest z = own <;> simp [hk,hd]
    _ = 1 := μ.total

/-- Reference loss, initially deleted protected mass, and surviving
protected rows sent elsewhere partition the missing part of this copy. -/
theorem missing_copy_identity
    (keep : V38IndexedTwoTag.Column src → Prop)
    (dest : V38IndexedTwoTag.Column src → D) (own : D) :
    (255/256 : ℝ) * referenceLoss src keep dest own +
      protectedDeleted src keep + protectedOutgoing src keep dest own =
      1 - (V38IndexedTwoTag.law src).toFiniteLaw.prob
        (fun Z => keep Z ∧ dest Z = own) := by
  rw [V38IndexedTwoTag.prob_split]
  have hp := three_way_probability
    (CurrentAdditive.DeterministicIndexedMatrix.Sources.diagonalLaw src).toFiniteLaw
    (fun j => keep (.inr j)) (fun j => dest (.inr j)) own
  unfold referenceLoss protectedDeleted protectedOutgoing
  simp only [CurrentAdditive.DeterministicIndexedMatrix.Sources.ordinaryLaw, CurrentAdditive.DeterministicIndexedMatrix.Sources.diagonalLaw] at *
  linarith

/-- Every surviving protected input outside its owner has exactly one
other-owner or nonowner destination. This uses an actual total destination
function; the receiving partition is proved, not assumed. -/
theorem outgoing_partition [DecidableEq D]
    (keep : V38IndexedTwoTag.Column src → Prop)
    (dest : V38IndexedTwoTag.Column src → D)
    (owners : Finset D) (own : D) (ho : own ∈ owners) :
    protectedOutgoing src keep dest own =
      (∑ d ∈ owners.erase own, (1/256 : ℝ) *
        (CurrentAdditive.DeterministicIndexedMatrix.Sources.diagonalLaw src).toFiniteLaw.prob
          (fun j => keep (.inr j) ∧ dest (.inr j) = d)) +
      (∑ d ∈ Finset.univ \ owners, (1/256 : ℝ) *
        (CurrentAdditive.DeterministicIndexedMatrix.Sources.diagonalLaw src).toFiniteLaw.prob
          (fun j => keep (.inr j) ∧ dest (.inr j) = d)) := by
  classical
  unfold protectedOutgoing FiniteLaw.prob
  simp_rw [Finset.mul_sum]
  conv_rhs =>
    lhs
    rw [Finset.sum_comm]
  conv_rhs =>
    rhs
    rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hk : keep (.inr j)
  · by_cases hd : dest (.inr j) = own
    · simp [hk,hd,ho]
    · by_cases hm : dest (.inr j) ∈ owners <;> simp [hk,hd,hm]
  · simp [hk]


end CurrentAdditive.V39IndexedProtectedAccounting

#print axioms CurrentAdditive.V39IndexedProtectedAccounting.missing_copy_identity
#print axioms CurrentAdditive.V39IndexedProtectedAccounting.outgoing_partition
