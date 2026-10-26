import Paper2.RestorationOwnerEscape
import Paper2.RestorationRowPartition
import Paper2.ForeignOwnerMass

/-!
# Partition of actual protected outgoing mass

Frozen v12 Section 5, lines 467--484. Both original protected populations
are counted with their actual mixture coefficients. The partition uses the
physical destination of each original row, not a presumed receipt budget.
This module alone proves neither the incoming bound nor the final sum bound.
-/

namespace Paper2.ProtectedMassPartition

open ReferenceCertificateTree SourceMatrix SourceProfileParameters
open scoped BigOperators

local instance (L : ℕ) : NeZero (outerWidth L) := ⟨by
  unfold outerWidth
  positivity⟩

/-- One original donor's outgoing protected mass is the disjoint sum of
its receipt at other owners and at physical nonowner destinations. -/
theorem protected_outgoing_partition
    {B I W Y : Type*} [Fintype W] [Fintype Y]
    (L w : ℕ) (μ : FiniteLaw W)
    (input : I → W → Fin w × TaggedColumn (width L - 2) (outerWidth L) (width L) Y)
    (floor : ℕ → ℝ) (d fuel : ℕ)
    (st : State (Fin w × TaggedColumn (width L - 2) (outerWidth L) (width L) Y) B I W)
    (ν : PositiveRationalLaw Y)
    (O : Finset (run μ input floor d fuel st).Leaves)
    (owner : (run μ input floor d fuel st).Leaves) (howner : owner ∈ O)
    (i : Fin w) :
    RestorationOwnerEscape.protectedOutgoing μ input floor d fuel st ν owner i =
      (∑ v ∈ O.erase owner, ForeignOwnerMass.protectedMass ν L w i
        ((run μ input floor d fuel st).state v).rows) +
      (∑ v ∈ Finset.univ \ O, ForeignOwnerMass.protectedMass ν L w i
        ((run μ input floor d fuel st).state v).rows) := by
  classical
  have hf := RestorationRowPartition.outgoing_owner_partition
    μ input floor d fuel st
    (SourceLaws.fixedTailLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw
    (fun Z => (i, TaggedColumn.fixedTail Z)) O owner howner
  have hd := RestorationRowPartition.outgoing_owner_partition
    μ input floor d fuel st
    (SourceLaws.outerLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw
    (fun Z => (i, TaggedColumn.diagonal Z)) O owner howner
  unfold RestorationOwnerEscape.protectedOutgoing
  rw [hf, hd]
  simp only [ForeignOwnerMass.protectedMass, Finset.mul_sum, Finset.sum_add_distrib,
    mul_add]
  ring

/-- Summing the exact one-donor partitions retains the same physical
owner set and the actual chosen source labels. No injectivity is needed
for this identity; later upper bounds must establish it separately. -/
theorem total_protected_outgoing_partition
    {B I W Y : Type*} [Fintype W] [Fintype Y]
    (L w : ℕ) (μ : FiniteLaw W)
    (input : I → W → Fin w × TaggedColumn (width L - 2) (outerWidth L) (width L) Y)
    (floor : ℕ → ℝ) (d fuel : ℕ)
    (st : State (Fin w × TaggedColumn (width L - 2) (outerWidth L) (width L) Y) B I W)
    (ν : PositiveRationalLaw Y)
    (O : Finset (run μ input floor d fuel st).Leaves)
    (origin : O → Fin w) :
    (∑ u : O, RestorationOwnerEscape.protectedOutgoing
      μ input floor d fuel st ν u.val (origin u)) =
      (∑ u : O, ∑ v ∈ O.erase u.val, ForeignOwnerMass.protectedMass ν L w
        (origin u) ((run μ input floor d fuel st).state v).rows) +
      (∑ u : O, ∑ v ∈ Finset.univ \ O, ForeignOwnerMass.protectedMass ν L w
        (origin u) ((run μ input floor d fuel st).state v).rows) := by
  classical
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  exact protected_outgoing_partition L w μ input floor d fuel st ν O u.val u.property (origin u)

end Paper2.ProtectedMassPartition

#print axioms Paper2.ProtectedMassPartition.protected_outgoing_partition
#print axioms Paper2.ProtectedMassPartition.total_protected_outgoing_partition
