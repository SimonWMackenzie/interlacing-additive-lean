import CurrentAdditive.IndexedIncomingDensity
import Paper2.RestorationSourceMassBalance

/-! Protected-mass bookkeeping on the original indexed tagged columns of W.
Every destination is a physical leaf of the same Alice-only run. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.ReferenceCertificateTree Paper2.ReferenceCertificateProtocol
  Paper2.RestorationSourceMassBalance
open scoped BigOperators

variable {X Y : Type*} [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s w : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

noncomputable def protectedDeleted
    (R₀ : Set (Fin w × Column src)) (i : Fin w) : ℝ :=
  (1/256 : ℝ) * src.outer.law.toFiniteLaw.prob
      (fun z => (i,Column.fixedTail z) ∉ R₀) +
    (1/256 : ℝ) * (diagonalLaw src).toFiniteLaw.prob
      (fun z => (i,Column.diagonal z) ∉ R₀)

noncomputable def ordinaryInitialLoss
    (R₀ : Set (Fin w × Column src)) (i : Fin w) : ℝ :=
  1 - (ordinaryLaw src).toFiniteLaw.prob
    (fun z => (i,Column.ordinary z) ∈ R₀)

theorem indexed_column_prob_by_copy [NeZero w]
    (E : Fin w → Column src → Prop) :
    (((PositiveRationalLaw.uniform (Fin w)).prod
      (columnLaw src)).toFiniteLaw).prob (fun z => E z.1 z.2) =
      (∑ i : Fin w, (columnLaw src).toFiniteLaw.prob (E i)) / w := by
  rw [PositiveRationalLaw.toFiniteLaw_prod, FiniteLaw.prod_prob]
  simp only [PositiveRationalLaw.toFiniteLaw, PositiveRationalLaw.uniform,
    Fintype.card_fin, Rat.cast_inv, Rat.cast_natCast]
  rw [← Finset.mul_sum]
  ring

theorem protectedDeleted_le_missing
    (R₀ : Set (Fin w × Column src)) (i : Fin w) :
    protectedDeleted src R₀ i ≤
      (columnLaw src).toFiniteLaw.prob (fun z => (i,z) ∉ R₀) := by
  have hs := column_prob_split src (fun z => (i,z) ∉ R₀)
  have ho := (ordinaryLaw src).toFiniteLaw.prob_nonneg
    (fun z => (i,Column.ordinary z) ∉ R₀)
  change (columnLaw src).toFiniteLaw.prob (fun z => (i,z) ∉ R₀) =
    (127/128 : ℝ) * (ordinaryLaw src).toFiniteLaw.prob
      (fun z => (i,Column.ordinary z) ∉ R₀) +
    (1/256 : ℝ) * src.outer.law.toFiniteLaw.prob
      (fun z => (i,Column.fixedTail z) ∉ R₀) +
    (1/256 : ℝ) * (diagonalLaw src).toFiniteLaw.prob
      (fun z => (i,Column.diagonal z) ∉ R₀) at hs
  unfold protectedDeleted
  linarith

theorem total_protectedDeleted_le [NeZero w]
    (R₀ : Set (Fin w × Column src)) (δ : ℝ)
    (hR : 1-δ ≤ (((PositiveRationalLaw.uniform (Fin w)).prod
      (columnLaw src)).toFiniteLaw).prob (· ∈ R₀)) :
    (∑ i : Fin w, protectedDeleted src R₀ i) ≤ (w : ℝ)*δ := by
  let ν := ((PositiveRationalLaw.uniform (Fin w)).prod
    (columnLaw src)).toFiniteLaw
  have hcomp : ν.prob (· ∉ R₀) ≤ δ := by
    rw [Paper2.SourceProjectionRetention.probability_complement]
    exact sub_le_iff_le_add'.2 (by dsimp [ν] at *; linarith)
  have hsum : (∑ i : Fin w,
      (columnLaw src).toFiniteLaw.prob (fun z => (i,z) ∉ R₀)) /
        (w : ℝ) ≤ δ := by
    have hp := indexed_column_prob_by_copy src
      (fun i z => (i,z) ∉ R₀)
    change ν.prob (fun z => (z.1,z.2) ∉ R₀) ≤ δ at hcomp
    rw [show ν.prob (fun z => (z.1,z.2) ∉ R₀) = _ from hp] at hcomp
    exact hcomp
  have hsum' : (∑ i : Fin w,
      (columnLaw src).toFiniteLaw.prob (fun z => (i,z) ∉ R₀)) ≤
        (w : ℝ)*δ := by
    have hw : (0 : ℝ) < w := by exact_mod_cast NeZero.pos w
    simpa only [mul_comm] using (div_le_iff₀ hw).mp hsum
  exact (Finset.sum_le_sum (fun i _ => protectedDeleted_le_missing src R₀ i)).trans hsum'

theorem ordinaryInitialLoss_le_missing
    (R₀ : Set (Fin w × Column src)) (i : Fin w) :
    (127/128 : ℝ) * ordinaryInitialLoss src R₀ i ≤
      (columnLaw src).toFiniteLaw.prob (fun z => (i,z) ∉ R₀) := by
  have hs := column_prob_split src (fun z => (i,z) ∉ R₀)
  have hf := src.outer.law.toFiniteLaw.prob_nonneg
    (fun z => (i,Column.fixedTail z) ∉ R₀)
  have hd := (diagonalLaw src).toFiniteLaw.prob_nonneg
    (fun z => (i,Column.diagonal z) ∉ R₀)
  have hc := Paper2.SourceProjectionRetention.probability_complement
    (ordinaryLaw src).toFiniteLaw
    (fun z => (i,Column.ordinary z) ∈ R₀)
  change (ordinaryLaw src).toFiniteLaw.prob
    (fun z => (i,Column.ordinary z) ∉ R₀) = _ at hc
  change (columnLaw src).toFiniteLaw.prob (fun z => (i,z) ∉ R₀) =
    (127/128 : ℝ) * (ordinaryLaw src).toFiniteLaw.prob
      (fun z => (i,Column.ordinary z) ∉ R₀) +
    (1/256 : ℝ) * src.outer.law.toFiniteLaw.prob
      (fun z => (i,Column.fixedTail z) ∉ R₀) +
    (1/256 : ℝ) * (diagonalLaw src).toFiniteLaw.prob
      (fun z => (i,Column.diagonal z) ∉ R₀) at hs
  unfold ordinaryInitialLoss
  linarith

theorem total_ordinaryInitialLoss_le [NeZero w]
    (R₀ : Set (Fin w × Column src)) (δ : ℝ)
    (hR : 1-δ ≤ (((PositiveRationalLaw.uniform (Fin w)).prod
      (columnLaw src)).toFiniteLaw).prob (· ∈ R₀)) :
    (127/128 : ℝ) *
      (∑ i : Fin w, ordinaryInitialLoss src R₀ i) ≤ (w : ℝ)*δ := by
  have hcomp : (((PositiveRationalLaw.uniform (Fin w)).prod
      (columnLaw src)).toFiniteLaw).prob (· ∉ R₀) ≤ δ := by
    rw [Paper2.SourceProjectionRetention.probability_complement]
    linarith
  have hsum : (∑ i : Fin w,
      (columnLaw src).toFiniteLaw.prob (fun z => (i,z) ∉ R₀)) /
        (w : ℝ) ≤ δ := by
    rw [indexed_column_prob_by_copy src (fun i z => (i,z) ∉ R₀)] at hcomp
    exact hcomp
  have hw : (0 : ℝ) < w := by exact_mod_cast NeZero.pos w
  have hsum' : (∑ i : Fin w,
      (columnLaw src).toFiniteLaw.prob (fun z => (i,z) ∉ R₀)) ≤
        (w : ℝ)*δ := by simpa only [mul_comm] using (div_le_iff₀ hw).mp hsum
  calc
    _ = ∑ i : Fin w, (127/128 : ℝ) * ordinaryInitialLoss src R₀ i := by
      rw [Finset.mul_sum]
    _ ≤ ∑ i : Fin w,
      (columnLaw src).toFiniteLaw.prob (fun z => (i,z) ∉ R₀) :=
        Finset.sum_le_sum (fun i _ => ordinaryInitialLoss_le_missing src R₀ i)
    _ ≤ (w : ℝ)*δ := hsum'

noncomputable def protectedOutgoing
    {C I Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (input : I → Ω → Fin w × Column src)
    (floor : ℕ → ℝ) (depth fuel : ℕ)
    (state : State (Fin w × Column src) C I Ω)
    (v : (run μ input floor depth fuel state).Leaves)
    (i : Fin w) : ℝ :=
  (1/256 : ℝ) * src.outer.law.toFiniteLaw.prob
      (fun z => (i,Column.fixedTail z) ∈ state.rows ∧
        destination μ input floor depth fuel state
          (i,Column.fixedTail z) ≠ v) +
    (1/256 : ℝ) * (diagonalLaw src).toFiniteLaw.prob
      (fun z => (i,Column.diagonal z) ∈ state.rows ∧
        destination μ input floor depth fuel state
          (i,Column.diagonal z) ≠ v)

theorem protected_missing_identity
    {C I Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (input : I → Ω → Fin w × Column src)
    (floor : ℕ → ℝ) (depth fuel : ℕ)
    (state : State (Fin w × Column src) C I Ω)
    (v : (run μ input floor depth fuel state).Leaves)
    (i : Fin w) :
    1 - (columnLaw src).toFiniteLaw.prob
      (fun z => (i,z) ∈
        ((run μ input floor depth fuel state).state v).rows) =
      (127/128 : ℝ) *
        (1 - (ordinaryLaw src).toFiniteLaw.prob
          (fun z => (i,Column.ordinary z) ∈
            ((run μ input floor depth fuel state).state v).rows)) +
      protectedDeleted src state.rows i +
      protectedOutgoing src μ input floor depth fuel state v i := by
  have hf := missing_eq_deleted_add_outgoing μ input floor depth fuel state
    src.outer.law.toFiniteLaw (fun z => (i,Column.fixedTail z)) v
  have hd := missing_eq_deleted_add_outgoing μ input floor depth fuel state
    (diagonalLaw src).toFiniteLaw (fun z => (i,Column.diagonal z)) v
  have hsplit := column_prob_split src
    (fun z => (i,z) ∈
      ((run μ input floor depth fuel state).state v).rows)
  change (columnLaw src).toFiniteLaw.prob
      (fun z => (i,z) ∈ ((run μ input floor depth fuel state).state v).rows) =
    (127/128 : ℝ) * (ordinaryLaw src).toFiniteLaw.prob
      (fun z => (i,Column.ordinary z) ∈
        ((run μ input floor depth fuel state).state v).rows) +
    (1/256 : ℝ) * src.outer.law.toFiniteLaw.prob
      (fun z => (i,Column.fixedTail z) ∈
        ((run μ input floor depth fuel state).state v).rows) +
    (1/256 : ℝ) * (diagonalLaw src).toFiniteLaw.prob
      (fun z => (i,Column.diagonal z) ∈
        ((run μ input floor depth fuel state).state v).rows) at hsplit
  dsimp only [protectedDeleted, protectedOutgoing]
  linarith

/-- One original donor's outgoing protected rows partition by their unique
physical destination: another owner or a nonowner node. -/
theorem protectedOutgoing_partition
    {C I Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (input : I → Ω → Fin w × Column src)
    (floor : ℕ → ℝ) (depth fuel : ℕ)
    (state : State (Fin w × Column src) C I Ω)
    (O : Finset (run μ input floor depth fuel state).Leaves)
    (owner : (run μ input floor depth fuel state).Leaves)
    (howner : owner ∈ O) (i : Fin w) :
    protectedOutgoing src μ input floor depth fuel state owner i =
      (∑ v ∈ O.erase owner,
        protectedReceipt src w
          ((run μ input floor depth fuel state).state v).rows i) +
      (∑ v ∈ Finset.univ \ O,
        protectedReceipt src w
          ((run μ input floor depth fuel state).state v).rows i) := by
  classical
  have hf := Paper2.RestorationRowPartition.outgoing_owner_partition
    μ input floor depth fuel state src.outer.law.toFiniteLaw
      (fun z => (i,Column.fixedTail z)) O owner howner
  have hd := Paper2.RestorationRowPartition.outgoing_owner_partition
    μ input floor depth fuel state (diagonalLaw src).toFiniteLaw
      (fun z => (i,Column.diagonal z)) O owner howner
  unfold protectedOutgoing protectedReceipt
  rw [hf, hd]
  simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add]
  ring

/-- Sum the same physical partition over a finite set of owners. -/
theorem total_protectedOutgoing_partition
    {C I Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (input : I → Ω → Fin w × Column src)
    (floor : ℕ → ℝ) (depth fuel : ℕ)
    (state : State (Fin w × Column src) C I Ω)
    (O : Finset (run μ input floor depth fuel state).Leaves)
    (origin : O → Fin w) :
    (∑ u : O, protectedOutgoing src μ input floor depth fuel state
      u.val (origin u)) =
      (∑ u : O, ∑ v ∈ O.erase u.val,
        protectedReceipt src w
          ((run μ input floor depth fuel state).state v).rows (origin u)) +
      (∑ u : O, ∑ v ∈ Finset.univ \ O,
        protectedReceipt src w
          ((run μ input floor depth fuel state).state v).rows (origin u)) := by
  classical
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  exact protectedOutgoing_partition src μ input floor depth fuel state
    O u.val u.property (origin u)

end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.protected_missing_identity
#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.total_protectedDeleted_le
#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.total_ordinaryInitialLoss_le
#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.total_protectedOutgoing_partition
