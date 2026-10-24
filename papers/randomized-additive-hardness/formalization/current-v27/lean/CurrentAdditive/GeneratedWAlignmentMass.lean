import CurrentAdditive.GeneratedWOwnerEscapeV2
import CurrentAdditive.GeneratedOwnerGoodSingleton
import Paper2.RestorationOutgoingMass
import Paper2.OwnerTransferReindex

/-! Appendix I: the physical protected populations of the generated W matrix
partition between other owners and nonowner destinations.  This file keeps the
actual indexed source law and the actual Alice-prefix run throughout. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.ReferenceCertificateTree Paper2.ReferenceOwners
  Paper2.RestorationOutgoingMass Paper2.OwnerTransferReindex
open scoped BigOperators

variable {G V Aux X Y : Type*}
  [Fintype G] [Fintype V] [Fintype Aux] [Fintype X] [Fintype Y]
  [DecidableEq G] [DecidableEq V] [DecidableEq Aux]
  [DecidableEq X] [DecidableEq Y]
  {q₁ q₂ s w : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

/-- On the literal tagged rows of W, local owner escape and local receipt
caps contradict each other.  The upper bounds are on individual physical
destinations; the partition, change of summation order, and scalar comparison
are proved here. -/
theorem indexed_run_mass_contradiction
    {B J Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (input : J → Ω → Fin w × Column src)
    (floor : ℕ → ℝ) (depth fuel : ℕ)
    (state : State (Fin w × Column src) B J Ω)
    (μI : PositiveRationalLaw (G × (V ⊕ Aux)))
    (streams : InternalStreams src μI w)
    (R : X → Y → Bool)
    (activity : G × (V ⊕ Aux) → Fin q₂ → Option (Fin s))
    (ξ₀ : Paper2.SourceMatrix.Tail s Y) (C : ℕ)
    (Yevent : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (O : Finset (run μ input floor depth fuel state).Leaves)
    (origin : O → Fin w)
    (η μweight Kstar : ℝ) (E : ℕ) (capacity :
      (run μ input floor depth fuel state).Leaves → ℕ)
    (δ : O → ℝ)
    (hη : 0 < η) (hw : 2 ≤ w) (hE : 4 * E ≤ w)
    (hcount : w - E ≤ O.card)
    (hinjective : Function.Injective origin)
    (hnear : ∀ (U : Set (Column src))
      (Vrows : Set (Row (I := G × (V ⊕ Aux)) src)),
      1-η ≤ (columnLaw src).toFiniteLaw.prob (· ∈ U) →
      1-η ≤ (rowLaw src μI).toFiniteLaw.prob (· ∈ Vrows) →
      C ≤ Paper2.Compression.restrictionD (N src R activity ξ₀) U Vrows)
    (hYpos : 0 < streams.law.toFiniteLaw.prob (· ∈ Yevent))
    (ε : ℝ) (hε : ε ≤ η/2)
    (hTV : ∀ u : O,
      CurrentAdditive.projectionTV
        (CurrentAdditive.condition streams.law.toFiniteLaw
          (· ∈ Yevent) hYpos)
        (rowLaw src μI).toFiniteLaw
        (InternalStreams.decode src streams)
        (Finset.univ.image (fun _ : Fin 1 => origin u)) ≤ ε)
    (hcost : ∀ u : O,
      Paper2.Compression.restrictionD (W src streams R activity ξ₀)
        Yevent ((run μ input floor depth fuel state).state u.val).rows < C)
    (hdefect : (Finset.univ.sum (fun u : ↥O =>
      1 - (ordinaryLaw src).toFiniteLaw.prob
        (fun z => (origin u, Column.ordinary z) ∈
          ((run μ input floor depth fuel state).state u.val).rows))) ≤
      η / (8 * (127/128 : ℝ)))
    (hdeleted : (Finset.univ.sum (fun u : ↥O =>
      protectedDeleted src state.rows (origin u))) ≤ η/16)
    (hpair : ∀ v u : O, u ≠ v →
      protectedReceipt src w
        ((run μ input floor depth fuel state).state v.val).rows (origin u) ≤
        2 * μweight * δ v)
    (hδpoint : ∀ v : O, 0 ≤ δ v)
    (hδ : 0 ≤ Finset.univ.sum (fun v : ↥O => δ v))
    (hμ : 0 ≤ μweight)
    (hpairScalar : 2 * μweight * w *
      (Finset.univ.sum (fun v : ↥O => δ v)) ≤
      3 * η * w / 32)
    (hremote : ∀ v ∈ Finset.univ \ O,
      (Finset.univ.sum (fun u : ↥O => protectedReceipt src w
        ((run μ input floor depth fuel state).state v).rows (origin u))) ≤
        Kstar * capacity v)
    (hK : 0 ≤ Kstar)
    (hcapacity : (∑ v ∈ Finset.univ \ O, capacity v) ≤ E)
    (hcapacityScalar : Kstar * E ≤ η * w / 16) : False := by
  classical
  let T := run μ input floor depth fuel state
  let i₀ : Fin w := ⟨0, by omega⟩
  have hout' : η * w / 2 <
      ∑ u ∈ O, protectedOutgoing src μ input floor depth fuel state
        u (if hu : u ∈ O then origin ⟨u,hu⟩ else i₀) := by
    apply outgoing_lower_of_owner_bounds O w E η
      (fun u : T.Leaves => protectedOutgoing src μ input floor depth fuel state
        u (if hu : u ∈ O then origin ⟨u,hu⟩ else i₀))
      (fun u : T.Leaves => 1 - (ordinaryLaw src).toFiniteLaw.prob
        (fun z => ((if hu : u ∈ O then origin ⟨u,hu⟩ else i₀),
          Column.ordinary z) ∈ (T.state u).rows))
      (fun u : T.Leaves => protectedDeleted src state.rows
        (if hu : u ∈ O then origin ⟨u,hu⟩ else i₀))
      hη hw hE hcount
    · intro u hu
      let uu : O := ⟨u,hu⟩
      have himage : 1-η/2 ≤ (rowLaw src μI).toFiniteLaw.prob
          (· ∈ (fun t => InternalStreams.decode src streams t (origin uu)) '' Yevent) := by
        have hloss := owner_singleton_loss_of_projectionTV src μI
          streams Yevent Yevent (Set.Subset.rfl) hYpos
          (origin uu) ε (hTV uu)
        have hcomp := Paper2.SourceProjectionRetention.probability_complement
          (rowLaw src μI).toFiniteLaw
          (· ∈ (fun t => InternalStreams.decode src streams t (origin uu)) '' Yevent)
        linarith
      have hlocal := indexed_owner_escape_of_good_singleton_image src μI
        streams R activity ξ₀ C η hη.le hnear μ input floor depth fuel
        state u (origin uu) Yevent himage (hcost uu)
      simpa [hu, uu] using hlocal
    · rw [← Finset.sum_coe_sort O]
      simpa [T] using hdefect
    · rw [← Finset.sum_coe_sort O]
      simpa using hdeleted
  have hout : η * w / 2 <
      Finset.univ.sum (fun u : ↥O =>
        protectedOutgoing src μ input floor depth fuel state
          u.val (origin u)) := by
    rw [← Finset.sum_coe_sort O] at hout'
    simpa using hout'
  have hpartition := total_protectedOutgoing_partition src μ input floor
    depth fuel state O origin
  have hreindex := owner_receipts_reindex O
    (fun u v => protectedReceipt src w (T.state v).rows (origin u))
  rw [hreindex] at hpartition
  have hcard : (O.card : ℝ) ≤ w := by
    have hc : Fintype.card O ≤ Fintype.card (Fin w) :=
      Fintype.card_le_of_injective origin hinjective
    have hc' : O.card ≤ w := by simpa using hc
    exact_mod_cast hc'
  have hforeign :
      (Finset.univ.sum (fun v : ↥O =>
        ∑ u ∈ Finset.univ.erase v,
          protectedReceipt src w (T.state v.val).rows (origin u))) ≤
      3 * η * w / 32 := by
    have hnode (v : O) :
        (∑ u ∈ Finset.univ.erase v,
          protectedReceipt src w (T.state v.val).rows (origin u)) ≤
        O.card * (2 * μweight * δ v) := by
      calc
        _ ≤ ∑ u ∈ Finset.univ.erase v, 2 * μweight * δ v := by
          apply Finset.sum_le_sum
          intro u hu
          exact hpair v u (Finset.ne_of_mem_erase hu)
        _ = (Finset.univ.erase v).card * (2 * μweight * δ v) := by simp
        _ ≤ O.card * (2 * μweight * δ v) := by
          have hc : (Finset.univ.erase v).card ≤ O.card := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ v)]
            simp
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc)
            (mul_nonneg (mul_nonneg (by norm_num) hμ) (hδpoint v))
    have hsum :
        (Finset.univ.sum (fun v : ↥O =>
          ∑ u ∈ Finset.univ.erase v,
            protectedReceipt src w (T.state v.val).rows (origin u))) ≤
        Finset.univ.sum (fun v : ↥O =>
          (O.card : ℝ) * (2 * μweight * δ v)) := by
      apply Finset.sum_le_sum
      intro v _
      exact hnode v
    have hsum' :
        (Finset.univ.sum (fun v : ↥O =>
          ∑ u ∈ Finset.univ.erase v,
            protectedReceipt src w (T.state v.val).rows (origin u))) ≤
        (O.card : ℝ) * (2 * μweight * (Finset.univ.sum (fun v : ↥O => δ v))) := by
      calc
        _ ≤ Finset.univ.sum (fun v : ↥O =>
            (O.card : ℝ) * (2 * μweight * δ v)) := hsum
        _ = Finset.univ.sum (fun v : ↥O =>
            ((O.card : ℝ) * (2 * μweight)) * δ v) := by
          congr 1
          funext v
          ring
        _ = ((O.card : ℝ) * (2 * μweight)) *
            Finset.univ.sum (fun v : ↥O => δ v) := by
          rw [Finset.mul_sum]
        _ = (O.card : ℝ) *
            (2 * μweight * Finset.univ.sum (fun v : ↥O => δ v)) := by ring
    have hprod : 0 ≤ 2 * μweight *
        (Finset.univ.sum (fun v : ↥O => δ v)) := by positivity
    have hbound := mul_le_mul_of_nonneg_right hcard hprod
    nlinarith
  have hexception :
      (Finset.univ.sum (fun u : ↥O =>
        ∑ v ∈ Finset.univ \ O,
          protectedReceipt src w (T.state v).rows (origin u))) ≤
      η * w / 16 := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ v ∈ Finset.univ \ O, Kstar * capacity v := by
        apply Finset.sum_le_sum
        intro v hv
        exact hremote v hv
      _ = Kstar * (∑ v ∈ Finset.univ \ O, capacity v) := by
        simp only [Nat.cast_sum, Finset.mul_sum]
      _ ≤ Kstar * E := by
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hcapacity) hK
      _ ≤ η * w / 16 := hcapacityScalar
  rw [hpartition] at hout
  nlinarith

end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.indexed_run_mass_contradiction
