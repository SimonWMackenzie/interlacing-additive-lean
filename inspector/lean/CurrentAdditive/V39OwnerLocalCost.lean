import CurrentAdditive.V38IndexedTwoTag
import CurrentAdditive.V39RareBoost
import CurrentAdditive.IndexedIncomingBound
import Paper2.ReferencePrefix
import Paper2.ReferenceCertificates
import Paper2.ReferenceTerminalCapacity

/-! Selected v39 res:destinations, local current-two-tag reference obstructions.
The conditioned event stays the original complete-stream source event. -/

namespace CurrentAdditive.V39OwnerLocalCost

open Paper2 Paper2.ReferenceCertificates
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicIndexedMatrix.Sources

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  {μI : PositiveRationalLaw I} {w : ℕ}
  (streams : InternalStreams src μI w)


/-- The actual transpose-row game on the current two-tag alphabet. Its
ordinary component is literally `Nref`; no legacy fixed-tail label occurs. -/
def internalMatrix (R₀ : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Paper2.SourceMatrix.Tail s Y) :
    (Fin w × V38IndexedTwoTag.Column src) →
      (streams.metadataStream.Label ×
        (streams.baseStream.Label × streams.selectorStream.Label)) → Bool :=
  fun row t => V38IndexedTwoTag.matrix src R₀ activity ξ₀ row.2
    (InternalStreams.decode src streams t row.1)

@[simp] theorem ordinary_entry (R₀ : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Paper2.SourceMatrix.Tail s Y)
    (i : Fin w) (Z : src.outer.Label × src.gamma.Label)
    (t : streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)) :
    internalMatrix src streams R₀ activity ξ₀ (i, Sum.inl Z) t =
      Nref src R₀ activity ξ₀ Z (InternalStreams.decode src streams t i) := rfl

/-- A family of original ordinary row supports inside a node. -/
theorem owner_reference_local_cost
    (ν : PositiveRationalLaw (Row (I := I) src))
    (R₀ : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Paper2.SourceMatrix.Tail s Y)
    (R : Set (Fin w × V38IndexedTwoTag.Column src))
    (Y K : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (family : Family (Fin w) (src.outer.Label × src.gamma.Label))
    (E : Finset (Fin w)) (H a : ℕ) (x v τ : ℝ)
    (ha : 1 ≤ a) (hd : 2 ≤ H) (hx : 0 < x)
    (hscale : (2 : ℝ)^a * x ≤ 1)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile
      (Nref src R₀ activity ξ₀)
      (ordinaryLaw src).toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (hwise : IsDWise 8192 streams.law.toFiniteLaw
      (InternalStreams.decode src streams) ν.toFiniteLaw)
    (hcount : 2^(a-1)+1 ≤ family.active.card)
    (houtside : ∀ i ∈ family.active, i ∉ E)
    (hfloor : ∀ i ∈ family.active,
      (2 : ℝ)^a * x ≤ (ordinaryLaw src).toFiniteLaw.prob
        (fun Z => Z ∈ family.support i))
    (hreach : ∀ i ∈ family.active, ∀ Z ∈ family.support i,
      (i, Sum.inl Z) ∈ R)
    (hv : 0 < v) (hv1 : v ≤ 1)
    (hY : v ≤ streams.law.toFiniteLaw.prob (· ∈ Y))
    (hKY : K ⊆ Y)
    (hK : (1/2 : ℝ) ≤
      streams.law.toFiniteLaw.prob (· ∈ K) /
        streams.law.toFiniteLaw.prob (· ∈ Y))
    (hτ : 0 < τ)
    (hTV : ∀ J : Finset (Fin w),
      J ⊆ Finset.univ \ E → J.card ≤ 8 →
      projectionTV
        (condition streams.law.toFiniteLaw (· ∈ Y)
          (hv.trans_le hY)) ν.toFiniteLaw
        (InternalStreams.decode src streams) J ≤ V38Moments.epsilon v τ) :
    H+a ≤ Paper2.Compression.restrictionD
      (fun pc t => internalMatrix src streams R₀ activity ξ₀ pc t) R K := by
  classical
  let Rows : Fin w → Set (src.outer.Label × src.gamma.Label) :=
    fun i => {Z | Z ∈ family.support i}
  have hrow : ∀ i ∈ family.active,
      (2 : ℝ)^a * x ≤ (ordinaryLaw src).toFiniteLaw.prob (· ∈ Rows i) :=
    hfloor
  have hlower := V38RareBoost.rareboost_two_threshold
    (ordinaryLaw src).toFiniteLaw ν (Nref src R₀ activity ξ₀)
    streams.law.toFiniteLaw (InternalStreams.decode src streams)
    hwise family.active E Rows Y K H a x v τ
    ha hd hx hscale hprofile hcount houtside hrow
    hv hv1 hτ hY hKY hK hTV
  let S := ArbitraryPrefix.rowRectangle family.active Rows
  let f : (Fin w × (src.outer.Label × src.gamma.Label)) →
      Fin w × V38IndexedTwoTag.Column src := fun row => (row.1, .inl row.2)
  have hf : Set.MapsTo f S R := by
    intro row hr
    change row.1 ∈ family.active ∧ row.2 ∈ Rows row.1 at hr
    exact hreach row.1 hr.1 row.2 hr.2
  have hmap := Paper2.SourceProjection.restrictionD_map_le
    (fun pc t => internalMatrix src streams R₀ activity ξ₀ pc t)
    f id R K S K hf (fun _ h => h)
  have heq : Paper2.Compression.restrictionD
      (fun row t => Nref src R₀ activity ξ₀ row.2
        (InternalStreams.decode src streams t row.1)) S K =
      Paper2.Compression.restrictionD
        (fun row t => internalMatrix src streams R₀ activity ξ₀ (f row) t) S K := by
    unfold Paper2.Compression.restrictionD
    congr 1
  rw [heq] at hlower
  exact hlower.trans hmap

#print axioms owner_reference_local_cost

/-- The retained original node cannot contain the stated number of good
reference supports under a strictly smaller communication budget. -/
theorem owner_reference_active_lt
    (ν : PositiveRationalLaw (Row (I := I) src))
    (R₀ : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Paper2.SourceMatrix.Tail s Y)
    (R : Set (Fin w × V38IndexedTwoTag.Column src))
    (Y K : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (family : Family (Fin w) (src.outer.Label × src.gamma.Label))
    (E : Finset (Fin w)) (H a : ℕ) (x v τ : ℝ)
    (ha : 1 ≤ a) (hd : 2 ≤ H) (hx : 0 < x)
    (hscale : (2 : ℝ)^a * x ≤ 1)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile
      (Nref src R₀ activity ξ₀)
      (ordinaryLaw src).toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (hwise : IsDWise 8192 streams.law.toFiniteLaw
      (InternalStreams.decode src streams) ν.toFiniteLaw)
    (houtside : ∀ i ∈ family.active, i ∉ E)
    (hfloor : ∀ i ∈ family.active,
      (2 : ℝ)^a * x ≤ (ordinaryLaw src).toFiniteLaw.prob
        (fun Z => Z ∈ family.support i))
    (hreach : ∀ i ∈ family.active, ∀ Z ∈ family.support i,
      (i, Sum.inl Z) ∈ R)
    (hv : 0 < v) (hv1 : v ≤ 1)
    (hY : v ≤ streams.law.toFiniteLaw.prob (· ∈ Y))
    (hKY : K ⊆ Y)
    (hK : (1/2 : ℝ) ≤
      streams.law.toFiniteLaw.prob (· ∈ K) /
        streams.law.toFiniteLaw.prob (· ∈ Y))
    (hτ : 0 < τ)
    (hTV : ∀ J : Finset (Fin w),
      J ⊆ Finset.univ \ E → J.card ≤ 8 →
      projectionTV
        (condition streams.law.toFiniteLaw (· ∈ Y)
          (hv.trans_le hY)) ν.toFiniteLaw
        (InternalStreams.decode src streams) J ≤ V38Moments.epsilon v τ)
    (hbudget : Paper2.Compression.restrictionD
      (fun pc t => internalMatrix src streams R₀ activity ξ₀ pc t) R K < H+a) :
    family.active.card < 2^(a-1)+1 := by
  by_contra hn
  have hc : 2^(a-1)+1 ≤ family.active.card := by omega
  have hlower := owner_reference_local_cost src streams ν R₀ activity ξ₀
    R Y K family E H a x v τ ha hd hx hscale hprofile hwise
    hc houtside hfloor hreach hv hv1 hY hKY hK hτ hTV
  omega

#print axioms owner_reference_active_lt

/-- Twice reference weight is bounded by capacity once at most half
as many active supports survive. This is the selected source's sharp bound. -/
theorem owner_units_le_of_active_lt
    {A : Type*} [Fintype A] (family : Family (Fin w) A)
    (a κ : ℕ) (ha : 1 ≤ a) (hκ : κ = 2^a)
    (hvalid : family.unsplit ⊆ family.active)
    (hactive : family.active.card < 2^(a-1)+1) :
    units family ≤ κ := by
  have hu := Finset.card_le_card hvalid
  have hp : 2^a = 2*2^(a-1) := by
    conv_lhs => rw [show a = (a-1)+1 by omega]
    rw [pow_succ']
  dsimp only [units]
  omega

#print axioms owner_units_le_of_active_lt

/-- A Bob query has a genuine original-index child carrying at least half
the mass of the retained full-stream event. -/
theorem owner_dense_bob_child
    (Y : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (query : (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)) → Bool)
    (hY : 0 < streams.law.toFiniteLaw.prob (· ∈ Y)) :
    ∃ b : Bool,
      let K := Paper2.ReferenceColumnStep.columnChild Y query b
      K ⊆ Y ∧ (1/2 : ℝ) ≤
        streams.law.toFiniteLaw.prob (· ∈ K) /
          streams.law.toFiniteLaw.prob (· ∈ Y) := by
  classical
  let μ := streams.law.toFiniteLaw
  have hpart := Paper2.TwoStreamColumnStep.ordinary_partition μ Y id query
  let K := Paper2.ReferenceColumnStep.columnChild Y query
  have heq (b : Bool) :
      μ.prob (· ∈ Paper2.TwoStreamColumnStep.ordinaryChild Y id query b) =
        μ.prob (· ∈ K b) := rfl
  rw [heq false, heq true] at hpart
  by_cases hf : μ.prob (· ∈ K false) ≥ μ.prob (· ∈ Y)/2
  · refine ⟨false, ?_, ?_⟩
    · intro t ht; exact ht.1
    · apply (le_div_iff₀ hY).2
      nlinarith
  · refine ⟨true, ?_, ?_⟩
    · intro t ht; exact ht.1
    · apply (le_div_iff₀ hY).2
      push Not at hf
      nlinarith

/-- The actual Bob bit leaves each genuine child one bit below the parent
budget, expressed on the original transposed W rectangle. -/
theorem owner_bob_child_budget
    (R₀ : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Paper2.SourceMatrix.Tail s Y)
    (R : Set (Fin w × V38IndexedTwoTag.Column src))
    (Yevent : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (query : (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)) → Bool)
    (left right : Workspace.Types.Protocol.Protocol
      (Fin w × V38IndexedTwoTag.Column src)
      (streams.metadataStream.Label ×
        (streams.baseStream.Label × streams.selectorStream.Label)) Bool)
    (H a : ℕ)
    (hcompute : ∀ row ∈ R, ∀ t ∈ Yevent,
      (Workspace.Types.Protocol.Protocol.bNode query left right).eval row t =
        internalMatrix src streams R₀ activity ξ₀ row t)
    (hcost : (Workspace.Types.Protocol.Protocol.bNode query left right).cost ≤ H+a)
    (b : Bool) :
    Paper2.Compression.restrictionD
      (fun row t => internalMatrix src streams R₀ activity ξ₀ row t) R
      (Paper2.ReferenceColumnStep.columnChild Yevent query b) < H+a := by
  have hc := Paper2.ReferenceColumnStep.restriction_add_one_le
    (fun row t => internalMatrix src streams R₀ activity ξ₀ row t)
    R Yevent query left right hcompute b
  omega

#print axioms owner_dense_bob_child
#print axioms owner_bob_child_budget

/-- A genuine first-Bob node cannot carry the threshold reference weight.
The projection and family premises refer to the original retained node. -/
theorem owner_reference_first_bob_bounds
    (ν : PositiveRationalLaw (Row (I := I) src))
    (R₀ : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Paper2.SourceMatrix.Tail s Y)
    (R : Set (Fin w × V38IndexedTwoTag.Column src))
    (Yevent : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (family : Family (Fin w) (src.outer.Label × src.gamma.Label))
    (E : Finset (Fin w)) (H a κ : ℕ) (x v τ : ℝ)
    (query : (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)) → Bool)
    (left right : Workspace.Types.Protocol.Protocol
      (Fin w × V38IndexedTwoTag.Column src)
      (streams.metadataStream.Label ×
        (streams.baseStream.Label × streams.selectorStream.Label)) Bool)
    (ha : 1 ≤ a) (hd : 2 ≤ H) (hx : 0 < x)
    (hκ : κ = 2^a)
    (hvalid : family.unsplit ⊆ family.active)
    (hscale : (2 : ℝ)^a * x ≤ 1)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile
      (Nref src R₀ activity ξ₀)
      (ordinaryLaw src).toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (hwise : IsDWise 8192 streams.law.toFiniteLaw
      (InternalStreams.decode src streams) ν.toFiniteLaw)
    (houtside : ∀ i ∈ family.active, i ∉ E)
    (hfloor : ∀ i ∈ family.active,
      (2 : ℝ)^a * x ≤ (ordinaryLaw src).toFiniteLaw.prob
        (fun Z => Z ∈ family.support i))
    (hreach : ∀ i ∈ family.active, ∀ Z ∈ family.support i,
      (i, Sum.inl Z) ∈ R)
    (hv : 0 < v) (hv1 : v ≤ 1)
    (hY : v ≤ streams.law.toFiniteLaw.prob (· ∈ Yevent))
    (hτ : 0 < τ)
    (hTV : ∀ J : Finset (Fin w),
      J ⊆ Finset.univ \ E → J.card ≤ 8 →
      projectionTV
        (condition streams.law.toFiniteLaw (· ∈ Yevent)
          (hv.trans_le hY)) ν.toFiniteLaw
        (InternalStreams.decode src streams) J ≤ V38Moments.epsilon v τ)
    (hcompute : ∀ row ∈ R, ∀ t ∈ Yevent,
      (Workspace.Types.Protocol.Protocol.bNode query left right).eval row t =
        internalMatrix src streams R₀ activity ξ₀ row t)
    (hcost : (Workspace.Types.Protocol.Protocol.bNode query left right).cost ≤ H+a) :
    family.active.card ≤ 2^(a-1) ∧ units family ≤ κ := by
  obtain ⟨b, hsub, hmass⟩ := owner_dense_bob_child src streams
    Yevent query (hv.trans_le hY)
  let K := Paper2.ReferenceColumnStep.columnChild Yevent query b
  have hbudget := owner_bob_child_budget src streams R₀ activity ξ₀
    R Yevent query left right H a hcompute hcost b
  have hactive := owner_reference_active_lt src streams ν R₀ activity ξ₀
    R Yevent K family E H a x v τ ha hd hx hscale hprofile hwise
    houtside hfloor hreach hv hv1 hY hsub hmass hτ hTV
    hbudget
  exact ⟨by omega, owner_units_le_of_active_lt (w := w) family a κ ha hκ hvalid hactive⟩

#print axioms owner_reference_first_bob_bounds

/-- Correctness of an original node protocol supplies its ordinary
restriction upper bound, with no replacement of its row or column carrier. -/
theorem owner_node_restriction_le_protocol
    (R₀ : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Paper2.SourceMatrix.Tail s Y)
    (R : Set (Fin w × V38IndexedTwoTag.Column src))
    (Yevent : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (P : Workspace.Types.Protocol.Protocol
      (Fin w × V38IndexedTwoTag.Column src)
      (streams.metadataStream.Label ×
        (streams.baseStream.Label × streams.selectorStream.Label)) Bool)
    (hcompute : ∀ row ∈ R, ∀ t ∈ Yevent,
      P.eval row t = internalMatrix src streams R₀ activity ξ₀ row t) :
    Paper2.Compression.restrictionD
      (fun row t => internalMatrix src streams R₀ activity ξ₀ row t) R Yevent ≤ P.cost := by
  classical
  let Q := Workspace.UpperBound.Protocol.comap
    (fun row : R => row.val) (fun t : Yevent => t.val) P
  have hQ : Q.Computes (fun (row : R) (t : Yevent) =>
      internalMatrix src streams R₀ activity ξ₀ row.val t.val) := by
    intro row t
    simpa [Q, Workspace.UpperBound.Protocol.comap_eval] using
      hcompute row.val row.property t.val t.property
  have hD : Paper2.Compression.restrictionD
      (fun row t => internalMatrix src streams R₀ activity ξ₀ row t) R Yevent ≤ Q.cost :=
    Nat.sInf_le ⟨Q, rfl, hQ⟩
  simpa [Q, Workspace.UpperBound.Protocol.comap_cost] using hD

/-- The actual final node budget admits at most one good original reference
support.  Its retained columns are the same full-stream event used for
conditioning, and the source law is not replaced by independent copies. -/
theorem owner_reference_final_active_le_one
    (ν : PositiveRationalLaw (Row (I := I) src))
    (R₀ : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Paper2.SourceMatrix.Tail s Y)
    (R : Set (Fin w × V38IndexedTwoTag.Column src))
    (Yevent : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (family : Family (Fin w) (src.outer.Label × src.gamma.Label))
    (E : Finset (Fin w)) (H : ℕ) (x v τ : ℝ)
    (P : Workspace.Types.Protocol.Protocol
      (Fin w × V38IndexedTwoTag.Column src)
      (streams.metadataStream.Label ×
        (streams.baseStream.Label × streams.selectorStream.Label)) Bool)
    (hd : 2 ≤ H) (hx : 0 < x) (hscale : 2*x ≤ 1)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile
      (Nref src R₀ activity ξ₀)
      (ordinaryLaw src).toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (hwise : IsDWise 8192 streams.law.toFiniteLaw
      (InternalStreams.decode src streams) ν.toFiniteLaw)
    (houtside : ∀ i ∈ family.active, i ∉ E)
    (hfloor : ∀ i ∈ family.active,
      2*x ≤ (ordinaryLaw src).toFiniteLaw.prob
        (fun Z => Z ∈ family.support i))
    (hreach : ∀ i ∈ family.active, ∀ Z ∈ family.support i,
      (i, Sum.inl Z) ∈ R)
    (hv : 0 < v) (hv1 : v ≤ 1)
    (hY : v ≤ streams.law.toFiniteLaw.prob (· ∈ Yevent))
    (hτ : 0 < τ)
    (hTV : ∀ J : Finset (Fin w),
      J ⊆ Finset.univ \ E → J.card ≤ 8 →
      projectionTV
        (condition streams.law.toFiniteLaw (· ∈ Yevent)
          (hv.trans_le hY)) ν.toFiniteLaw
        (InternalStreams.decode src streams) J ≤ V38Moments.epsilon v τ)
    (hcompute : ∀ row ∈ R, ∀ t ∈ Yevent,
      P.eval row t = internalMatrix src streams R₀ activity ξ₀ row t)
    (hcost : P.cost ≤ H) :
    family.active.card ≤ 1 := by
  have hupper := owner_node_restriction_le_protocol src streams
    R₀ activity ξ₀ R Yevent P hcompute
  have hbudget : Paper2.Compression.restrictionD
      (fun row t => internalMatrix src streams R₀ activity ξ₀ row t) R Yevent < H+1 := by
    omega
  have hmass : (1/2 : ℝ) ≤
      streams.law.toFiniteLaw.prob (· ∈ Yevent) /
        streams.law.toFiniteLaw.prob (· ∈ Yevent) := by
    rw [div_self (ne_of_gt (hv.trans_le hY))]
    norm_num
  have hactive := owner_reference_active_lt src streams ν R₀ activity ξ₀
    R Yevent Yevent family E H 1 x v τ (by omega) hd hx
    (by simpa only [pow_one] using hscale) hprofile hwise
    houtside (by simpa only [pow_one] using hfloor)
    hreach hv hv1 hY (Set.Subset.rfl) hmass hτ hTV hbudget
  simpa using hactive

#print axioms owner_node_restriction_le_protocol
#print axioms owner_reference_final_active_le_one

end CurrentAdditive.V39OwnerLocalCost
