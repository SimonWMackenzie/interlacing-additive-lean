import CurrentAdditive.V39OwnerLocalCost
import CurrentAdditive.InjectiveProjectionTVCompatible

/-! Selected v39 `res:destinations`: live supports cannot reach an original
leaf. Padding preserves the actual entries and budget of the current game.
Every projection below uses the same original retained stream event. -/

namespace CurrentAdditive.V39OwnerLocalCost

open Paper2 Paper2.ReferenceCertificates
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicIndexedMatrix.Sources

section Probability

variable {S Z : Type*} [Fintype S] [Fintype Z] {w : ℕ}

/-- A singleton image of the original retained event has almost full base
mass whenever its conditioned marginal is close to the original base law. -/
theorem singleton_image_mass_of_tv
    (source : FiniteLaw S) (ν : FiniteLaw Z) (decode : S → Fin w → Z)
    (Yevent : Set S) (hY : 0 < source.prob (· ∈ Yevent))
    (i : Fin w) (ε : ℝ)
    (hTV : projectionTV (condition source (· ∈ Yevent) hY) ν decode
      (Finset.univ.image (fun _ : Fin 1 => i)) ≤ ε) :
    1 - ε ≤ ν.prob (· ∈ (fun t => decode t i) '' Yevent) := by
  classical
  let B : Set Z := (fun t => decode t i) '' Yevent
  let e : Fin 1 → Fin w := fun _ => i
  have he : Function.Injective e := by
    intro a b _
    exact Subsingleton.elim a b
  have hconditional : (condition source (· ∈ Yevent) hY).prob
      (fun t => decode t i ∈ B) = 1 := by
    rw [condition_prob_event_eq_div]
    have hevent : (fun t => t ∈ Yevent ∧ decode t i ∈ B) =
        (fun t => t ∈ Yevent) := by
      funext t
      apply propext
      exact ⟨And.left, fun ht => ⟨ht, ⟨t, ht, rfl⟩⟩⟩
    rw [hevent, div_self (ne_of_gt hY)]
  have htv := injective_projectionTV_event_abs
    (condition source (· ∈ Yevent) hY) ν decode e he ε hTV
    (fun z => z 0 ∈ B)
  simp only [e] at htv
  rw [hconditional] at htv
  have hiid : (ν.iid 1).prob (fun z => z 0 ∈ B) = ν.prob (· ∈ B) := by
    exact Paper2.ReferenceProjectionMass.iid_one_coordinate_prob ν (· ∈ B)
  rw [hiid] at htv
  have hh := (abs_le.mp htv).2
  change 1 - ε ≤ ν.prob (· ∈ B)
  linarith

end Probability

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  {μI : PositiveRationalLaw I} {w : ℕ}
  (streams : InternalStreams src μI w)

/-- One actual good reference support already forces the base profile
cost on the same retained node, with no source independence after deletion. -/
theorem owner_reference_single_cost
    (ν : PositiveRationalLaw (Row (I := I) src))
    (R₀ : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Paper2.SourceMatrix.Tail s Y)
    (R : Set (Fin w × V38IndexedTwoTag.Column src))
    (Yevent : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (family : Family (Fin w) (src.outer.Label × src.gamma.Label))
    (i : Fin w) (H : ℕ) (x v τ : ℝ)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile
      (Nref src R₀ activity ξ₀) (ordinaryLaw src).toFiniteLaw
      ν.toFiniteLaw x (H : ℤ))
    (hfloor : x ≤ (ordinaryLaw src).toFiniteLaw.prob
      (fun Z => Z ∈ family.support i))
    (hreach : ∀ Z ∈ family.support i, (i, Sum.inl Z) ∈ R)
    (hv : 0 < v) (hv1 : v ≤ 1)
    (hY : v ≤ streams.law.toFiniteLaw.prob (· ∈ Yevent))
    (hTV : projectionTV
      (condition streams.law.toFiniteLaw (· ∈ Yevent) (hv.trans_le hY))
      ν.toFiniteLaw (InternalStreams.decode src streams)
      (Finset.univ.image (fun _ : Fin 1 => i)) ≤ V38Moments.epsilon v τ) :
    H ≤ Compression.restrictionD
      (internalMatrix src streams R₀ activity ξ₀) R Yevent := by
  classical
  let U : Set (src.outer.Label × src.gamma.Label) :=
    {Z | (i, Sum.inl Z) ∈ R}
  let V : Set (Row (I := I) src) :=
    (fun t => InternalStreams.decode src streams t i) '' Yevent
  have hrow : x ≤ (ordinaryLaw src).toFiniteLaw.prob (· ∈ U) := by
    apply hfloor.trans
    apply FiniteLaw.prob_mono
    intro Z hZ
    exact hreach Z hZ
  have hmass := singleton_image_mass_of_tv streams.law.toFiniteLaw
    ν.toFiniteLaw (InternalStreams.decode src streams) Yevent
    (hv.trans_le hY) i (V38Moments.epsilon v τ) hTV
  have hε := V38RareBoost.short_epsilon v τ hv hv1
  have hcol : (3 / 5 : ℝ) ≤ ν.toFiniteLaw.prob (· ∈ V) := by
    dsimp only [V]
    linarith
  have hlow : H ≤ Compression.restrictionD (Nref src R₀ activity ξ₀) U V := by
    have hh := hprofile ⟨0, by omega⟩ U V hrow (by simpa using hcol)
    simp only [Nat.cast_zero, sub_zero] at hh
    exact_mod_cast hh
  have hproject : Compression.restrictionD (Nref src R₀ activity ξ₀) U V ≤
      Compression.restrictionD (internalMatrix src streams R₀ activity ξ₀)
        R Yevent := by
    apply SourceProjection.restrictionD_projected_le
      (internalMatrix src streams R₀ activity ξ₀) (Nref src R₀ activity ξ₀)
      (fun Z => (i, Sum.inl Z))
      (fun t => InternalStreams.decode src streams t i) R Yevent U
    · intro Z hZ
      exact hZ
    · intro Z _ t _
      rfl
  exact hlow.trans hproject

/-- Any original leaf computing the actual retained node has no live good
reference support. This is a communication obstruction, separate from the
structural no-early-leaf property supplied by dummy padding. -/
theorem owner_reference_leaf_active_empty
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
    (hH : 1 ≤ H)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile
      (Nref src R₀ activity ξ₀) (ordinaryLaw src).toFiniteLaw
      ν.toFiniteLaw x (H : ℤ))
    (houtside : ∀ i ∈ family.active, i ∉ E)
    (hfloor : ∀ i ∈ family.active, x ≤ (ordinaryLaw src).toFiniteLaw.prob
      (fun Z => Z ∈ family.support i))
    (hreach : ∀ i ∈ family.active, ∀ Z ∈ family.support i,
      (i, Sum.inl Z) ∈ R)
    (hv : 0 < v) (hv1 : v ≤ 1)
    (hY : v ≤ streams.law.toFiniteLaw.prob (· ∈ Yevent))
    (hTV : ∀ J : Finset (Fin w), J ⊆ Finset.univ \ E → J.card ≤ 8 →
      projectionTV
        (condition streams.law.toFiniteLaw (· ∈ Yevent) (hv.trans_le hY))
        ν.toFiniteLaw (InternalStreams.decode src streams) J ≤
          V38Moments.epsilon v τ)
    (hcompute : ∀ row ∈ R, ∀ t ∈ Yevent,
      P.eval row t = internalMatrix src streams R₀ activity ξ₀ row t)
    (hleaf : P.cost = 0) : family.active = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  let e : Fin 1 → Fin w := fun _ => i
  have hsub : Finset.univ.image e ⊆ Finset.univ \ E := by
    intro j hj
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, houtside i hi⟩
  have hcard : (Finset.univ.image e).card ≤ 8 := by
    exact Finset.card_image_le.trans (by simp)
  have hlower := owner_reference_single_cost src streams ν R₀ activity ξ₀
    R Yevent family i H x v τ hprofile (hfloor i hi) (hreach i hi)
    hv hv1 hY (hTV _ hsub hcard)
  have hupper := owner_node_restriction_le_protocol src streams R₀ activity ξ₀
    R Yevent P hcompute
  have hzero : Compression.restrictionD
      (internalMatrix src streams R₀ activity ξ₀) R Yevent ≤ 0 := by
    simpa only [hleaf] using hupper
  exact (Nat.not_le_of_gt hH) (hlower.trans hzero)

/-- Dummy Alice padding preserves this same current two-tag game and its
budget, and yields the complete structural frontier used by owner counting. -/
theorem owner_reference_padding
    (R₀ : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Paper2.SourceMatrix.Tail s Y)
    (R : Set (Fin w × V38IndexedTwoTag.Column src))
    (Yevent : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (P : Workspace.Types.Protocol.Protocol
      (Fin w × V38IndexedTwoTag.Column src)
      (streams.metadataStream.Label ×
        (streams.baseStream.Label × streams.selectorStream.Label)) Bool)
    (H r : ℕ)
    (hcompute : ∀ row ∈ R, ∀ t ∈ Yevent,
      P.eval row t = internalMatrix src streams R₀ activity ξ₀ row t)
    (hcost : P.cost ≤ H+r) :
    (∀ row ∈ R, ∀ t ∈ Yevent,
      (ReferencePrefix.padAlicePrefix r P).eval row t =
        internalMatrix src streams R₀ activity ξ₀ row t) ∧
      (ReferencePrefix.padAlicePrefix r P).cost ≤ H+r ∧
      ReferencePrefix.NoEarlyLeaf r (ReferencePrefix.padAlicePrefix r P) := by
  refine ⟨?_, ?_, ReferencePrefix.padAlicePrefix_noEarlyLeaf r P⟩
  · intro row hrow t ht
    rw [ReferencePrefix.padAlicePrefix_eval]
    exact hcompute row hrow t ht
  · exact (ReferencePrefix.padAlicePrefix_cost_le r P).trans (by omega)

#print axioms singleton_image_mass_of_tv
#print axioms owner_reference_single_cost
#print axioms owner_reference_leaf_active_empty
#print axioms owner_reference_padding

end CurrentAdditive.V39OwnerLocalCost
