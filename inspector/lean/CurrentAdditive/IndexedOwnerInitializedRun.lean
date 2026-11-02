import CurrentAdditive.IndexedOwnerInitialState

/-! Apply the checked owner-run closure to a state constructed from the
actual retained W rectangle and its original protocol. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.ReferenceCertificates Paper2.ReferenceCertificateTree
  Paper2.ReferenceOwners Workspace.Types.Protocol

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  {μI : PositiveRationalLaw I} {w : ℕ}
  (streams : InternalStreams src μI w)

theorem indexed_initialised_owner_capacity
    (ν : PositiveRationalLaw (Row (I := I) src))
    (R₀ : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Paper2.SourceMatrix.Tail s Y)
    (R : Set (Fin w × Column src))
    (Yevent : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (P : Protocol Yevent R Bool)
    (E : Finset (Fin w)) (r H : ℕ) (η x θ ε : ℝ)
    (hw : w = 2^r) (hrpos : 1 ≤ r) (hd : 2 ≤ H) (hx : 0 < x)
    (hscale : ∀ a ≤ r, (2 : ℝ)^a * x ≤ 1)
    (hprofile : RestrictionProfile
      (Nref src R₀ activity ξ₀)
      (ordinaryLaw src).toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (hwise : IsDWise 8192 streams.law.toFiniteLaw
      (InternalStreams.decode src streams) ν.toFiniteLaw)
    (hR : 1 - η / (16 * w) ≤
      (indexedFirstRowLaw src (by rw [hw]; positivity)).prob (· ∈ R))
    (hmargin : 2*w*x + η / (16 * (127 / 128 : ℝ)) < 1)
    (hθ : 0 < θ)
    (hY : θ ≤ streams.law.toFiniteLaw.prob (· ∈ Yevent))
    (hεpos : 0 < ε)
    (hεcap : ε ≤ (2 : ℝ)^(-20 : ℤ) / 1024 *
      θ^((1 : ℝ)/256))
    (hTV : ∀ J : Finset (Fin w),
      J ⊆ Finset.univ \ E → J.card ≤ 8 →
      projectionTV
        (condition streams.law.toFiniteLaw (· ∈ Yevent)
          (hθ.trans_le hY)) ν.toFiniteLaw
        (InternalStreams.decode src streams) J ≤ ε)
    (hP : P.Computes (fun t row => W src streams R₀ activity ξ₀ t.val row.val))
    (hPcost : P.cost ≤ H+r) :
    ∃ row0 : R, ∃ col0 : Yevent,
      ∃ st : State (Fin w × Column src)
        (streams.metadataStream.Label ×
          (streams.baseStream.Label × streams.selectorStream.Label))
        (Fin w) (src.outer.Label × src.gamma.Label),
      st = indexedInitialState src streams R Yevent row0 col0 P E r ∧
      (let T := run (ordinaryLaw src).toFiniteLaw
        (referenceInput src) (Paper2.ReferenceSchedule.floor w x) 0 r st
      let F := fun z : T.Leaves => (T.state z).family
      let final := fun z : T.Leaves => (T.route z).length = r
      2^r - exceptionBudget E.card ≤ (ownerNodes F final).card ∧
        exceptionalCapacity F final (fun z => 2^(r-(T.route z).length)) ≤
          exceptionBudget E.card) := by
  classical
  have hwpos : 0 < w := by rw [hw]; positivity
  obtain ⟨row0, hrow0⟩ := indexed_retained_rows_nonempty src hwpos
    R η x hx.le hR hmargin
  obtain ⟨col0, hcol0⟩ := indexed_event_nonempty_of_prob_pos
    streams.law.toFiniteLaw Yevent (hθ.trans_le hY)
  let st := indexedInitialState src streams R Yevent
    ⟨row0, hrow0⟩ ⟨col0, hcol0⟩ P E r
  let n := (Finset.univ \ E).card
  have hEw : E.card ≤ w := by
    simpa using Finset.card_le_card (Finset.subset_univ E)
  have hn : n = w - E.card := by
    dsimp [n]
    rw [Finset.card_sdiff]
    simp
  have hinitial : 2^r ≤ n + E.card := by
    rw [← hw]
    omega
  have hvalid : st.family.unsplit ⊆ st.family.active :=
    indexedInitialFamily_valid src R E
  have hunits : 2*n ≤ units st.family := by
    change 2*n ≤ units (indexedInitialFamily src R E)
    rw [indexedInitialFamily_units src R E, hn]
  have houtside : ∀ i ∈ st.family.active, i ∉ E := by
    intro i hi
    exact (Finset.mem_sdiff.mp hi).2
  have hfloor : ∀ i ∈ st.family.active,
      Paper2.ReferenceSchedule.floor w x 0 ≤
        (ordinaryLaw src).toFiniteLaw.prob
          (fun Z => Z ∈ st.family.support i) :=
    indexedInitialFamily_floor src hwpos R E η x hR hmargin
  have hreach : ∀ i ∈ st.family.active,
      ∀ Z ∈ st.family.support i,
        (i, Column.ordinary Z) ∈ st.rows :=
    indexedInitialFamily_reaches src R E
  have hprefix : Paper2.ReferencePrefix.NoEarlyLeaf r st.protocol :=
    indexedInitialState_noEarlyLeaf src streams R Yevent
      ⟨row0, hrow0⟩ ⟨col0, hcol0⟩ P E r
  have hcompute : ∀ row ∈ st.rows, ∀ t ∈ Yevent,
      st.protocol.eval row t = W src streams R₀ activity ξ₀ t row := by
    intro row hr t ht
    exact indexedInitialState_correct src streams R₀ activity ξ₀
      R Yevent ⟨row0, hrow0⟩ ⟨col0, hcol0⟩ P hP E r
      ⟨row, hr⟩ ⟨t, ht⟩
  have hcost : st.protocol.cost ≤ H+r :=
    indexedInitialState_cost src streams R Yevent
      ⟨row0, hrow0⟩ ⟨col0, hcol0⟩ P E r H hPcost
  have hv1 : θ ≤ 1 :=
    hY.trans (streams.law.toFiniteLaw.prob_le_one (· ∈ Yevent))
  refine ⟨⟨row0, hrow0⟩, ⟨col0, hcol0⟩, st, rfl, ?_⟩
  exact indexed_owner_capacity_of_source_bounds src streams ν
    R₀ activity ξ₀ st Yevent E r n E.card H x θ ε
    hw hrpos hd hx hscale hprofile hwise hvalid hprefix
    hinitial hunits houtside hfloor hreach hθ hv1 hY
    hεpos hεcap hTV hcompute hcost

#print axioms indexed_initialised_owner_capacity

end CurrentAdditive.DeterministicIndexedMatrix.Sources
