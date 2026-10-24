import CurrentAdditive.IndexedOwnerInitialMass
import Paper2.SourceSupportInitialCore

/-! The padded actual-W protocol and original ordinary reference family. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.ReferenceCertificates Paper2.ReferenceCertificateTree
  Workspace.Types.Protocol

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  {μI : PositiveRationalLaw I} {w : ℕ}
  (streams : InternalStreams src μI w)

/-- Original good coordinates, with ordinary source support from the
unmodified retained row event. -/
noncomputable def indexedInitialFamily
    (R : Set (Fin w × Column src)) (E : Finset (Fin w)) :
    Family (Fin w) (src.outer.Label × src.gamma.Label) := by
  classical
  exact ReferenceCertificates.initial (Finset.univ \ E)
    (fun i => Finset.univ.filter (fun Z => Z ∈ indexedReferenceSupport src R i))

theorem indexedInitialFamily_active
    (R : Set (Fin w × Column src)) (E : Finset (Fin w)) :
    (indexedInitialFamily src R E).active = Finset.univ \ E := rfl

theorem indexedInitialFamily_support_event
    (R : Set (Fin w × Column src)) (E : Finset (Fin w)) (i : Fin w) :
    (fun Z => Z ∈ (indexedInitialFamily src R E).support i) =
      (fun Z => (i, Column.ordinary Z) ∈ R) := by
  classical
  funext Z
  simp [indexedInitialFamily, ReferenceCertificates.initial,
    indexedReferenceSupport]

theorem indexedInitialFamily_valid
    (R : Set (Fin w × Column src)) (E : Finset (Fin w)) :
    (indexedInitialFamily src R E).unsplit ⊆
      (indexedInitialFamily src R E).active := by
  rfl

theorem indexedInitialFamily_reaches
    (R : Set (Fin w × Column src)) (E : Finset (Fin w)) :
    ∀ i ∈ (indexedInitialFamily src R E).active,
      ∀ Z ∈ (indexedInitialFamily src R E).support i,
        (i, Column.ordinary Z) ∈ R := by
  classical
  intro i _ Z hZ
  change Z ∈ Finset.univ.filter (fun Z => Z ∈ indexedReferenceSupport src R i) at hZ
  exact (Finset.mem_filter.mp hZ).2

theorem indexedInitialFamily_floor (hw : 0 < w)
    (R : Set (Fin w × Column src)) (E : Finset (Fin w))
    (η x : ℝ)
    (hR : 1 - η / (16 * w) ≤ (indexedFirstRowLaw src hw).prob (· ∈ R))
    (hmargin : 2*w*x + η / (16 * (127 / 128 : ℝ)) < 1) :
    ∀ i ∈ (indexedInitialFamily src R E).active,
      Paper2.ReferenceSchedule.floor w x 0 ≤
        (ordinaryLaw src).toFiniteLaw.prob
          (fun Z => Z ∈ (indexedInitialFamily src R E).support i) := by
  intro i _
  have heq : (fun Z => Z ∈ (indexedInitialFamily src R E).support i) =
      (fun Z => Z ∈ indexedReferenceSupport src R i) := by
    funext Z
    simp [indexedInitialFamily, ReferenceCertificates.initial]
  rw [heq]
  exact indexed_reference_floor src hw R η x hR hmargin i

theorem indexedInitialFamily_units
    (R : Set (Fin w × Column src)) (E : Finset (Fin w)) :
    units (indexedInitialFamily src R E) =
      2 * (w - E.card) := by
  simp [indexedInitialFamily, units, ReferenceCertificates.initial,
    Finset.card_sdiff]
  omega

/-- An event of positive actual finite-law mass has an original label. -/
theorem indexed_event_nonempty_of_prob_pos {T : Type*} [Fintype T]
    (law : FiniteLaw T) (U : Set T) (h : 0 < law.prob (· ∈ U)) :
    U.Nonempty := by
  by_contra hn
  have hnone : ∀ t, t ∉ U := by
    intro t ht
    exact hn ⟨t, ht⟩
  have heq : (fun t : T => t ∈ U) = fun _ => False := by
    funext t
    exact propext ⟨fun ht => hnone t ht, False.elim⟩
  rw [heq, FiniteLaw.prob_false] at h
  exact (not_lt_of_ge le_rfl) h

/-- The full near-row event is inhabited under the same margin that gives
the initial ordinary floor. -/
theorem indexed_retained_rows_nonempty (hw : 0 < w)
    (R : Set (Fin w × Column src)) (η x : ℝ) (hx : 0 ≤ x)
    (hR : 1 - η / (16 * w) ≤ (indexedFirstRowLaw src hw).prob (· ∈ R))
    (hmargin : 2*w*x + η / (16 * (127 / 128 : ℝ)) < 1) :
    R.Nonempty := by
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hsmall : η < 16 * (w : ℝ) := by
    have hpos : 0 ≤ 2 * (w : ℝ) * x := by positivity
    have hg : η < 16 * (127 / 128 : ℝ) := by
      have hh : η / (16 * (127 / 128 : ℝ)) < 1 := by linarith
      apply (div_lt_iff₀ (by norm_num : (0 : ℝ) <
        16 * (127 / 128 : ℝ))).mp at hh
      simpa using hh
    have hwr : (1 : ℝ) ≤ w := by exact_mod_cast hw
    nlinarith
  have hp : 0 < (indexedFirstRowLaw src hw).prob (· ∈ R) := by
    have hd : η / (16 * (w : ℝ)) < 1 :=
      (div_lt_iff₀ (by positivity : (0 : ℝ) < 16 * (w : ℝ))).2
        (by simpa using hsmall)
    linarith
  exact indexed_event_nonempty_of_prob_pos _ R hp

noncomputable def indexedInitialState
    (R : Set (Fin w × Column src))
    (Yevent : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (row0 : R) (col0 : Yevent)
    (P : Protocol Yevent R Bool) (E : Finset (Fin w)) (r : ℕ) :
    State (Fin w × Column src)
      (streams.metadataStream.Label ×
        (streams.baseStream.Label × streams.selectorStream.Label))
      (Fin w) (src.outer.Label × src.gamma.Label) where
  protocol := Paper2.ReferencePrefix.padAlicePrefix r
    (Workspace.UpperBound.Protocol.comap
      (Paper2.SourceSupportInitial.columnRetraction R row0)
      (Paper2.SourceSupportInitial.columnRetraction Yevent col0)
      (Workspace.UpperBound.Protocol.transpose P))
  rows := R
  family := indexedInitialFamily src R E

theorem indexedInitialState_noEarlyLeaf
    (R : Set (Fin w × Column src))
    (Yevent : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (row0 : R) (col0 : Yevent) (P : Protocol Yevent R Bool)
    (E : Finset (Fin w)) (r : ℕ) :
    Paper2.ReferencePrefix.NoEarlyLeaf r
      (indexedInitialState src streams R Yevent row0 col0 P E r).protocol :=
  Paper2.ReferencePrefix.padAlicePrefix_noEarlyLeaf r _

theorem indexedInitialState_correct
    (R₀ : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Paper2.SourceMatrix.Tail s Y)
    (R : Set (Fin w × Column src))
    (Yevent : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (row0 : R) (col0 : Yevent) (P : Protocol Yevent R Bool)
    (hP : P.Computes (fun t row => W src streams R₀ activity ξ₀ t.val row.val))
    (E : Finset (Fin w)) (r : ℕ)
    (row : R) (t : Yevent) :
    (indexedInitialState src streams R Yevent row0 col0 P E r).protocol.eval
      row.val t.val = W src streams R₀ activity ξ₀ t.val row.val := by
  change (Paper2.ReferencePrefix.padAlicePrefix r _).eval row.val t.val = _
  rw [Paper2.ReferencePrefix.padAlicePrefix_eval,
    Workspace.UpperBound.Protocol.comap_eval]
  simp only [Paper2.SourceSupportInitial.columnRetraction_retained,
    Workspace.UpperBound.Protocol.transpose_eval]
  exact hP t row

theorem indexedInitialState_cost
    (R : Set (Fin w × Column src))
    (Yevent : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (row0 : R) (col0 : Yevent) (P : Protocol Yevent R Bool)
    (E : Finset (Fin w)) (r H : ℕ)
    (hPcost : P.cost ≤ H+r) :
    (indexedInitialState src streams R Yevent row0 col0 P E r).protocol.cost ≤
      H+r := by
  have hp := Paper2.ReferencePrefix.padAlicePrefix_cost_le r
    (Workspace.UpperBound.Protocol.comap
      (Paper2.SourceSupportInitial.columnRetraction R row0)
      (Paper2.SourceSupportInitial.columnRetraction Yevent col0)
      (Workspace.UpperBound.Protocol.transpose P))
  simp only [Workspace.UpperBound.Protocol.comap_cost,
    Workspace.UpperBound.Protocol.transpose_cost] at hp
  change (Paper2.ReferencePrefix.padAlicePrefix r
    (Workspace.UpperBound.Protocol.comap
      (Paper2.SourceSupportInitial.columnRetraction R row0)
      (Paper2.SourceSupportInitial.columnRetraction Yevent col0)
      (Workspace.UpperBound.Protocol.transpose P))).cost ≤ H+r
  exact hp.trans (max_le hPcost (by omega))

#print axioms indexedInitialFamily_floor
#print axioms indexedInitialState_noEarlyLeaf
#print axioms indexedInitialState_correct
#print axioms indexedInitialState_cost

end CurrentAdditive.DeterministicIndexedMatrix.Sources
