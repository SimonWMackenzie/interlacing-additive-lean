import CurrentAdditive.GeneratedOwnerTuple

/-! Original indexed tuple representatives for a pair of template copies. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  {μI : PositiveRationalLaw I} {w : ℕ}
  (streams : InternalStreams src μI w)

/-- Two selector labels occur in the same surviving original indexed
tuple, with the owner and foreign copy both in specified template bins. -/
def ownerPairImage (U : Set (InternalLabel src streams))
    (i j : Fin w) (p r : Fin s) :
    Set (src.inner.Label × src.inner.Label) :=
  fun z => ∃ t ∈ U,
    streams.metadataStream.decode t.1 i = .inl p ∧
    streams.metadataStream.decode t.1 j = .inl r ∧
    streams.selectorStream.decode t.2.2 i = z.1 ∧
    streams.selectorStream.decode t.2.2 j = z.2

noncomputable def ownerPairRepresentative
    (U : Set (InternalLabel src streams))
    (i j : Fin w) (p r : Fin s)
    (z : ownerPairImage src streams U i j p r) :
    InternalLabel src streams := Classical.choose z.property

theorem ownerPairRepresentative_spec
    (U : Set (InternalLabel src streams))
    (i j : Fin w) (p r : Fin s)
    (z : ownerPairImage src streams U i j p r) :
    ownerPairRepresentative src streams U i j p r z ∈ U ∧
    streams.metadataStream.decode
      (ownerPairRepresentative src streams U i j p r z).1 i = .inl p ∧
    streams.metadataStream.decode
      (ownerPairRepresentative src streams U i j p r z).1 j = .inl r ∧
    streams.selectorStream.decode
      (ownerPairRepresentative src streams U i j p r z).2.2 i = z.val.1 ∧
    streams.selectorStream.decode
      (ownerPairRepresentative src streams U i j p r z).2.2 j = z.val.2 :=
  Classical.choose_spec z.property

noncomputable def ownerPairTuple
    (U : Set (InternalLabel src streams))
    (i j : Fin w) (p r : Fin s)
    (z : ownerPairImage src streams U i j p r) :
    OwnerTemplateTuple src streams i :=
  ⟨ownerPairRepresentative src streams U i j p r z,
    ⟨p, (ownerPairRepresentative_spec src streams U i j p r z).2.1⟩⟩

theorem ownerPairTuple_labels
    (U : Set (InternalLabel src streams))
    (i j : Fin w) (p r : Fin s)
    (z : ownerPairImage src streams U i j p r) :
    ownerPairTuple src streams U i j p r z ∈ ownerRetained src streams i U ∧
    ownerBin src streams i (ownerPairTuple src streams U i j p r z) = p ∧
    ownerSelector src streams i (ownerPairTuple src streams U i j p r z) = z.val.1 ∧
    streams.metadataStream.decode
      (ownerPairTuple src streams U i j p r z).val.1 j = .inl r ∧
    streams.selectorStream.decode
      (ownerPairTuple src streams U i j p r z).val.2.2 j = z.val.2 := by
  have h := ownerPairRepresentative_spec src streams U i j p r z
  have hbin := ownerBin_eq src streams i (ownerPairTuple src streams U i j p r z)
  change streams.metadataStream.decode
    (ownerPairRepresentative src streams U i j p r z).1 i =
      .inl (ownerBin src streams i (ownerPairTuple src streams U i j p r z)) at hbin
  have hp : ownerBin src streams i
      (ownerPairTuple src streams U i j p r z) = p :=
    Sum.inl.inj (hbin.symm.trans h.2.1)
  exact ⟨h.1, hp, h.2.2.2.1, h.2.2.1, h.2.2.2.2⟩

/-- Totalize pair representatives using one fixed original template
tuple; outside P0 the choice is never used. -/
noncomputable def ownerPairInput
    (U : Set (InternalLabel src streams))
    (i j : Fin w) (p r : Fin s)
    (P0 : Finset (src.inner.Label × src.inner.Label))
    (hP0 : ∀ z, z ∈ P0 ↔ z ∈ ownerPairImage src streams U i j p r)
    (fallback : OwnerTemplateTuple src streams i)
    (z : src.inner.Label × src.inner.Label) :
    OwnerTemplateTuple src streams i :=
  if hz : z ∈ P0 then
    ownerPairTuple src streams U i j p r ⟨z, (hP0 z).mp hz⟩
  else fallback

theorem ownerPairInput_labels
    (U : Set (InternalLabel src streams))
    (i j : Fin w) (p r : Fin s)
    (P0 : Finset (src.inner.Label × src.inner.Label))
    (hP0 : ∀ z, z ∈ P0 ↔ z ∈ ownerPairImage src streams U i j p r)
    (fallback : OwnerTemplateTuple src streams i)
    (z : src.inner.Label × src.inner.Label) (hz : z ∈ P0) :
    ownerPairInput src streams U i j p r P0 hP0 fallback z ∈
      ownerRetained src streams i U ∧
    ownerBin src streams i
      (ownerPairInput src streams U i j p r P0 hP0 fallback z) = p ∧
    ownerSelector src streams i
      (ownerPairInput src streams U i j p r P0 hP0 fallback z) = z.1 ∧
    streams.metadataStream.decode
      (ownerPairInput src streams U i j p r P0 hP0 fallback z).val.1 j = .inl r ∧
    streams.selectorStream.decode
      (ownerPairInput src streams U i j p r P0 hP0 fallback z).val.2.2 j = z.2 := by
  simpa only [ownerPairInput, dif_pos hz] using
    ownerPairTuple_labels src streams U i j p r ⟨z, (hP0 z).mp hz⟩

private theorem product_first_pushes {S : Type*} [Fintype S]
    (μ : FiniteLaw S) : (μ.prod μ).PushesTo μ Prod.fst := by
  classical
  intro E
  conv_lhs => rw [FiniteLaw.prod_prob μ μ (fun a _ => E a)]
  have hinner (a : S) : μ.prob (fun _ : S => E a) = if E a then 1 else 0 := by
    by_cases ha : E a <;> simp [ha]
  simp_rw [hinner]
  simp only [FiniteLaw.prob]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : E a <;> simp [ha]

theorem ownerPairFirst_mass
    (P0 : Finset (src.inner.Label × src.inner.Label)) (a : ℝ)
    (ha : a ≤ (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw).prob
      (· ∈ (P0 : Set _))) :
    a ≤ src.inner.law.toFiniteLaw.prob
      (· ∈ (fun z : src.inner.Label × src.inner.Label => z.1) '' (P0 : Set _)) :=
  ha.trans (FiniteLaw.prob_le_image
    (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw)
    src.inner.law.toFiniteLaw Prod.fst
    (product_first_pushes src.inner.law.toFiniteLaw) (P0 : Set _))

/-- Original pair-law mass with slack above 49/64+τ proves precisely
the manuscript's quantified deletion-retention condition. -/
theorem ownerPair_retention
    (P0 : Finset (src.inner.Label × src.inner.Label)) (a τ : ℝ)
    (ha : a ≤ (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw).prob
      (· ∈ (P0 : Set _)))
    (hmargin : 49/64+τ < a) :
    ∀ P' : Finset (src.inner.Label × src.inner.Label), P' ⊆ P0 →
      SourceSupportStep.mass
        (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw) (P0 \ P') < τ →
      (49/64 : ℝ) ≤
        (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw).prob
          (· ∈ (P' : Set _)) := by
  classical
  intro P' hsub hloss
  have hsplit : SourceSupportStep.mass
        (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw) (P0 \ P') +
      SourceSupportStep.mass
        (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw) P' =
      SourceSupportStep.mass
        (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw) P0 := by
    unfold SourceSupportStep.mass FiniteLaw.prob
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : z ∈ P'
    · have hp := hsub hz
      simp [hz, hp]
    · by_cases hp : z ∈ P0 <;> simp [hz, hp]
  change _ +
      (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw).prob
        (· ∈ (P' : Set _)) =
      (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw).prob
        (· ∈ (P0 : Set _)) at hsplit
  linarith

#print axioms ownerPairInput_labels
#print axioms ownerPairFirst_mass
#print axioms ownerPair_retention

end CurrentAdditive.DeterministicIndexedMatrix.Sources
