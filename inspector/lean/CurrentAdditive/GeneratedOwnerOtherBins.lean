import CurrentAdditive.GeneratedOwnerPairAveraging

/-! Source Appendix I:683--685, selector mass in each non-distinguished
template bin after a bounded singleton projection loss. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix

variable {G V Aux X Y : Type*}
  [Fintype G] [Fintype V] [Fintype Aux]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  [DecidableEq G] [DecidableEq V] [DecidableEq Aux]
  {D q₁ q₂ s : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  (μI : PositiveRationalLaw (G × (V ⊕ Aux)))

private theorem template_bin_prob (b : Fin s)
    (Z : Set src.inner.Label) :
    (rowLaw src μI).toFiniteLaw.prob
      (fun k => ∃ z ∈ Z, k = .inl (b,z)) =
      (255 / 256 : ℝ) * (s : ℝ)⁻¹ *
        src.inner.law.toFiniteLaw.prob (· ∈ Z) := by
  classical
  simp [FiniteLaw.prob, rowLaw, templateRowLaw,
    PositiveRationalLaw.toFiniteLaw, PositiveRationalLaw.prod,
    PositiveRationalLaw.uniform, Fintype.sum_sum_type,
    Fintype.sum_prod_type, Fintype.card_fin, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : z ∈ Z
  · simp [hz]; ring
  · simp [hz]

/-- An owner-coordinate singleton image can lose at most the stated
fraction of the full indexed row law. Each fixed template bin therefore
retains almost all of its original selector mass. -/
theorem owner_other_bin_mass_of_singleton_loss
    {w : ℕ} (streams : InternalStreams src μI w)
    (U : Set (InternalLabel src streams)) (i : Fin w)
    (η : ℝ)
    (hdelete : (rowLaw src μI).toFiniteLaw.prob
      (fun k => k ∉ (InternalStreams.decode src streams · i) '' U) ≤ η/2)
    (b : Fin s) :
    1 - η * (s : ℝ) / (2 * (255/256 : ℝ)) ≤
      src.inner.law.toFiniteLaw.prob
        (fun z => ∃ t ∈ U,
          streams.metadataStream.decode t.1 i = .inl b ∧
          streams.selectorStream.decode t.2.2 i = z) := by
  classical
  let χ := (rowLaw src μI).toFiniteLaw
  let B : Set (Row (I := G × (V ⊕ Aux)) src) :=
    (InternalStreams.decode src streams · i) '' U
  let Z : Set src.inner.Label := fun z => ∃ t ∈ U,
    streams.metadataStream.decode t.1 i = .inl b ∧
    streams.selectorStream.decode t.2.2 i = z
  let Bin : Set (Row (I := G × (V ⊕ Aux)) src) :=
    fun k => ∃ z, k = .inl (b,z)
  let Zevent : Set (Row (I := G × (V ⊕ Aux)) src) :=
    fun k => ∃ z ∈ Z, k = .inl (b,z)
  have hbin : χ.prob (· ∈ Bin) = (255/256 : ℝ) * (s : ℝ)⁻¹ := by
    have h := template_bin_prob src μI b Set.univ
    simpa [χ, Bin] using h
  have hZ : χ.prob (· ∈ Zevent) =
      (255/256 : ℝ) * (s : ℝ)⁻¹ *
        src.inner.law.toFiniteLaw.prob (· ∈ Z) := by
    exact template_bin_prob src μI b Z
  have hsub : (fun k => k ∈ Bin ∧ k ∈ B) ≤ (· ∈ Zevent) := by
    intro k ⟨⟨z, hk⟩, ⟨t, ht, htk⟩⟩
    have hd : InternalStreams.decode src streams t i = .inl (b,z) :=
      htk.trans hk
    unfold InternalStreams.decode at hd
    cases hm : streams.metadataStream.decode t.1 i with
    | inl p =>
        simp only [hm] at hd
        have hp := (Prod.mk.inj (Sum.inl.inj hd)).1
        have hz := (Prod.mk.inj (Sum.inl.inj hd)).2
        exact ⟨z, ⟨t, ht, hp ▸ hm, hz⟩, hk⟩
    | inr v => simp only [hm] at hd; cases hd
  have hsplit : χ.prob (· ∈ Bin) ≤
      χ.prob (fun k => k ∈ Bin ∧ k ∈ B) +
        χ.prob (fun k => k ∉ B) := by
    unfold FiniteLaw.prob
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro k _
    by_cases hbin' : k ∈ Bin <;> by_cases hb : k ∈ B <;>
      simp [hbin', hb, χ.nonneg k]
  have hret := χ.prob_mono hsub
  have hbound : (255/256 : ℝ) * (s : ℝ)⁻¹ ≤
      (255/256 : ℝ) * (s : ℝ)⁻¹ *
        src.inner.law.toFiniteLaw.prob (· ∈ Z) + η/2 := by
    rw [hbin] at hsplit
    rw [hZ] at hret
    exact le_trans hsplit (add_le_add hret hdelete)
  have hspos : (0 : ℝ) < s := by exact_mod_cast (NeZero.pos s)
  dsimp [Z] at hbound
  field_simp at hbound ⊢
  change (255 : ℝ) * 2 ≤
    (255 * src.inner.law.toFiniteLaw.prob
      (fun z => ∃ t ∈ U,
        streams.metadataStream.decode t.1 i = .inl b ∧
        streams.selectorStream.decode t.2.2 i = z)) * 2 +
      256 * (s : ℝ) * η at hbound
  nlinarith

#print axioms owner_other_bin_mass_of_singleton_loss

/-- This is the exact all-other-bin input of the owner-to-owner W theorem.
It follows from one original-law singleton loss and the source's numeric
gap, uniformly in whichever distinguished bin averaging selects. -/
theorem owner_other_bins_from_singleton_loss
    {w : ℕ} (streams : InternalStreams src μI w)
    (U : Set (InternalLabel src streams)) (i : Fin w)
    (η x : ℝ)
    (hdelete : (rowLaw src μI).toFiniteLaw.prob
      (fun k => k ∉ (InternalStreams.decode src streams · i) '' U) ≤ η/2)
    (hfloor : 2*s*x ≤ 1 - η * (s : ℝ) / (2 * (255/256 : ℝ))) :
    ∀ p b : Fin s, b ≠ p →
      2*s*x ≤ src.inner.law.toFiniteLaw.prob
        (fun z => ∃ t ∈ U,
          streams.metadataStream.decode t.1 i = .inl b ∧
          streams.selectorStream.decode t.2.2 i = z) := by
  intro _ b _
  exact hfloor.trans
    (owner_other_bin_mass_of_singleton_loss src μI streams U i η hdelete b)

#print axioms owner_other_bins_from_singleton_loss

end CurrentAdditive.DeterministicIndexedMatrix.Sources
