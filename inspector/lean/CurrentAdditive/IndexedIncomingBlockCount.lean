import CurrentAdditive.IndexedIncomingFibres

/-! Appendix I `det:incoming`: count literal `(outer position, inner bin)`
blocks in the original indexed source. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2
open scoped BigOperators

variable {X Y : Type*} [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

/-- Labelled heavy fibres retain both coordinates, which prevents collisions
between different original outer positions. -/
noncomputable def heavyProtectedBlocks (w : ℕ)
    (R : Set (Fin w × Column src)) (V : Finset (Fin w))
    (b : Bool) (p : Fin w → Fin s) (δ : ℝ) :
    Finset (Σ _ : Fin w, Fin q₂) :=
  V.sigma (fun i => heavyProtectedBins src w R b i (p i) δ)

/-- The same blocks as coordinates of the actual flattened selector stream. -/
noncomputable def flatHeavyProtectedBlocks (w : ℕ)
    (R : Set (Fin w × Column src)) (V : Finset (Fin w))
    (b : Bool) (p : Fin w → Fin s) (δ : ℝ) :
    Finset (Fin w × Fin q₂) :=
  (heavyProtectedBlocks src w R V b p δ).image
    (fun z => (z.1, z.2))

theorem flatHeavyProtectedBlocks_card (w : ℕ)
    (R : Set (Fin w × Column src)) (V : Finset (Fin w))
    (b : Bool) (p : Fin w → Fin s) (δ : ℝ) :
    (flatHeavyProtectedBlocks src w R V b p δ).card =
      (heavyProtectedBlocks src w R V b p δ).card := by
  apply Finset.card_image_of_injective
  intro a b h
  cases a with | mk i α =>
    cases b with | mk j β =>
      cases h
      rfl

theorem mem_flatHeavyProtectedBlocks (w : ℕ)
    (R : Set (Fin w × Column src)) (V : Finset (Fin w))
    (b : Bool) (p : Fin w → Fin s) (δ : ℝ)
    (i : Fin w) (α : Fin q₂) :
    (i, α) ∈ flatHeavyProtectedBlocks src w R V b p δ ↔
      i ∈ V ∧ α ∈ heavyProtectedBins src w R b i (p i) δ := by
  classical
  constructor
  · intro h
    obtain ⟨z, hz, hza⟩ := Finset.mem_image.mp h
    cases z with
    | mk j β =>
      have hij : j = i := congrArg Prod.fst hza
      have hβα : β = α := congrArg Prod.snd hza
      subst j
      subst β
      exact Finset.mem_sigma.mp hz
  · rintro ⟨hi, hα⟩
    apply Finset.mem_image.mpr
    exact ⟨⟨i, α⟩, Finset.mem_sigma.mpr ⟨hi, hα⟩, rfl⟩

theorem heavyProtectedBlocks_card (w : ℕ)
    (R : Set (Fin w × Column src)) (V : Finset (Fin w))
    (b : Bool) (p : Fin w → Fin s) (δ : ℝ) :
    (heavyProtectedBlocks src w R V b p δ).card =
      ∑ i ∈ V, (heavyProtectedBins src w R b i (p i) δ).card := by
  simp [heavyProtectedBlocks, Finset.card_sigma]

/-- Density grouping and the exact `J₂` product law give more than the
manuscript's `K₀=2sκq₂` distinct original flattened blocks. -/
theorem heavy_protected_blocks_many (w s₀ κ : ℕ)
    (R : Set (Fin w × Column src)) (I V : Finset (Fin w))
    (b : Bool) (p : Fin w → Fin s) (δ : ℝ)
    (hD : 1 ≤ D) (hV : V.Nonempty) (hVI : V ⊆ I) (hδ : 0 < δ)
    (hrow : ∀ i ∈ V, δ / 2 < protectedDensity src w R I b i)
    (hsize : 16 * (s₀ : ℝ) * κ ≤ (V.card : ℝ) * δ) :
    2 * s₀ * κ * q₂ < (heavyProtectedBlocks src w R V b p δ).card := by
  have hfibre (i : Fin w) (hi : i ∈ V) :
      δ * q₂ / 4 < (heavyProtectedBins src w R b i (p i) δ).card := by
    have hmass := protected_image_mass_ge src w R I b i (hVI hi) (p i) hD
    apply protected_heavy_fibres src w R b i (p i) δ hδ.le
    exact lt_of_lt_of_le (hrow i hi) hmass
  have hsum : (∑ i ∈ V, δ * (q₂ : ℝ) / 4) <
      ∑ i ∈ V, ((heavyProtectedBins src w R b i (p i) δ).card : ℝ) := by
    exact Finset.sum_lt_sum_of_nonempty hV (fun i hi => hfibre i hi)
  have hsum' : (V.card : ℝ) * (δ * q₂ / 4) <
      ((heavyProtectedBlocks src w R V b p δ).card : ℝ) := by
    simp only [Finset.sum_const_zero, Finset.sum_const, nsmul_eq_mul] at hsum
    rw [heavyProtectedBlocks_card]
    exact_mod_cast hsum
  have hq : (0 : ℝ) ≤ q₂ := Nat.cast_nonneg _
  have hsmall : 8 * (s₀ : ℝ) * κ ≤ (V.card : ℝ) * δ := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ s₀ by positivity)
      (show (0 : ℝ) ≤ κ by positivity)]
  have hK : ((2 * s₀ * κ * q₂ : ℕ) : ℝ) ≤
      (V.card : ℝ) * (δ * q₂ / 4) := by
    calc
      ((2 * s₀ * κ * q₂ : ℕ) : ℝ) =
          (8 * (s₀ : ℝ) * κ) * ((q₂ : ℝ) / 4) := by push_cast; ring
      _ ≤ ((V.card : ℝ) * δ) * ((q₂ : ℝ) / 4) :=
        mul_le_mul_of_nonneg_right hsmall (by positivity)
      _ = (V.card : ℝ) * (δ * q₂ / 4) := by ring
  exact_mod_cast lt_of_le_of_lt hK hsum'

/-- Delete exceptional flattened coordinates from the *original* selected
blocks and keep `K₀/2+1` genuine coordinates. -/
theorem select_flat_protected_blocks (w s₀ κ : ℕ)
    (R : Set (Fin w × Column src)) (V : Finset (Fin w))
    (b : Bool) (p : Fin w → Fin s) (δ : ℝ)
    (E : Finset (Fin w × Fin q₂))
    (hκ : 1 ≤ κ) (hE : E.card ≤ s₀ * q₂)
    (hmany : 2 * s₀ * κ * q₂ <
      (flatHeavyProtectedBlocks src w R V b p δ).card) :
    ∃ Q : Finset (Fin w × Fin q₂),
      Q ⊆ flatHeavyProtectedBlocks src w R V b p δ \ E ∧
      Q.card = s₀ * κ * q₂ + 1 := by
  classical
  have hdiff : (flatHeavyProtectedBlocks src w R V b p δ \ E).card + E.card ≥
      (flatHeavyProtectedBlocks src w R V b p δ).card := by
    exact Finset.card_le_card_sdiff_add_card
  have hneed : s₀ * κ * q₂ + 1 ≤
      (flatHeavyProtectedBlocks src w R V b p δ \ E).card := by
    have hκ' : s₀ * q₂ ≤ s₀ * κ * q₂ := by
      nlinarith
    have hmany' : 2 * (s₀ * κ * q₂) <
        (flatHeavyProtectedBlocks src w R V b p δ).card := by
      convert hmany using 1 <;> ring
    omega
  obtain ⟨Q, hQ, hcard⟩ := Finset.exists_subset_card_eq hneed
  exact ⟨Q, hQ, hcard⟩

#print axioms heavy_protected_blocks_many
#print axioms select_flat_protected_blocks

end CurrentAdditive.DeterministicIndexedMatrix.Sources
