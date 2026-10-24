import Paper2.ProtectedIncomingRows
import Paper2.ForeignOwnerMass

/-!
# Actual incoming protected densities

Frozen v12 `res:incoming`, lines 330--351. Start with the literal weighted
receipts from an arbitrary collection of original coordinates. Choose a
protected type and obtain its dyadic group; do not assume a heavy type or
replace the actual incoming population by a density certificate.
-/

namespace Paper2.ProtectedIncomingDensity

open SourceMatrix SourceLaws SourceProfileParameters ProtectedIncomingRows
open scoped BigOperators

variable {Y : Type*} [Fintype Y]

local instance (L : ℕ) : NeZero (outerWidth L) := ⟨by
  unfold outerWidth
  positivity⟩

/-- The two actual conditional densities, set to zero outside the chosen
collection. `false` is fixed-tail, `true` is diagonal. -/
noncomputable def density (ν : PositiveRationalLaw Y) (L w : ℕ)
    (R : Set (Fin w × TaggedColumn (width L - 2) (outerWidth L) (width L) Y))
    (I : Finset (Fin w)) (b : Bool) (i : Fin w) : ℝ := by
  classical
  exact if i ∈ I then
    if b then
      (outerLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw.prob
        (· ∈ diagonalEvent R i)
    else
      (fixedTailLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw.prob
        (· ∈ fixedEvent R i)
    else 0

theorem density_nonneg (ν : PositiveRationalLaw Y) (L w : ℕ)
    (R : Set (Fin w × TaggedColumn (width L - 2) (outerWidth L) (width L) Y))
    (I : Finset (Fin w)) (b : Bool) (i : Fin w) :
    0 ≤ density ν L w R I b i := by
  classical
  unfold density
  split_ifs <;> first | exact FiniteLaw.prob_nonneg _ _ | positivity

theorem density_le_one (ν : PositiveRationalLaw Y) (L w : ℕ)
    (R : Set (Fin w × TaggedColumn (width L - 2) (outerWidth L) (width L) Y))
    (I : Finset (Fin w)) (b : Bool) (i : Fin w) :
    density ν L w R I b i ≤ 1 := by
  classical
  unfold density
  split_ifs <;> first | exact FiniteLaw.prob_le_one _ _ | norm_num

theorem protected_sum_eq (ν : PositiveRationalLaw Y) (L w : ℕ)
    (R : Set (Fin w × TaggedColumn (width L - 2) (outerWidth L) (width L) Y))
    (I : Finset (Fin w)) :
    (∑ i ∈ I, ForeignOwnerMass.protectedMass ν L w i R) =
      (1 / 256 : ℝ) * (∑ i, density ν L w R I false i) +
      (1 / 256 : ℝ) * (∑ i, density ν L w R I true i) := by
  classical
  dsimp [density, ForeignOwnerMass.protectedMass, fixedEvent, diagonalEvent]
  simp [mul_add, Finset.mul_sum, Finset.sum_add_distrib] <;> rfl

/-- If the displayed incoming bound fails, one original protected type has
the large normalized density sum used by the source's grouping argument. -/
theorem exists_heavy_type (ν : PositiveRationalLaw Y) (L w r B κ : ℕ)
    (R : Set (Fin w × TaggedColumn (width L - 2) (outerWidth L) (width L) Y))
    (I : Finset (Fin w))
    (hmass : 1024 * (1 / 256 : ℝ) * B * (r + 2) * width L * κ ≤
      ∑ i ∈ I, ForeignOwnerMass.protectedMass ν L w i R) :
    ∃ b : Bool, 512 * (B : ℝ) * (r + 2) * width L * κ ≤
      ∑ i, density ν L w R I b i := by
  have heq := protected_sum_eq ν L w R I
  by_cases h : 512 * (B : ℝ) * (r + 2) * width L * κ ≤
      ∑ i, density ν L w R I false i
  · exact ⟨false, h⟩
  · refine ⟨true, ?_⟩
    push Not at h
    nlinarith [heq]

/-- The group consists of contributing original coordinates: zero padding
outside the collection cannot create positive-density members. -/
theorem group_subset (ν : PositiveRationalLaw Y) (L w r : ℕ)
    (R : Set (Fin w × TaggedColumn (width L - 2) (outerWidth L) (width L) Y))
    (I : Finset (Fin w)) (b : Bool) (D : ℝ) (j : Fin (r + 2)) :
    ProtectedDensityGroups.dyadicGroup (density ν L w R I b) D j ⊆ I := by
  classical
  intro i hi
  by_contra hn
  have hz : density ν L w R I b i = 0 := by simp [density, hn]
  have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ (j.val + 1) := by positivity
  have hmem := (Finset.mem_filter.mp hi).2
  rw [hz] at hmem
  linarith [hmem.2.1]

set_option maxRecDepth 4096 in
/-- Actual receipt failure supplies the complete dyadic grouping package,
including membership in the original contributing collection. -/
theorem actual_density_group (ν : PositiveRationalLaw Y) (L w r B κ : ℕ)
    (R : Set (Fin w × TaggedColumn (width L - 2) (outerWidth L) (width L) Y))
    (I : Finset (Fin w)) (hw : w = 2 ^ r) (hB : 0 < B) (hκ : 0 < κ)
    (hmass : 1024 * (1 / 256 : ℝ) * B * (r + 2) * width L * κ ≤
      ∑ i ∈ I, ForeignOwnerMass.protectedMass ν L w i R) :
    ∃ b : Bool,
      let d := density ν L w R I b
      let D : ℝ := ∑ i, d i
      512 * (B : ℝ) * (r + 2) * width L * κ ≤ D ∧ 1 ≤ D ∧
      ∃ (j : Fin (r + 2)) (k : ℕ),
        let δ : ℝ := (1 / 2 : ℝ) ^ j.val
        let V := ProtectedDensityGroups.dyadicGroup d D j
        let u : ℕ := 2 ^ k
        V ⊆ I ∧ k ≤ r ∧ 0 < δ ∧ δ ≤ 1 ∧
          D / (2 * (w : ℝ)) ≤ δ ∧
          (∀ i ∈ V, δ / 2 < d i ∧ d i ≤ δ) ∧
          D / (2 * (r + 2 : ℝ)) ≤ (V.card : ℝ) * δ ∧
          16 * (width L : ℝ) * κ ≤ (u : ℝ) * δ ∧
          (u : ℝ) * δ < 32 * (width L : ℝ) * κ ∧
          u * B < V.card ∧ u ≤ w := by
  obtain ⟨b, hlarge⟩ := exists_heavy_type ν L w r B κ R I hmass
  have hs : 0 < width L := by unfold width; positivity
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hs1 : (1 : ℝ) ≤ width L := by exact_mod_cast hs
  have hκ1 : (1 : ℝ) ≤ κ := by exact_mod_cast hκ
  have hr1 : (1 : ℝ) ≤ (r : ℝ) + 2 := by
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    linarith
  have hprod : (1 : ℝ) ≤ (B : ℝ) * (r + 2) * width L * κ := by
    have hbr : (1 : ℝ) * 1 ≤ (B : ℝ) * (r + 2) :=
      mul_le_mul hB1 hr1 (by norm_num) (Nat.cast_nonneg B)
    have hbrs : (1 : ℝ) * 1 * 1 ≤ (B : ℝ) * (r + 2) * width L :=
      mul_le_mul hbr hs1 (by norm_num)
        (le_trans (by norm_num : (0 : ℝ) ≤ 1 * 1) hbr)
    have hbrsk : (1 : ℝ) * 1 * 1 * 1 ≤ (B : ℝ) * (r + 2) * width L * κ :=
      mul_le_mul hbrs hκ1 (by norm_num)
        (le_trans (by norm_num : (0 : ℝ) ≤ 1 * 1 * 1) hbrs)
    simpa only [one_mul] using hbrsk
  have hDone : (1 : ℝ) ≤ ∑ i, density ν L w R I b i := by
    calc
      (1 : ℝ) ≤ 512 := by norm_num
      _ ≤ 512 * ((B : ℝ) * (r + 2) * width L * κ) :=
        le_mul_of_one_le_right (by norm_num) hprod
      _ = 512 * (B : ℝ) * (r + 2) * width L * κ := by ring
      _ ≤ ∑ i, density ν L w R I b i := hlarge
  obtain ⟨j, k, hgroup⟩ := ProtectedDensityGroups.density_group_and_size
    (density ν L w R I b) hw (density_nonneg ν L w R I b)
    (density_le_one ν L w R I b) (width L) κ B hs hκ hB
    (∑ i, density ν L w R I b i) rfl hlarge
  exact ⟨b, hlarge, hDone, j, k, group_subset ν L w r R I b _ j, hgroup⟩

end Paper2.ProtectedIncomingDensity

#print axioms Paper2.ProtectedIncomingDensity.protected_sum_eq
#print axioms Paper2.ProtectedIncomingDensity.exists_heavy_type
#print axioms Paper2.ProtectedIncomingDensity.group_subset
#print axioms Paper2.ProtectedIncomingDensity.actual_density_group
