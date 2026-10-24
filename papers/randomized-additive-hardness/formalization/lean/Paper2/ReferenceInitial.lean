import Paper2.SourceProjectionRetention

/-!
# Initial reference-copy supports in the first source interlace

Frozen v12, Section 5, lines 193--201 and 250--260. These are slices of the
actual retained first-interlace row event. Their probabilities use the fixed
normalized unrestricted-tag law, not a law conditioned after deletion.
-/

namespace Paper2.ReferenceInitial

open SourceMatrix SourceLaws

variable {Y : Type*} [Fintype Y] {q₁ q₂ s w : ℕ} [NeZero q₂]

/-- Original unrestricted rows retained in coordinate `i`. -/
def referenceSupport
    (R0 : Set (Fin w × TaggedColumn q₁ q₂ s Y)) (i : Fin w) :
    Set (RawColumn q₁ q₂ s Y) :=
  {Z | (i, .unrestricted Z) ∈ R0}

/-- The exact law on original first-interlace rows. -/
noncomputable def firstRowLaw (ν : PositiveRationalLaw Y) (hw : 0 < w) :
    FiniteLaw (Fin w × TaggedColumn q₁ q₂ s Y) := by
  letI : Nonempty (Fin w) := Fin.pos_iff_nonempty.mp hw
  exact ((PositiveRationalLaw.uniform (Fin w)).prod (taggedLaw ν q₁ q₂ s)).toFiniteLaw

theorem firstRowLaw_prob (ν : PositiveRationalLaw Y) (hw : 0 < w)
    (E : Fin w → TaggedColumn q₁ q₂ s Y → Prop) :
    (firstRowLaw ν hw).prob (fun p => E p.1 p.2) =
      (∑ i : Fin w, (taggedLaw ν q₁ q₂ s).toFiniteLaw.prob (E i)) / w := by
  letI : Nonempty (Fin w) := Fin.pos_iff_nonempty.mp hw
  rw [firstRowLaw, PositiveRationalLaw.toFiniteLaw_prod, FiniteLaw.prod_prob]
  simp only [PositiveRationalLaw.toFiniteLaw, PositiveRationalLaw.uniform,
    Fintype.card_fin, Rat.cast_inv, Rat.cast_natCast]
  rw [← Finset.mul_sum]
  ring

private theorem unrestricted_loss_le_tagged (ν : PositiveRationalLaw Y)
    (E : TaggedColumn q₁ q₂ s Y → Prop) :
    (127 / 128 : ℝ) *
      (rawLaw ν q₁ q₂ s).toFiniteLaw.prob (fun Z => E (.unrestricted Z)) ≤
      (taggedLaw ν q₁ q₂ s).toFiniteLaw.prob E := by
  rw [tagged_prob]
  have hf := (fixedTailLaw ν q₁ q₂ s).toFiniteLaw.prob_nonneg
    (fun js => E (.fixedTail js))
  have hd := (outerLaw ν q₁ q₂ s).toFiniteLaw.prob_nonneg
    (fun j => E (.diagonal j))
  linarith

/-- Total normalized reference-copy loss is charged to the actual retained
first-interlace row law, with the exact dominant-tag weight `g=127/128`. -/
theorem reference_defect_sum_le (ν : PositiveRationalLaw Y) (hw : 0 < w)
    (R0 : Set (Fin w × TaggedColumn q₁ q₂ s Y)) (η : ℝ)
    (hR0 : 1 - η / (16 * w) ≤ (firstRowLaw ν hw).prob (· ∈ R0)) :
    (∑ i : Fin w, (1 - (rawLaw ν q₁ q₂ s).toFiniteLaw.prob
      (· ∈ referenceSupport R0 i))) ≤ η / (16 * (127 / 128 : ℝ)) := by
  let μΩ := (rawLaw ν q₁ q₂ s).toFiniteLaw
  let μT := (taggedLaw ν q₁ q₂ s).toFiniteLaw
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hcomp : (firstRowLaw ν hw).prob (fun p => p ∉ R0) ≤ η / (16 * w) := by
    rw [SourceProjectionRetention.probability_complement]
    linarith
  have hsum :
      (127 / 128 : ℝ) *
        (∑ i : Fin w, μΩ.prob (fun Z => (i, .unrestricted Z) ∉ R0)) ≤
      (∑ i : Fin w, μT.prob (fun Z => (i, Z) ∉ R0)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => unrestricted_loss_le_tagged ν
      (fun Z => (i, Z) ∉ R0))
  have hsum' : (∑ i : Fin w, μT.prob (fun Z => (i, Z) ∉ R0)) ≤ η / 16 := by
    rw [firstRowLaw_prob ν hw (fun i Z => (i, Z) ∉ R0)] at hcomp
    rw [show η / (16 * (w : ℝ)) = (η / 16) / w by ring] at hcomp
    have hm := (div_le_div_iff₀ hwR hwR).mp hcomp
    nlinarith
  have hdef (i : Fin w) :
      1 - μΩ.prob (· ∈ referenceSupport R0 i) =
        μΩ.prob (fun Z => (i, .unrestricted Z) ∉ R0) := by
    rw [SourceProjectionRetention.probability_complement]
    rfl
  have hg : (0 : ℝ) < 127 / 128 := by norm_num
  have hbound : (∑ i : Fin w, μΩ.prob (fun Z => (i, .unrestricted Z) ∉ R0)) ≤
      η / (16 * (127 / 128 : ℝ)) := by
    calc
      _ ≤ (η / 16) / (127 / 128 : ℝ) :=
        (le_div_iff₀ hg).mpr (by simpa only [mul_comm] using hsum.trans hsum')
      _ = _ := by ring
  calc
    (Finset.sum Finset.univ (fun i : Fin w =>
      1 - (rawLaw ν q₁ q₂ s).toFiniteLaw.prob
        (fun Z => Z ∈ referenceSupport R0 i))) =
        (∑ i : Fin w, μΩ.prob (fun Z => (i, .unrestricted Z) ∉ R0)) := by
          apply Finset.sum_congr rfl
          intro i _
          exact hdef i
    _ ≤ _ := hbound

/-- No one original copy loses more reference mass than the total loss. -/
theorem reference_defect_le (ν : PositiveRationalLaw Y) (hw : 0 < w)
    (R0 : Set (Fin w × TaggedColumn q₁ q₂ s Y)) (η : ℝ)
    (hR0 : 1 - η / (16 * w) ≤ (firstRowLaw ν hw).prob (· ∈ R0))
    (i : Fin w) :
    1 - (rawLaw ν q₁ q₂ s).toFiniteLaw.prob (· ∈ referenceSupport R0 i) ≤
      η / (16 * (127 / 128 : ℝ)) := by
  have hsum := reference_defect_sum_le ν hw R0 η hR0
  have hnonneg (j : Fin w) :
      0 ≤ 1 - (rawLaw ν q₁ q₂ s).toFiniteLaw.prob
        (fun Z => Z ∈ referenceSupport R0 j) := by
    have hle := (rawLaw ν q₁ q₂ s).toFiniteLaw.prob_le_one
      (fun Z => Z ∈ referenceSupport R0 j)
    linarith
  have hle := Finset.single_le_sum
    (f := fun j : Fin w => 1 - (rawLaw ν q₁ q₂ s).toFiniteLaw.prob
      (fun Z => Z ∈ referenceSupport R0 j))
    (fun j _ => hnonneg j) (Finset.mem_univ i)
  exact hle.trans hsum

/-- The manuscript's strict initialization margin gives every copy the
threshold needed at depth zero, before excluding exceptional coordinates. -/
theorem reference_initial_floor (ν : PositiveRationalLaw Y) (hw : 0 < w)
    (R0 : Set (Fin w × TaggedColumn q₁ q₂ s Y)) (η x : ℝ)
    (hR0 : 1 - η / (16 * w) ≤ (firstRowLaw ν hw).prob (· ∈ R0))
    (hmargin : 2 * w * x + η / (16 * (127 / 128 : ℝ)) < 1)
    (i : Fin w) :
    2 * w * x ≤ (rawLaw ν q₁ q₂ s).toFiniteLaw.prob
      (· ∈ referenceSupport R0 i) := by
  have hdef := reference_defect_le ν hw R0 η hR0 i
  linarith

#print axioms Paper2.ReferenceInitial.firstRowLaw_prob
#print axioms Paper2.ReferenceInitial.reference_defect_sum_le
#print axioms Paper2.ReferenceInitial.reference_defect_le
#print axioms Paper2.ReferenceInitial.reference_initial_floor

end Paper2.ReferenceInitial
