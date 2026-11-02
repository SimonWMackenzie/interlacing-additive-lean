import Mathlib

/-!
Source: `papers/randomized-additive-hardness/versions/2026-10-12-proof-exposition-v27/
source/appendices/H-deterministic-core.tex`, proof of `det:conditioning`, lines 201--242.

This file proves only the finite covering step. The analytic moment estimate that
bounds the size of a disjoint bad family is a separate premise below. The bad
family must exclude the empty set: the two empty marginals are the same point
mass, hence their total variation distance is zero.
-/

namespace CurrentAdditive

/-- If bad means that a nonnegative threshold is exceeded by a discrepancy,
and the discrepancy of the empty projection is zero, then no bad set is empty.
For the manuscript discrepancy, the latter equality is TV of the two empty
marginals, both point masses on the unique empty tuple. -/
theorem bad_family_nonempty_of_zero_empty
    {α : Type*} [DecidableEq α] (bad : Finset (Finset α))
    (discrepancy : Finset α → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) (hzero : discrepancy ∅ = 0)
    (hbad : ∀ J ∈ bad, ε < discrepancy J) :
    ∀ J ∈ bad, J.Nonempty := by
  intro J hJ
  by_contra h
  have hJempty : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  have hpos := hbad J hJ
  simp [hJempty, hzero] at hpos
  exact (not_lt_of_ge hε) hpos

/-- Choose a cardinal-maximal pairwise-disjoint subfamily and take its union.
Every bad set meets this union. This theorem contains no moment estimate. -/
theorem finite_exceptional_cover_core
    {α : Type*} [DecidableEq α] (bad : Finset (Finset α))
    (hnonempty : ∀ J ∈ bad, J.Nonempty)
    (hsize : ∀ J ∈ bad, J.card ≤ 8) :
    ∃ (F : Finset (Finset α)) (E : Finset α),
      F ⊆ bad ∧ (F : Set (Finset α)).Pairwise Disjoint ∧
      E.card ≤ F.card * 8 ∧ ∀ J ∈ bad, ¬ Disjoint J E := by
  classical
  let admissible : Finset (Finset (Finset α)) :=
    bad.powerset.filter (fun F => (F : Set (Finset α)).Pairwise Disjoint)
  have hempty : ∅ ∈ admissible := by
    simp [admissible, Set.Pairwise]
  obtain ⟨F, hmax⟩ :=
    admissible.exists_maximalFor Finset.card ⟨∅, hempty⟩
  have hF : F ⊆ bad ∧ (F : Set (Finset α)).Pairwise Disjoint := by
    simpa [admissible] using hmax.1
  refine ⟨F, F.biUnion id, hF.1, hF.2, ?_, ?_⟩
  · exact Finset.card_biUnion_le_card_mul F id 8 (by
      intro J hJ
      exact hsize J (hF.1 hJ))
  · intro J hJ hdisj
    have hJnot : J ∉ F := by
      intro hJF
      obtain ⟨x, hx⟩ := hnonempty J hJ
      have hxE : x ∈ F.biUnion id := Finset.mem_biUnion.mpr ⟨J, hJF, hx⟩
      exact (Finset.disjoint_left.mp hdisj hx) hxE
    have hnew : ((insert J F : Finset (Finset α)) : Set (Finset α)).Pairwise Disjoint := by
      rw [Finset.coe_insert, Set.pairwise_insert]
      refine ⟨hF.2, ?_⟩
      intro K hKF _
      have hJK : Disjoint J K := by
        apply Finset.disjoint_left.mpr
        intro x hxJ hxK
        exact (Finset.disjoint_left.mp hdisj hxJ)
          (Finset.mem_biUnion.mpr ⟨K, hKF, hxK⟩)
      exact ⟨hJK, hJK.symm⟩
    have hnewmem : insert J F ∈ admissible := by
      simp only [admissible, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.insert_subset_iff.mpr ⟨hJ, hF.1⟩, hnew⟩
    have hFsub : F ⊆ insert J F := Finset.subset_insert J F
    have hnewcard : (insert J F).card ≤ F.card :=
      hmax.2 hnewmem (Finset.card_le_card hFsub)
    rw [Finset.card_insert_of_notMem hJnot] at hnewcard
    omega

/-- A natural-number packing bound gives the manuscript's factor-eight
exceptional-set bound. -/
theorem finite_exceptional_cover
    {α : Type*} [DecidableEq α] (bad : Finset (Finset α)) (M : ℕ)
    (hnonempty : ∀ J ∈ bad, J.Nonempty)
    (hsize : ∀ J ∈ bad, J.card ≤ 8)
    (hpacking : ∀ F : Finset (Finset α), F ⊆ bad →
      (F : Set (Finset α)).Pairwise Disjoint → F.card ≤ M) :
    ∃ E : Finset α, E.card ≤ 8 * M ∧
      ∀ J ∈ bad, ¬ Disjoint J E := by
  obtain ⟨F, E, hFB, hpair, hcard, hcover⟩ :=
    finite_exceptional_cover_core bad hnonempty hsize
  refine ⟨E, ?_, hcover⟩
  calc
    E.card ≤ F.card * 8 := hcard
    _ ≤ M * 8 := Nat.mul_le_mul_right 8 (hpacking F hFB hpair)
    _ = 8 * M := Nat.mul_comm _ _

/-- The same cover accepts a real-valued bound on disjoint bad families, as
provided by the even-moment argument. A strict real packing bound implies this
hypothesis by `le_of_lt`. -/
theorem finite_exceptional_cover_real
    {α : Type*} [DecidableEq α] (bad : Finset (Finset α)) (B : ℝ)
    (hnonempty : ∀ J ∈ bad, J.Nonempty)
    (hsize : ∀ J ∈ bad, J.card ≤ 8)
    (hpacking : ∀ F : Finset (Finset α), F ⊆ bad →
      (F : Set (Finset α)).Pairwise Disjoint → (F.card : ℝ) ≤ B) :
    ∃ E : Finset α, (E.card : ℝ) ≤ 8 * B ∧
      ∀ J ∈ bad, ¬ Disjoint J E := by
  obtain ⟨F, E, hFB, hpair, hcard, hcover⟩ :=
    finite_exceptional_cover_core bad hnonempty hsize
  refine ⟨E, ?_, hcover⟩
  have hcardR : (E.card : ℝ) ≤ (F.card : ℝ) * 8 := by exact_mod_cast hcard
  have hpack := hpacking F hFB hpair
  nlinarith

/-- The precise integer bound used in `det:exception-count`: if the analytic
argument bounds the cardinality of every disjoint bad family by a real `B`,
the exceptional set has at most `8 * ceil B` coordinates. -/
theorem finite_exceptional_cover_ceiling
    {α : Type*} [DecidableEq α] (bad : Finset (Finset α)) (B : ℝ)
    (hnonempty : ∀ J ∈ bad, J.Nonempty)
    (hsize : ∀ J ∈ bad, J.card ≤ 8)
    (hpacking : ∀ F : Finset (Finset α), F ⊆ bad →
      (F : Set (Finset α)).Pairwise Disjoint → (F.card : ℝ) ≤ B) :
    ∃ E : Finset α, E.card ≤ 8 * ⌈B⌉₊ ∧
      ∀ J ∈ bad, ¬ Disjoint J E := by
  apply finite_exceptional_cover bad ⌈B⌉₊ hnonempty hsize
  intro F hFB hpair
  have hreal : (F.card : ℝ) ≤ (⌈B⌉₊ : ℝ) :=
    (hpacking F hFB hpair).trans (Nat.le_ceil B)
  exact_mod_cast hreal

/-- A set disjoint from the chosen exceptional set cannot be bad. In
particular this applies to every set inside the remaining coordinates. -/
theorem no_bad_subset_complement
    {α : Type*} [DecidableEq α] {bad : Finset (Finset α)} {E U J : Finset α}
    (hcover : ∀ K ∈ bad, ¬ Disjoint K E)
    (hremaining : J ⊆ U \ E) : J ∉ bad := by
  intro hJ
  apply hcover J hJ
  apply Finset.disjoint_left.mpr
  intro x hxJ hxE
  have hxRemaining := hremaining hxJ
  exact (Finset.mem_sdiff.mp hxRemaining).2 hxE

#print axioms bad_family_nonempty_of_zero_empty
#print axioms finite_exceptional_cover_core
#print axioms finite_exceptional_cover
#print axioms finite_exceptional_cover_real
#print axioms finite_exceptional_cover_ceiling
#print axioms no_bad_subset_complement

end CurrentAdditive
