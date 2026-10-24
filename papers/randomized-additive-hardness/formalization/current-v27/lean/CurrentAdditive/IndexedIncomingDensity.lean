import CurrentAdditive.DeterministicIndexedStreamConditioning
import Paper2.ProtectedDensityGroups

/-!
Appendix I `det:incoming`: the incoming protected receipts and the first
dyadic selection on the actual indexed column labels.  The selected group
contains original outer positions, including positions discarded by a
separate owner argument.
-/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.ProtectedDensityGroups
open scoped BigOperators

variable {X Y : Type*} [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

/-- The two protected column populations, each normalized before its
`1/256` weight in the actual `columnLaw`. -/
noncomputable def protectedDensity (w : ℕ)
    (R : Set (Fin w × Column src)) (I : Finset (Fin w))
    (diagonal : Bool) (i : Fin w) : ℝ := by
  classical
  exact if i ∈ I then
    if diagonal then
      (diagonalLaw src).toFiniteLaw.prob
        (fun z => (i, Column.diagonal z) ∈ R)
    else
      src.outer.law.toFiniteLaw.prob
        (fun z => (i, Column.fixedTail z) ∈ R)
    else 0

theorem protectedDensity_nonneg (w : ℕ)
    (R : Set (Fin w × Column src)) (I : Finset (Fin w))
    (b : Bool) (i : Fin w) :
    0 ≤ protectedDensity src w R I b i := by
  unfold protectedDensity
  split_ifs <;> first | exact FiniteLaw.prob_nonneg _ _ | positivity

theorem protectedDensity_le_one (w : ℕ)
    (R : Set (Fin w × Column src)) (I : Finset (Fin w))
    (b : Bool) (i : Fin w) :
    protectedDensity src w R I b i ≤ 1 := by
  unfold protectedDensity
  split_ifs <;> first | exact FiniteLaw.prob_le_one _ _ | norm_num

/-- Protected mass in units of one full indexed N copy. -/
noncomputable def protectedReceipt (w : ℕ)
    (R : Set (Fin w × Column src)) (i : Fin w) : ℝ :=
  (1 / 256 : ℝ) * src.outer.law.toFiniteLaw.prob
      (fun z => (i, Column.fixedTail z) ∈ R) +
    (1 / 256 : ℝ) * (diagonalLaw src).toFiniteLaw.prob
      (fun z => (i, Column.diagonal z) ∈ R)

/-- The receipt is exactly the protected part of the original tagged column
law.  No replacement iid alphabet or changed measure occurs here. -/
theorem protectedReceipt_eq_actual_prob (w : ℕ)
    (R : Set (Fin w × Column src)) (i : Fin w) :
    protectedReceipt src w R i =
      (columnLaw src).toFiniteLaw.prob (fun Z =>
        (match Z with
          | .ordinary _ => False
          | .fixedTail _ => True
          | .diagonal _ => True) ∧ (i, Z) ∈ R) := by
  classical
  simp only [FiniteLaw.prob, PositiveRationalLaw.toFiniteLaw,
    protectedReceipt, columnLaw]
  rw [column_sum]
  simp only [Finset.mul_sum, mul_ite, mul_zero]
  push_cast
  simp

theorem protected_sum_eq (w : ℕ)
    (R : Set (Fin w × Column src)) (I : Finset (Fin w)) :
    (∑ i ∈ I, protectedReceipt src w R i) =
      (1 / 256 : ℝ) * (∑ i, protectedDensity src w R I false i) +
      (1 / 256 : ℝ) * (∑ i, protectedDensity src w R I true i) := by
  classical
  simp [protectedReceipt, protectedDensity, Finset.mul_sum,
    Finset.sum_add_distrib]

/-- Failure of the source's incoming bound forces one of the two actual
protected populations to have the density total required for grouping. -/
theorem heavy_protected_type (w r κ : ℕ)
    (R : Set (Fin w × Column src)) (I : Finset (Fin w))
    (hmass : 1024 * (1 / 256 : ℝ) * (r + 2) * s * κ ≤
      ∑ i ∈ I, protectedReceipt src w R i) :
    ∃ b : Bool,
      512 * (r + 2 : ℝ) * s * κ ≤
        ∑ i, protectedDensity src w R I b i := by
  have heq := protected_sum_eq src w R I
  by_cases h : 512 * (r + 2 : ℝ) * s * κ ≤
      ∑ i, protectedDensity src w R I false i
  · exact ⟨false, h⟩
  · refine ⟨true, ?_⟩
    push Not at h
    nlinarith [heq]

/-- A failed incoming bound yields a dyadic class of actual origin labels.
The eventual flag and selector arguments may use these labels directly. -/
theorem incoming_density_group (w r κ : ℕ)
    (R : Set (Fin w × Column src)) (I : Finset (Fin w))
    (hw : w = 2 ^ r) (hs : 0 < s) (hκ : 0 < κ)
    (hmass : 1024 * (1 / 256 : ℝ) * (r + 2) * s * κ ≤
      ∑ i ∈ I, protectedReceipt src w R i) :
    ∃ b : Bool,
      let d := protectedDensity src w R I b
      let D₀ : ℝ := ∑ i, d i
      512 * (r + 2 : ℝ) * s * κ ≤ D₀ ∧
      ∃ j : Fin (r + 2),
        let δ : ℝ := (1 / 2 : ℝ) ^ j.val
        let V := dyadicGroup d D₀ j
        V ⊆ I ∧ 0 < δ ∧ δ ≤ 1 ∧
          D₀ / (2 * (w : ℝ)) ≤ δ ∧
          (∀ i ∈ V, δ / 2 < d i ∧ d i ≤ δ) ∧
          D₀ / (2 * (r + 2 : ℝ)) ≤ (V.card : ℝ) * δ ∧
          256 * (s : ℝ) * κ ≤ (V.card : ℝ) := by
  classical
  obtain ⟨b, hlarge⟩ := heavy_protected_type src w r κ R I hmass
  let d := protectedDensity src w R I b
  let D₀ : ℝ := ∑ i, d i
  have hDone : 1 ≤ D₀ := by
    have hr : (1 : ℝ) ≤ r + 2 := by exact_mod_cast (show 1 ≤ r + 2 by omega)
    have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
    have hκ' : (1 : ℝ) ≤ κ := by exact_mod_cast hκ
    have hprod : (1 : ℝ) ≤ (r + 2 : ℝ) * s * κ := by
      calc
        (1 : ℝ) = 1 * 1 * 1 := by ring
        _ ≤ (r + 2 : ℝ) * s * κ := by gcongr
    nlinarith [hlarge]
  obtain ⟨j, hδpos, hδone, hδlow, hrow, hcount⟩ :=
    density_group d hw (protectedDensity_nonneg src w R I b)
      (protectedDensity_le_one src w R I b) D₀ rfl hDone
  let V := dyadicGroup d D₀ j
  refine ⟨b, hlarge, j, ?_, hδpos, hδone, hδlow, hrow, hcount, ?_⟩
  · intro i hi
    by_contra hn
    have hz : protectedDensity src w R I b i = 0 := by
      simp [protectedDensity, hn]
    have hmem := (Finset.mem_filter.mp hi).2
    rw [hz] at hmem
    have hp : (0 : ℝ) < (1 / 2 : ℝ) ^ (j.val + 1) := by positivity
    linarith [hmem.2.1]
  · have hL : (0 : ℝ) < (r + 2 : ℝ) := by positivity
    have hscaled : 256 * (s : ℝ) * κ ≤ D₀ / (2 * (r + 2 : ℝ)) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (r + 2 : ℝ))).2
      nlinarith [hlarge]
    have hcard : (V.card : ℝ) * (1 / 2 : ℝ) ^ j.val ≤ V.card := by
      have hn : (0 : ℝ) ≤ (V.card : ℝ) := Nat.cast_nonneg _
      nlinarith [mul_nonneg hn (sub_nonneg.mpr hδone)]
    linarith

#print axioms heavy_protected_type
#print axioms incoming_density_group

end CurrentAdditive.DeterministicIndexedMatrix.Sources
