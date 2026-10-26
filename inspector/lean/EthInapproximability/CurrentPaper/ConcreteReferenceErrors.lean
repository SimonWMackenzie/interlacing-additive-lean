import EthInapproximability.CurrentPaper.ConcreteGlobalClosure

/-!
# Actual missing-reference fractions at assigned terminals

Source: frozen v8 `A-stage4-details.tex`, `clm:paper-global-transfer`,
lines 1275--1284. Initial deletions are counted once across disjoint original
coordinate blocks. The remaining missing rows are the actual route losses
from the retained reference set. No aggregate error bound is assumed.
-/

noncomputable section
open scoped Classical BigOperators

namespace EthInapproximability.CurrentPaper.ConcreteReferenceErrors

open ConcreteGlobalClosure

variable {X Node : Type*} [Fintype X] [DecidableEq X] [DecidableEq Node] {q : ℕ}

/-- Original reference rows retained initially and reaching their assigned node. -/
def terminalReference (A : Finset (Fin q × X)) (ref : Finset X)
    (dest : Fin q × X → Node) (owner : Fin q → Node) (j : Fin q) :
    Finset (Fin q × X) :=
  (retainedReference A ref j).filter fun z => dest z = owner j

/-- Missing fraction normalized by one full reference block, not all rows. -/
def epsilon (A : Finset (Fin q × X)) (ref : Finset X)
    (dest : Fin q × X → Node) (owner : Fin q → Node) (j : Fin q) : ℚ :=
  ((referenceBlock ref j \ terminalReference A ref dest owner j).card : ℚ) / ref.card

theorem terminalReference_subset (A : Finset (Fin q × X)) (ref : Finset X)
    (dest : Fin q × X → Node) (owner : Fin q → Node) (j : Fin q) :
    terminalReference A ref dest owner j ⊆ referenceBlock ref j := by
  intro z hz
  exact (Finset.mem_inter.mp (Finset.mem_filter.mp hz).1).2

theorem epsilon_nonneg (A : Finset (Fin q × X)) (ref : Finset X)
    (dest : Fin q × X → Node) (owner : Fin q → Node) (j : Fin q) :
    0 ≤ epsilon A ref dest owner j := by unfold epsilon; positivity

theorem epsilon_le_one (A : Finset (Fin q × X)) (ref : Finset X)
    (href : 0 < ref.card) (dest : Fin q × X → Node) (owner : Fin q → Node) (j : Fin q) :
    epsilon A ref dest owner j ≤ 1 := by
  unfold epsilon
  apply (div_le_one (by exact_mod_cast href)).mpr
  exact_mod_cast (Finset.card_le_card Finset.sdiff_subset).trans (referenceBlock_card ref j).le

theorem epsilon_eq_one_sub (A : Finset (Fin q × X)) (ref : Finset X)
    (href : 0 < ref.card) (dest : Fin q × X → Node) (owner : Fin q → Node) (j : Fin q) :
    epsilon A ref dest owner j = 1 -
      (terminalReference A ref dest owner j).card / (ref.card : ℚ) := by
  have hc := Finset.card_sdiff_add_card_eq_card (terminalReference_subset A ref dest owner j)
  rw [referenceBlock_card] at hc
  have hcQ : ((referenceBlock ref j \ terminalReference A ref dest owner j).card : ℚ) +
      (terminalReference A ref dest owner j).card = ref.card := by exact_mod_cast hc
  have hr : (ref.card : ℚ) ≠ 0 := by exact_mod_cast href.ne'
  unfold epsilon
  apply (div_eq_iff hr).mpr
  field_simp
  linarith

theorem missing_card_partition (A : Finset (Fin q × X)) (ref : Finset X)
    (dest : Fin q × X → Node) (owner : Fin q → Node) (j : Fin q) :
    (referenceBlock ref j \ terminalReference A ref dest owner j).card =
      (referenceBlock ref j \ A).card +
        ((retainedReference A ref j).filter fun z => dest z ≠ owner j).card := by
  have he : referenceBlock ref j \ terminalReference A ref dest owner j =
      (referenceBlock ref j \ A) ∪
        ((retainedReference A ref j).filter fun z => dest z ≠ owner j) := by
    ext z
    simp only [terminalReference, retainedReference, Finset.mem_sdiff, Finset.mem_union,
      Finset.mem_filter, Finset.mem_inter]
    tauto
  have hd : Disjoint (referenceBlock ref j \ A)
      ((retainedReference A ref j).filter fun z => dest z ≠ owner j) := by
    apply Finset.disjoint_left.mpr
    intro z hz ht
    exact (Finset.mem_sdiff.mp hz).2 (Finset.mem_inter.mp (Finset.mem_filter.mp ht).1).1
  rw [he, Finset.card_union_of_disjoint hd]

/-- Distinct coordinate blocks cannot charge the same initially deleted row. -/
theorem initial_deletion_sum_le (A : Finset (Fin q × X)) (ref : Finset X)
    (J : Finset (Fin q)) :
    (∑ j ∈ J, (referenceBlock ref j \ A).card) ≤ (Finset.univ \ A).card := by
  have hd (j : Fin q) (_ : j ∈ J) (k : Fin q) (_ : k ∈ J) (hjk : j ≠ k) :
      Disjoint (referenceBlock ref j \ A) (referenceBlock ref k \ A) := by
    apply Finset.disjoint_left.mpr
    intro z hj hk
    have hj' := (Finset.mem_product.mp (Finset.mem_sdiff.mp hj).1).1
    have hk' := (Finset.mem_product.mp (Finset.mem_sdiff.mp hk).1).1
    exact hjk ((Finset.mem_singleton.mp hj').symm.trans (Finset.mem_singleton.mp hk'))
  rw [← Finset.card_biUnion hd]
  apply Finset.card_le_card
  intro z hz
  obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hz
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hj).2⟩

/-- The actual missing-row sum consists only of initial deletions and the
separately proved per-coordinate clean route losses. -/
theorem missing_sum_le (A : Finset (Fin q × X)) (ref : Finset X)
    (dest : Fin q × X → Node) (owner : Fin q → Node) (J : Finset (Fin q))
    (A0 : ℕ) (hroute : ∀ j ∈ J,
      ((retainedReference A ref j).filter fun z => dest z ≠ owner j).card < (q - 1) * A0) :
    (∑ j ∈ J, (referenceBlock ref j \ terminalReference A ref dest owner j).card) ≤
      (Finset.univ \ A).card + q * (q - 1) * A0 := by
  simp_rw [missing_card_partition]
  rw [Finset.sum_add_distrib]
  have hr := Finset.sum_le_sum (fun j hj => (hroute j hj).le)
  simp only [Finset.sum_const, nsmul_eq_mul] at hr
  have hJ : J.card ≤ q := by simpa using Finset.card_le_univ J
  have hmul := Nat.mul_le_mul_right ((q - 1) * A0) hJ
  have hi := initial_deletion_sum_le A ref J
  simpa only [Nat.mul_assoc] using Nat.add_le_add hi (hr.trans hmul)

theorem error_sum_real_bound (A : Finset (Fin q × X)) (ref : Finset X)
    (href : 0 < ref.card) (hq : 1 ≤ q)
    (dest : Fin q × X → Node) (owner : Fin q → Node) (J : Finset (Fin q))
    (A0 : ℕ) (δ : ℝ)
    (hA : (1 - δ) * (q : ℝ) * Fintype.card X ≤ A.card)
    (hroute : ∀ j ∈ J,
      ((retainedReference A ref j).filter fun z => dest z ≠ owner j).card < (q - 1) * A0) :
    (∑ j ∈ J, (epsilon A ref dest owner j : ℝ)) ≤
      (δ * q * Fintype.card X + (q : ℝ) * (q - 1) * A0) / ref.card := by
  have hm := missing_sum_le A ref dest owner J A0 hroute
  have hmR : (∑ j ∈ J,
      ((referenceBlock ref j \ terminalReference A ref dest owner j).card : ℝ)) ≤
      ((Finset.univ \ A).card : ℝ) + (q : ℝ) * (q - 1) * A0 := by
    exact_mod_cast hm
  have htotal : (Finset.univ \ A).card + A.card = q * Fintype.card X := by
    simpa using Finset.card_sdiff_add_card_inter (Finset.univ : Finset (Fin q × X)) A
  have htotalR : ((Finset.univ \ A).card : ℝ) + A.card =
      (q : ℝ) * Fintype.card X := by exact_mod_cast htotal
  have hdel : ((Finset.univ \ A).card : ℝ) ≤ δ * q * Fintype.card X := by nlinarith
  simp only [epsilon, Rat.cast_div, Rat.cast_natCast, ← Finset.sum_div]
  exact div_le_div_of_nonneg_right (hmR.trans (by linarith))
    (le_of_lt (by exact_mod_cast href : (0 : ℝ) < ref.card))

open Parameters Construction JointTransfer ConcreteRouting

/-- The physical reference proportion and the actual accepted ceiling budget
pay the two parts of the missing-reference sum. -/
theorem physical_error_sum_real (i : Input) (hc : 0 < i.sourceConstant)
    (ha : Accepted i) (Y : Type) [Fintype Y] [Nonempty Y]
    (A : Finset (RoutingRow i Y))
    (dest : RoutingRow i Y → Node) (owner : Fin (outerWidth i) → Node)
    (J : Finset (Fin (outerWidth i)))
    (hA : (1 - ((columnLoss i : ℚ) : ℝ)) * outerWidth i *
      Fintype.card (ProtectedColumns (firstExponent i) (bins i) (secondWidth i) Y) ≤ A.card)
    (hroute : ∀ j ∈ J,
      ((retainedReference A (referenceRows (firstExponent i) (bins i) (secondWidth i)) j).filter
        fun z => dest z ≠ owner j).card < (outerWidth i - 1) * referenceFloor i Y) :
    (∑ j ∈ J, (epsilon A (referenceRows (firstExponent i) (bins i) (secondWidth i))
      dest owner j : ℝ)) ≤ ((rowTolerance i : ℚ) : ℝ) / (8 * (91 / 92)) := by
  classical
  let ref := referenceRows (Y := Y) (firstExponent i) (bins i) (secondWidth i)
  have href : 0 < ref.card := physicalReferenceCount_pos i Y
  have hbound := error_sum_real_bound A ref href (outerWidth_pos i) dest owner J
    (referenceFloor i Y) ((columnLoss i : ℚ) : ℝ) hA hroute
  have hR := ProtectedDeletionGates.reference_count (Y := Y)
    (firstExponent i) (bins i) (secondWidth i)
  have hM : (0 : ℝ) < Fintype.card
      (ProtectedColumns (firstExponent i) (bins i) (secondWidth i) Y) := by
    have hr : (0 : ℝ) < ref.card := by exact_mod_cast href
    change (ref.card : ℝ) = _ at hR
    nlinarith
  have hδQ : columnLoss i * outerWidth i = rowTolerance i / 16 := by
    have hq0 : (outerWidth i : ℚ) ≠ 0 := by exact_mod_cast (outerWidth_pos i).ne'
    unfold columnLoss
    field_simp
  have hδ : ((columnLoss i : ℚ) : ℝ) * outerWidth i =
      ((rowTolerance i : ℚ) : ℝ) / 16 := by exact_mod_cast hδQ
  have hinit : ((columnLoss i : ℚ) : ℝ) * outerWidth i *
      Fintype.card (ProtectedColumns (firstExponent i) (bins i) (secondWidth i) Y) /
      ref.card = ((rowTolerance i : ℚ) : ℝ) / (16 * (91 / 92)) := by
    rw [hδ]
    change _ / ((referenceRows (Y := Y) (firstExponent i) (bins i) (secondWidth i)).card : ℝ) = _
    rw [hR]
    field_simp
  have hbudget := (actual_reference_survival i hc ha Y).2.2
  change (outerWidth i : ℝ) * (outerWidth i - 1) * referenceFloor i Y /
      ref.card ≤ ((rowTolerance i : ℚ) : ℝ) / (16 * (91 / 92)) at hbudget
  calc
    _ ≤ _ := hbound
    _ = ((rowTolerance i : ℚ) : ℝ) / (16 * (91 / 92)) +
        (outerWidth i : ℝ) * (outerWidth i - 1) * referenceFloor i Y / ref.card := by
      rw [add_div, hinit]
    _ ≤ ((rowTolerance i : ℚ) : ℝ) / (16 * (91 / 92)) +
        ((rowTolerance i : ℚ) : ℝ) / (16 * (91 / 92)) := add_le_add_right hbudget _
    _ = _ := by ring

/-- Rational interface consumed by `RoutedClosure.transfer_mass_bound`.
The error function is the actual missing-reference fraction. -/
theorem physical_error_sum (i : Input) (hc : 0 < i.sourceConstant)
    (ha : Accepted i) (Y : Type) [Fintype Y] [Nonempty Y]
    (A : Finset (RoutingRow i Y))
    (dest : RoutingRow i Y → Node) (owner : Fin (outerWidth i) → Node)
    (J : Finset (Fin (outerWidth i)))
    (hA : (1 - ((columnLoss i : ℚ) : ℝ)) * outerWidth i *
      Fintype.card (ProtectedColumns (firstExponent i) (bins i) (secondWidth i) Y) ≤ A.card)
    (hroute : ∀ j ∈ J,
      ((retainedReference A (referenceRows (firstExponent i) (bins i) (secondWidth i)) j).filter
        fun z => dest z ≠ owner j).card < (outerWidth i - 1) * referenceFloor i Y) :
    (∑ j ∈ J, epsilon A (referenceRows (firstExponent i) (bins i) (secondWidth i))
      dest owner j) ≤ rowTolerance i / (8 * (91 / 92)) := by
  have h := physical_error_sum_real i hc ha Y A dest owner J hA hroute
  have hcast : (((∑ j ∈ J, epsilon A
      (referenceRows (firstExponent i) (bins i) (secondWidth i)) dest owner j) : ℚ) : ℝ) ≤
      ((rowTolerance i / (8 * (91 / 92)) : ℚ) : ℝ) := by
    simpa only [Rat.cast_sum, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat] using h
  exact_mod_cast hcast

end EthInapproximability.CurrentPaper.ConcreteReferenceErrors
