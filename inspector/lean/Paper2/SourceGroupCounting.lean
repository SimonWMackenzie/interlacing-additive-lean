import Mathlib

/-!
# Counting groups with few deleted items

Source: frozen Paper 2 v12, source item witness argument (T11).

Among `4s` groups, a vertex-deletion budget below `sD/2` and an auxiliary
deletion budget below `s/2` leave more than `3s` groups with no auxiliary
deletion and at most `D` vertex deletions.  Removing at most `s` further groups
still leaves more than `2s`.  The weights and retained group sets are concrete.
-/

namespace Paper2.SourceGroupCounting

open scoped BigOperators

variable {G : Type*} [Fintype G]

/-- Groups with no deleted auxiliary item and at most `D` deleted vertices. -/
noncomputable def goodGroups (d a : G → ℕ) (D : ℝ) : Finset G := by
  classical
  exact Finset.univ.filter (fun g => a g = 0 ∧ (d g : ℝ) ≤ D)

@[simp] theorem mem_goodGroups (d a : G → ℕ) (D : ℝ) (g : G) :
    g ∈ goodGroups d a D ↔ a g = 0 ∧ (d g : ℝ) ≤ D := by
  classical
  simp [goodGroups]

/-- A bad group incurs at least `D` units of combined deletion weight. -/
theorem weight_of_not_good (d a : G → ℕ) {D : ℝ} (hD : 0 < D) {g : G}
    (hg : g ∉ goodGroups d a D) : D ≤ (d g : ℝ) + D * (a g : ℝ) := by
  classical
  by_cases ha : a g = 0
  · have hd : D < (d g : ℝ) := by
      by_contra! h
      exact hg ((mem_goodGroups d a D g).mpr ⟨ha, h⟩)
    simp only [ha, Nat.cast_zero, mul_zero, add_zero]
    exact hd.le
  · have ha' : 1 ≤ (a g : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr ha
    have hd : 0 ≤ (d g : ℝ) := Nat.cast_nonneg _
    nlinarith

/-- The two strict deletion budgets leave strictly more than `3s` good groups. -/
theorem three_mul_lt_card_good (d a : G → ℕ) {s : ℕ} {D : ℝ}
    (hcard : Fintype.card G = 4 * s) (hD : 0 < D)
    (hd : (∑ g, (d g : ℝ)) < (s : ℝ) / 2 * D)
    (ha : (∑ g, (a g : ℝ)) < (s : ℝ) / 2) :
    3 * (s : ℝ) < (goodGroups d a D).card := by
  classical
  let bad : Finset G := Finset.univ \ goodGroups d a D
  have hw : (bad.card : ℝ) * D ≤
      ∑ g ∈ bad, ((d g : ℝ) + D * (a g : ℝ)) := by
    calc
      (bad.card : ℝ) * D = ∑ _g ∈ bad, D := by simp
      _ ≤ _ := Finset.sum_le_sum fun g hg =>
        weight_of_not_good d a hD (Finset.mem_sdiff.mp hg).2
  have hsum : (∑ g ∈ bad, ((d g : ℝ) + D * (a g : ℝ))) ≤
      (∑ g, (d g : ℝ)) + D * (∑ g, (a g : ℝ)) := by
    calc
      _ ≤ ∑ g, ((d g : ℝ) + D * (a g : ℝ)) :=
        Finset.sum_le_univ_sum_of_nonneg (fun g =>
          add_nonneg (Nat.cast_nonneg _) (mul_nonneg hD.le (Nat.cast_nonneg _)))
      _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hbad : (bad.card : ℝ) < (s : ℝ) := by nlinarith
  have hpartition : (bad.card : ℝ) + ((goodGroups d a D).card : ℝ) = 4 * (s : ℝ) := by
    have hc := Finset.card_sdiff_add_card Finset.univ (goodGroups d a D)
    have hn : bad.card + (goodGroups d a D).card = 4 * s := by
      have hu : Finset.univ ∪ goodGroups d a D = Finset.univ :=
        Finset.union_eq_left.mpr (Finset.subset_univ _)
      rw [hu, Finset.card_univ, hcard] at hc
      exact hc
    exact_mod_cast hn
  linarith

/-- Excluding at most `s` further groups leaves strictly more than `2s`. -/
theorem two_mul_lt_card_remaining [DecidableEq G] (d a : G → ℕ) {s : ℕ} {D : ℝ}
    (hcard : Fintype.card G = 4 * s) (hD : 0 < D)
    (hd : (∑ g, (d g : ℝ)) < (s : ℝ) / 2 * D)
    (ha : (∑ g, (a g : ℝ)) < (s : ℝ) / 2)
    (X : Finset G) (hX : X.card ≤ s) :
    2 * (s : ℝ) < (goodGroups d a D \ X).card := by
  classical
  have hg := three_mul_lt_card_good d a hcard hD hd ha
  have hs := Finset.card_le_card_sdiff_add_card (s := goodGroups d a D) (t := X)
  have hs' : ((goodGroups d a D).card : ℝ) ≤
      ((goodGroups d a D \ X).card : ℝ) + (X.card : ℝ) := by exact_mod_cast hs
  have hX' : (X.card : ℝ) ≤ (s : ℝ) := by exact_mod_cast hX
  linarith

variable {V : Type*} [Fintype V]

/-- The items of one group satisfying the designated property. -/
noncomputable def fiber (P : G → V → Prop) (g : G) : Finset V := by
  classical
  exact Finset.univ.filter (P g)

/-- All grouped items satisfying the same designated property. -/
noncomputable def grouped (P : G → V → Prop) : Finset (G × V) := by
  classical
  exact Finset.univ.filter (fun p => P p.1 p.2)

omit [Fintype G] in
@[simp] theorem mem_fiber (P : G → V → Prop) (g : G) (v : V) :
    v ∈ fiber P g ↔ P g v := by
  classical
  simp [fiber]

@[simp] theorem mem_grouped (P : G → V → Prop) (g : G) (v : V) :
    (g, v) ∈ grouped P ↔ P g v := by
  classical
  simp [grouped]

/-- Summing the per-group counts counts each grouped item exactly once. -/
theorem card_grouped_eq_sum_fiber (P : G → V → Prop) :
    (grouped P).card = ∑ g, (fiber P g).card := by
  classical
  simp only [grouped, fiber, Finset.card_eq_sum_ones, Finset.sum_filter,
    Fintype.sum_prod_type]

end Paper2.SourceGroupCounting
