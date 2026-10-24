import Paper2.TwoStreamMatrix
import Paper2.RationalRowEstimates

/-!
# Ordinary capacity on original two-stream labels

The selected row blocks below are images of retained original rows.  A whole
selected ordinary tuple is retained, so no independence is asserted of the
event after conditioning on the ordinary column set.
-/

namespace Paper2.TwoStreamOrdinaryCapacity

open Workspace.Types.CommComplexity
open Paper2.TwoStreamMatrix

variable {S J Rw Ω F : Type*} [Fintype S] [Fintype J]
  [Fintype Rw] [Fintype Ω] [Fintype F]
  {s n : ℕ}

/-- The first profile rung applies to an actual one-bin restriction. -/
theorem one_bin_lower
    (μ : FiniteLaw S) (ν : FiniteLaw J)
    (T : S → J → Bool) (M : Rw → (Ω ⊕ F) → Bool)
    (bin : Rw → Fin s) (selector : Rw → S) (Φ : Ω → Fin s → J)
    (hordinary : ∀ r c, M r (.inl c) = T (selector r) (Φ c (bin r)))
    (i : Fin s) (R : Set Rw) (O : Set Ω)
    (hbin : ∀ r ∈ R, bin r = i)
    (κ : FiniteLaw Ω) (hΦ : κ.PushesTo (ν.iid s) Φ)
    (x : ℝ) (H : ℕ)
    (hprofile : RestrictionProfile T μ ν x (H : ℤ))
    (hrow : x ≤ μ.prob (· ∈ selector '' R))
    (hO : 3 / 5 ≤ κ.prob (· ∈ O)) :
    H ≤ Compression.restrictionD M R (Sum.inl '' O) := by
  have hcoord : κ.PushesTo ν (fun c => Φ c i) := by
    intro U
    calc
      κ.prob (fun c => U (Φ c i)) = (ν.iid s).prob (fun z => U (z i)) :=
        hΦ (fun z => U (z i))
      _ = ν.prob U := FiniteLaw.iid_prob_coordinate ν s i U
  have hcol : (3 / 5 : ℝ) ≤ ν.prob (· ∈ (fun c => Φ c i) '' O) :=
    hO.trans (FiniteLaw.prob_le_image _ _ _ hcoord O)
  have hp := hprofile (0 : Fin 3) (selector '' R) ((fun c => Φ c i) '' O)
    hrow (by simpa using hcol)
  have hn : H ≤ Compression.restrictionD T (selector '' R)
      ((fun c => Φ c i) '' O) := by
    norm_num at hp
    exact_mod_cast hp
  exact hn.trans (one_bin_D_le T M bin selector Φ hordinary i R O hbin)

/-- A selected block is the image of original retained rows in its
physical bin. This definition keeps the raw row-to-bin witness available. -/
noncomputable def selectedRows (bin : Rw → Fin s) (selector : Rw → S)
    (e : Fin n → Fin s) (R : Set Rw) : Finset (Fin n × S) := by
  classical
  exact Finset.univ.filter (fun a => ∃ r ∈ R, bin r = e a.1 ∧ selector r = a.2)

/-- Actual original rows and one joint ordinary tuple realize the entire
selected interlace. Every row representative is fixed before a column is seen. -/
theorem many_bin_restriction
    [Nonempty Rw]
    (T : S → J → Bool) (M : Rw → (Ω ⊕ F) → Bool)
    (bin : Rw → Fin s) (selector : Rw → S) (Φ : Ω → Fin s → J)
    (hordinary : ∀ r c, M r (.inl c) = T (selector r) (Φ c (bin r)))
    (e : Fin n → Fin s) (R : Set Rw) (O : Set Ω) :
    Compression.restrictionD (fullInterlace T n)
      {a | a ∈ selectedRows bin selector e R}
      ((fun c j => Φ c (e j)) '' O) ≤
      Compression.restrictionD M R (Sum.inl '' O) := by
  classical
  let A : Set (Fin n × S) := {a | a ∈ selectedRows bin selector e R}
  let lift : Fin n × S → Rw := fun a =>
    if h : ∃ r ∈ R, bin r = e a.1 ∧ selector r = a.2 then
      Classical.choose h else Classical.choice inferInstance
  have hlift : ∀ a ∈ A, lift a ∈ R ∧ bin (lift a) = e a.1 ∧
      selector (lift a) = a.2 := by
    intro a ha
    have hex : ∃ r ∈ R, bin r = e a.1 ∧ selector r = a.2 := by
      simpa [A, selectedRows] using ha
    simpa [lift, hex] using Classical.choose_spec hex
  exact many_bin_D_le T M bin selector Φ hordinary e R O A lift hlift

/-- The power-capacity estimate on the actual matrix, with the selected
row masses supplied by raw retained-bin events and ordinary columns measured
through their correlated whole-tuple image. -/
theorem many_bin_power
    [Nonempty Rw]
    (μ : PositiveRationalLaw S) (ν : PositiveRationalLaw J)
    (T : S → J → Bool) (M : Rw → (Ω ⊕ F) → Bool)
    (bin : Rw → Fin s) (selector : Rw → S) (Φ : Ω → Fin s → J)
    (hordinary : ∀ r c, M r (.inl c) = T (selector r) (Φ c (bin r)))
    (e : Fin n → Fin s) (R : Set Rw) (O : Set Ω)
    (H l : ℕ) (x : ℝ) (hH : 2 ≤ H) (hx : 0 < x) (hl : 2 ≤ l)
    (hscale : (2 : ℝ) ^ l * x ≤ 1)
    (hprofile : RestrictionProfile T μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (Q : Finset (Fin n)) (hQ : 2 ^ (l - 1) + 1 ≤ Q.card)
    (hrow : ∀ i ∈ Q, (2 : ℝ) ^ l * x ≤
      μ.toFiniteLaw.prob (fun a => ∃ r ∈ R, bin r = e i ∧ selector r = a))
    (hcol : (9 / 25 : ℝ) ≤ (ν.toFiniteLaw.iid n).prob
      (· ∈ (fun c j => Φ c (e j)) '' O)) :
    H + l ≤ Compression.restrictionD M R (Sum.inl '' O) := by
  classical
  let A := selectedRows bin selector e R
  let C : Finset (Fin n → J) :=
    Finset.univ.filter (fun z => z ∈ (fun c j => Φ c (e j)) '' O)
  have hr : ∀ i ∈ Q, (2 : ℝ) ^ l * x ≤
      μ.toFiniteLaw.prob (fun a => (i, a) ∈ A) := by
    intro i hi
    simpa [A, selectedRows] using hrow i hi
  have hc : (9 / 25 : ℝ) ≤ (ν.toFiniteLaw.iid n).prob (· ∈ C) := by
    simpa [C] using hcol
  have hh := RationalRowEstimates.small_capacity_power μ ν T H l n
    hH hx hl hscale hprofile Q hQ A C hr hc
  have hCset : {z | z ∈ C} = (fun c j => Φ c (e j)) '' O := by
    ext z
    simp [C]
  have heq : D (NPCC.subgame (fullInterlace T n) A C) =
      Compression.restrictionD (fullInterlace T n)
        {a | a ∈ A} ((fun c j => Φ c (e j)) '' O) := by
    rw [← hCset]
    rfl
  rw [heq] at hh
  exact hh.trans (many_bin_restriction T M bin selector Φ hordinary e R O)

theorem many_bin_two
    [Nonempty Rw]
    (μ : PositiveRationalLaw S) (ν : PositiveRationalLaw J)
    (T : S → J → Bool) (M : Rw → (Ω ⊕ F) → Bool)
    (bin : Rw → Fin s) (selector : Rw → S) (Φ : Ω → Fin s → J)
    (hordinary : ∀ r c, M r (.inl c) = T (selector r) (Φ c (bin r)))
    (e : Fin n → Fin s) (R : Set Rw) (O : Set Ω)
    (H : ℕ) (x : ℝ) (hH : 2 ≤ H) (hx : 0 < x)
    (hscale : 2 * x ≤ 1)
    (hprofile : RestrictionProfile T μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (Q : Finset (Fin n)) (hQ : 2 ≤ Q.card)
    (hrow : ∀ i ∈ Q, 2 * x ≤
      μ.toFiniteLaw.prob (fun a => ∃ r ∈ R, bin r = e i ∧ selector r = a))
    (hcol : (9 / 25 : ℝ) ≤ (ν.toFiniteLaw.iid n).prob
      (· ∈ (fun c j => Φ c (e j)) '' O)) :
    H + 1 ≤ Compression.restrictionD M R (Sum.inl '' O) := by
  classical
  let A := selectedRows bin selector e R
  let C : Finset (Fin n → J) :=
    Finset.univ.filter (fun z => z ∈ (fun c j => Φ c (e j)) '' O)
  have hr : ∀ i ∈ Q, 2 * x ≤ μ.toFiniteLaw.prob (fun a => (i, a) ∈ A) := by
    intro i hi
    simpa [A, selectedRows] using hrow i hi
  have hc : (9 / 25 : ℝ) ≤ (ν.toFiniteLaw.iid n).prob (· ∈ C) := by
    simpa [C] using hcol
  have hh := RationalRowEstimates.small_capacity_two μ ν T H n
    hH hx hscale hprofile Q hQ A C hr hc
  have hCset : {z | z ∈ C} = (fun c j => Φ c (e j)) '' O := by
    ext z
    simp [C]
  have heq : D (NPCC.subgame (fullInterlace T n) A C) =
      Compression.restrictionD (fullInterlace T n)
        {a | a ∈ A} ((fun c j => Φ c (e j)) '' O) := by
    rw [← hCset]
    rfl
  rw [heq] at hh
  exact hh.trans (many_bin_restriction T M bin selector Φ hordinary e R O)

/-- The retained ordinary event is projected jointly to the selected bins.
The strict ambient density is only used to reach the row-estimate threshold. -/
theorem many_bin_power_from_ambient
    [Nonempty Rw]
    (μ : PositiveRationalLaw S) (ν : PositiveRationalLaw J)
    (κ : FiniteLaw Ω) (T : S → J → Bool) (M : Rw → (Ω ⊕ F) → Bool)
    (bin : Rw → Fin s) (selector : Rw → S) (Φ : Ω → Fin s → J)
    (hordinary : ∀ r c, M r (.inl c) = T (selector r) (Φ c (bin r)))
    (hΦ : κ.PushesTo (ν.toFiniteLaw.iid s) Φ)
    (e : Fin n → Fin s) (he : Function.Injective e)
    (R : Set Rw) (O : Set Ω)
    (H l : ℕ) (x : ℝ) (hH : 2 ≤ H) (hx : 0 < x) (hl : 2 ≤ l)
    (hscale : (2 : ℝ) ^ l * x ≤ 1)
    (hprofile : RestrictionProfile T μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (Q : Finset (Fin n)) (hQ : 2 ^ (l - 1) + 1 ≤ Q.card)
    (hrow : ∀ i ∈ Q, (2 : ℝ) ^ l * x ≤
      μ.toFiniteLaw.prob (fun a => ∃ r ∈ R, bin r = e i ∧ selector r = a))
    (hO : (9 / 25 : ℝ) < κ.prob (· ∈ O)) :
    H + l ≤ Compression.restrictionD M R (Sum.inl '' O) := by
  apply many_bin_power μ ν T M bin selector Φ hordinary e R O
    H l x hH hx hl hscale hprofile Q hQ hrow
  exact hO.le.trans (selected_joint_mass ν.toFiniteLaw κ Φ hΦ e he O)

theorem many_bin_two_from_ambient
    [Nonempty Rw]
    (μ : PositiveRationalLaw S) (ν : PositiveRationalLaw J)
    (κ : FiniteLaw Ω) (T : S → J → Bool) (M : Rw → (Ω ⊕ F) → Bool)
    (bin : Rw → Fin s) (selector : Rw → S) (Φ : Ω → Fin s → J)
    (hordinary : ∀ r c, M r (.inl c) = T (selector r) (Φ c (bin r)))
    (hΦ : κ.PushesTo (ν.toFiniteLaw.iid s) Φ)
    (e : Fin n → Fin s) (he : Function.Injective e)
    (R : Set Rw) (O : Set Ω)
    (H : ℕ) (x : ℝ) (hH : 2 ≤ H) (hx : 0 < x)
    (hscale : 2 * x ≤ 1)
    (hprofile : RestrictionProfile T μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (Q : Finset (Fin n)) (hQ : 2 ≤ Q.card)
    (hrow : ∀ i ∈ Q, 2 * x ≤
      μ.toFiniteLaw.prob (fun a => ∃ r ∈ R, bin r = e i ∧ selector r = a))
    (hO : (9 / 25 : ℝ) < κ.prob (· ∈ O)) :
    H + 1 ≤ Compression.restrictionD M R (Sum.inl '' O) := by
  apply many_bin_two μ ν T M bin selector Φ hordinary e R O
    H x hH hx hscale hprofile Q hQ hrow
  exact hO.le.trans (selected_joint_mass ν.toFiniteLaw κ Φ hΦ e he O)

end Paper2.TwoStreamOrdinaryCapacity

#print axioms Paper2.TwoStreamOrdinaryCapacity.one_bin_lower
#print axioms Paper2.TwoStreamOrdinaryCapacity.many_bin_restriction
#print axioms Paper2.TwoStreamOrdinaryCapacity.many_bin_power
#print axioms Paper2.TwoStreamOrdinaryCapacity.many_bin_two
#print axioms Paper2.TwoStreamOrdinaryCapacity.many_bin_power_from_ambient
#print axioms Paper2.TwoStreamOrdinaryCapacity.many_bin_two_from_ambient
