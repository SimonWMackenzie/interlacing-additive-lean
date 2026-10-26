import Mathlib

/-!
# Selecting a branch with surviving collision coordinates

Frozen v12 Section 4, `src:near-full`, the surviving-collisions paragraph.
The witness coordinates are assigned to actual witnessing branches and
partitioned by that assignment. Comparing their total population with the
sum of the actual bad-coordinate populations selects a branch; that branch
is not an input certificate. Removing its bad coordinates leaves more
than three times its entire bad-coordinate count.
-/

namespace Paper2.SourceCollisionPartition

open scoped BigOperators

variable {A J : Type*}

/-- The actual witness coordinates assigned to one branch. -/
noncomputable def part (K : Finset A) (assign : A → J) (j : J) : Finset A := by
  classical
  exact K.filter (fun α => assign α = j)

@[simp] theorem mem_part (K : Finset A) (assign : A → J) (j : J) (α : A) :
    α ∈ part K assign j ↔ α ∈ K ∧ assign α = j := by
  classical
  simp [part]

theorem parts_disjoint (K : Finset A) (assign : A → J) {i j : J} (hij : i ≠ j) :
    Disjoint (part K assign i) (part K assign j) := by
  classical
  apply Finset.disjoint_left.mpr
  intro α hi hj
  exact hij (((mem_part K assign i α).mp hi).2.symm.trans
    ((mem_part K assign j α).mp hj).2)

/-- No witness coordinate is lost or counted twice by the actual filters. -/
theorem sum_part_card [Fintype J] (K : Finset A) (assign : A → J) :
    (∑ j, (part K assign j).card) = K.card := by
  classical
  simp only [part, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

theorem sum_part_card_real [Fintype J] (K : Finset A) (assign : A → J) :
    (∑ j, ((part K assign j).card : ℝ)) = K.card := by
  exact_mod_cast sum_part_card K assign

/-- Selecting one witnessing branch per witness coordinate. The default
outside `K` is irrelevant because every part is filtered through `K`. -/
noncomputable def chooseBranch [Nonempty J] (K : Finset A) (WitnessAt : J → A → Prop)
    (hK : ∀ α ∈ K, ∃ j, WitnessAt j α) (α : A) : J := by
  classical
  exact if hα : α ∈ K then Classical.choose (hK α hα) else Classical.choice inferInstance

theorem chooseBranch_witness [Nonempty J] (K : Finset A) (WitnessAt : J → A → Prop)
    (hK : ∀ α ∈ K, ∃ j, WitnessAt j α) (α : A) (hα : α ∈ K) :
    WitnessAt (chooseBranch K WitnessAt hK α) α := by
  classical
  simpa only [chooseBranch, dif_pos hα] using Classical.choose_spec (hK α hα)

theorem part_witness [Nonempty J] (K : Finset A) (WitnessAt : J → A → Prop)
    (hK : ∀ α ∈ K, ∃ j, WitnessAt j α) (j : J) (α : A)
    (hα : α ∈ part K (chooseBranch K WitnessAt hK) j) : WitnessAt j α := by
  obtain ⟨hαK, hαj⟩ := (mem_part _ _ _ _).mp hα
  exact hαj ▸ chooseBranch_witness K WitnessAt hK α hαK

/-- The total witness/bad-coordinate comparison finds the branch whose
full witness set outnumbers four copies of its own bad set. -/
theorem exists_branch_excess [Fintype J]
    (K : Finset A) (assign : A → J) (bad : J → Finset A) (t : ℝ)
    (hK : t ≤ (K.card : ℝ)) (hbad : (∑ j, ((bad j).card : ℝ)) < t / 4) :
    ∃ j, 4 * (bad j).card < (part K assign j).card := by
  classical
  by_contra hh
  push Not at hh
  have hs : (∑ j, ((part K assign j).card : ℝ)) ≤
      ∑ j, 4 * ((bad j).card : ℝ) := by
    apply Finset.sum_le_sum
    intro j _
    exact_mod_cast hh j
  rw [sum_part_card_real, ← Finset.mul_sum] at hs
  linarith

/-- Removing all bad coordinates can delete at most their full number,
even when the bad set is not contained in the selected witness set. -/
theorem survivors_excess [DecidableEq A] (U B : Finset A) (h : 4 * B.card < U.card) :
    3 * B.card < (U \ B).card := by
  classical
  have hcard := Finset.card_le_card_sdiff_add_card (s := U) (t := B)
  omega

/-- The selected branch and its surviving coordinates are constructed
from the fixed assignment and actual bad sets. The threshold `t` may be
the source's `zeta*q2`, without any integrality assumption. -/
theorem select_surviving_branch [DecidableEq A] [Fintype J]
    (K : Finset A) (assign : A → J) (bad : J → Finset A) (t : ℝ)
    (hK : t ≤ (K.card : ℝ)) (hbad : (∑ j, ((bad j).card : ℝ)) < t / 4) :
    ∃ j, 4 * (bad j).card < (part K assign j).card ∧
      3 * (bad j).card < (part K assign j \ bad j).card := by
  obtain ⟨j, hj⟩ := exists_branch_excess K assign bad t hK hbad
  exact ⟨j, hj, survivors_excess _ _ hj⟩

/-- Source-facing form: choose a branch that actually witnesses each
coordinate, then select a branch with the required surviving excess.
All surviving coordinates still carry their original witness predicate. -/
theorem select_witness_branch [DecidableEq A] [Fintype J] [Nonempty J]
    (K : Finset A) (WitnessAt : J → A → Prop)
    (hWitness : ∀ α ∈ K, ∃ j, WitnessAt j α)
    (bad : J → Finset A) (t : ℝ)
    (hK : t ≤ (K.card : ℝ)) (hbad : (∑ j, ((bad j).card : ℝ)) < t / 4) :
    ∃ j, 4 * (bad j).card < (part K (chooseBranch K WitnessAt hWitness) j).card ∧
      3 * (bad j).card < (part K (chooseBranch K WitnessAt hWitness) j \ bad j).card ∧
      ∀ α ∈ part K (chooseBranch K WitnessAt hWitness) j \ bad j,
        α ∈ K ∧ WitnessAt j α ∧ α ∉ bad j := by
  classical
  obtain ⟨j, hj, hs⟩ := select_surviving_branch K (chooseBranch K WitnessAt hWitness)
    bad t hK hbad
  refine ⟨j, hj, hs, ?_⟩
  intro α hα
  obtain ⟨hpart, hnot⟩ := Finset.mem_sdiff.mp hα
  exact ⟨((mem_part _ _ _ _).mp hpart).1, part_witness K WitnessAt hWitness j α hpart, hnot⟩

end Paper2.SourceCollisionPartition
