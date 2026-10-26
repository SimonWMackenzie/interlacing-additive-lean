import Mathlib

/-! The finite combinatorial count in v39 `lem:conditioning-moment`.
This module has no probability-law or desired-moment premise. -/

namespace V39MomentCount

open scoped BigOperators

def support {n m : ℕ} (f : Fin n → Fin m) : Finset (Fin m) :=
  Finset.univ.image f

def fiberCount {n m : ℕ} (f : Fin n → Fin m) (j : Fin m) : ℕ :=
  (Finset.univ.filter fun t => f t = j).card

def NoSingleton {n m : ℕ} (f : Fin n → Fin m) : Prop :=
  ∀ j, fiberCount f j ≠ 1

noncomputable def goodTuples (m r : ℕ) : Finset (Fin (2*r) → Fin m) := by
  classical
  exact Finset.univ.filter NoSingleton

noncomputable def compositionImage (m r : ℕ) : Finset (Fin (2*r) → Fin m) := by
  classical
  exact (Finset.univ : Finset ((Fin r → Fin m) × (Fin (2*r) → Fin r))).image
    (fun p => p.1 ∘ p.2)

theorem support_card_le (n m : ℕ) (f : Fin n → Fin m) :
    (support f).card ≤ n := by
  simpa [support] using (Finset.card_image_le (s := Finset.univ) (f := f))

theorem fiberCount_pos_of_mem {n m : ℕ} (f : Fin n → Fin m) (j : Fin m)
    (hj : j ∈ support f) : 0 < fiberCount f j := by
  apply Nat.pos_of_ne_zero
  exact (Finset.fiber_card_ne_zero_iff_mem_image Finset.univ f j).2 hj

theorem sum_fiberCount {n m : ℕ} (f : Fin n → Fin m) :
    n = ∑ j ∈ support f, fiberCount f j := by
  simpa [support, fiberCount] using Finset.card_eq_sum_card_image f Finset.univ

theorem support_card_le_half (m r : ℕ) (f : Fin (2*r) → Fin m)
    (hf : NoSingleton f) : (support f).card ≤ r := by
  have hsum := sum_fiberCount f
  have htwo : 2 * (support f).card ≤ ∑ j ∈ support f, fiberCount f j := by
    calc
      2 * (support f).card = ∑ _j ∈ support f, (2 : ℕ) := by simp; omega
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j hj
        have hp := fiberCount_pos_of_mem f j hj
        have hn := hf j
        omega
  omega

/-- Every tuple using at most r labels is in the image of composition.
Unused positions of its label list are filled with an arbitrary label. -/
theorem small_range_factor (m r : ℕ) (hm : 0 < m)
    (f : Fin (2*r) → Fin m) (hf : (support f).card ≤ r) :
    ∃ a : Fin r → Fin m, ∃ b : Fin (2*r) → Fin r, a ∘ b = f := by
  classical
  let S := {j // j ∈ support f}
  have hc : Fintype.card S ≤ Fintype.card (Fin r) := by simpa [S] using hf
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hc
  let a : Fin r → Fin m :=
    Function.extend e (fun j : S => j.val) (fun _ => ⟨0, hm⟩)
  let b : Fin (2*r) → Fin r := fun t =>
    e ⟨f t, Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩⟩
  refine ⟨a, b, ?_⟩
  funext t
  exact e.injective.extend_apply (fun j : S => j.val) (fun _ => ⟨0, hm⟩)
    ⟨f t, Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩⟩

theorem goodTuples_card_le (m r : ℕ) (hr : 1 ≤ r) :
    (goodTuples m r).card ≤ m ^ r * r ^ (2*r) := by
  classical
  by_cases hm : m = 0
  · subst m
    have h2r : 2*r ≠ 0 := by omega
    calc
      (goodTuples 0 r).card ≤ (Finset.univ : Finset (Fin (2*r) → Fin 0)).card :=
        Finset.card_le_univ _
      _ = 0 := by simp [h2r]
      _ ≤ _ := Nat.zero_le _
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  have hsub : goodTuples m r ⊆ compositionImage m r := by
    intro f hf
    have hgood : NoSingleton f := (Finset.mem_filter.mp hf).2
    obtain ⟨a,b,hab⟩ := small_range_factor m r hmpos f
      (support_card_le_half m r f hgood)
    exact Finset.mem_image.mpr ⟨(a,b), Finset.mem_univ _, hab⟩
  calc
    (goodTuples m r).card ≤ (compositionImage m r).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset ((Fin r → Fin m) × (Fin (2*r) → Fin r))).card :=
      Finset.card_image_le
    _ = _ := by simp

theorem goodTuples_card_le_target (m r : ℕ) (hr : 1 ≤ r) :
    ((goodTuples m r).card : ℝ) ≤ (((r : ℝ)^2)*m)^r := by
  have h := goodTuples_card_le m r hr
  have heq : m ^ r * r ^ (2*r) = (r^2*m)^r := by
    simp only [mul_pow, pow_mul]
    ring
  rw [heq] at h
  exact_mod_cast h

#print axioms support
#print axioms fiberCount
#print axioms NoSingleton
#print axioms goodTuples
#print axioms compositionImage
#print axioms support_card_le
#print axioms fiberCount_pos_of_mem
#print axioms sum_fiberCount
#print axioms support_card_le_half
#print axioms small_range_factor
#print axioms goodTuples_card_le
#print axioms goodTuples_card_le_target

end V39MomentCount
