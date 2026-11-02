import Paper2.SourceSupportSchedule

/-!
# Numerical and indexing facts for the remaining conversation

Frozen v12 Section 4, `src:near-full`: the dyadic capacity after a Bob-only
prefix and the literal enumeration of its surviving coordinate supports.
These statements do not assume or construct a protocol frontier.
-/

namespace Paper2.SourceRemainingConversationNumerics

open SourceSupportSchedule

theorem capacity_eq_pow {q ell r : ℕ} (hq : q = 2 ^ ell) (hr : r ≤ ell) :
    (q : ℝ) / (2 : ℝ) ^ r = (2 : ℝ) ^ (ell - r) := by
  subst q
  rw [Nat.cast_pow, Nat.cast_ofNat,
    show (2 : ℝ) ^ ell = 2 ^ (ell - r) * 2 ^ r by
      rw [← pow_add, Nat.sub_add_cancel hr]]
  field_simp

/-- The initial support budget bounds both later dyadic row scales and
the two-coordinate scale used at capacity one. -/
theorem capacity_scale {q ell r : ℕ} {x : ℝ}
    (hx : 0 ≤ x) (hsmall : floor q x 0 ≤ 1 / 8)
    (hq : q = 2 ^ ell) (hr : r ≤ ell) :
    (2 : ℝ) ^ (ell - r) * x ≤ 1 ∧ 2 * x ≤ 1 := by
  subst q
  have hf : floor (2 ^ ell) x r ≤ 1 / 8 :=
    (floor_antitone hx (Nat.zero_le r)).trans hsmall
  rw [floor_capacity ell r x hr] at hf
  have hb : 2 * (2 : ℝ) ^ ell * x ≤ 1 / 8 := by
    simpa only [floor_zero, Nat.cast_pow, Nat.cast_ofNat] using hsmall
  have hp : (1 : ℝ) ≤ 2 ^ ell := one_le_pow₀ (by norm_num)
  have hpx : 0 ≤ ((2 : ℝ) ^ ell - 1) * x :=
    mul_nonneg (sub_nonneg.mpr hp) hx
  constructor <;> nlinarith

theorem remaining_cost {pCost r origCost H ell : ℕ}
    (hsubtree : pCost + r ≤ origCost) (horiginal : origCost ≤ H + ell)
    (hr : r ≤ ell) : pCost ≤ H + (ell - r) := by
  omega

/-- Enumerate the actual retained coordinates, without changing their labels. -/
noncomputable def coordinateEnumeration {q : ℕ} (Q : Finset (Fin q)) :
    Fin Q.card → Fin q := fun i => (Q.equivFin.symm i).val

theorem coordinateEnumeration_injective {q : ℕ} (Q : Finset (Fin q)) :
    Function.Injective (coordinateEnumeration Q) := by
  intro i j hij
  apply Q.equivFin.symm.injective
  exact Subtype.ext hij

@[simp] theorem coordinateEnumeration_mem {q : ℕ} (Q : Finset (Fin q))
    (i : Fin Q.card) : coordinateEnumeration Q i ∈ Q :=
  (Q.equivFin.symm i).property

theorem coordinateEnumeration_surjective_on {q : ℕ} (Q : Finset (Fin q))
    {a : Fin q} (ha : a ∈ Q) : ∃ i, coordinateEnumeration Q i = a := by
  refine ⟨Q.equivFin ⟨a, ha⟩, ?_⟩
  simp [coordinateEnumeration]

/-- Each selected coordinate keeps precisely its own original word support. -/
def selectedSupport {q : ℕ} {Word : Type*} (Q : Finset (Fin q))
    (support : Fin q → Set Word) : Set (Fin Q.card × Word) :=
  fun a => a.2 ∈ support (coordinateEnumeration Q a.1)

@[simp] theorem mem_selectedSupport {q : ℕ} {Word : Type*}
    (Q : Finset (Fin q)) (support : Fin q → Set Word)
    (i : Fin Q.card) (w : Word) :
    (i, w) ∈ selectedSupport Q support ↔ w ∈ support (coordinateEnumeration Q i) :=
  Iff.rfl

end Paper2.SourceRemainingConversationNumerics

#print axioms Paper2.SourceRemainingConversationNumerics.capacity_eq_pow
#print axioms Paper2.SourceRemainingConversationNumerics.capacity_scale
#print axioms Paper2.SourceRemainingConversationNumerics.remaining_cost
#print axioms Paper2.SourceRemainingConversationNumerics.coordinateEnumeration_injective
#print axioms Paper2.SourceRemainingConversationNumerics.coordinateEnumeration_surjective_on
#print axioms Paper2.SourceRemainingConversationNumerics.mem_selectedSupport
