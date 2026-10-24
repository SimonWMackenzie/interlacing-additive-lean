import Mathlib

/-!
# Balanced colours and lookup slots

Statement source: Paper 2, locked `2026-09-22-protocol-labels-v12`,
`sections/07-yao.tex`, the short-protocol paragraph following `yao:entry`.

A balanced colouring of an ordered edge of size `s * s` puts at least
`s - 1` vertices in every colour. Consequently at most `2 * s - 1` edge
positions have any specified colour. Adding the neutral slot uses at
most `2 * s` slots. This module proves that finite counting fact; it
does not assume or prove a colouring algorithm or a hardness reduction.
-/

namespace Paper2.YaoLookup

open scoped BigOperators

/-- Number of edge positions having a specified colour. -/
def colourFiberCard {K s : ℕ} (colour : Fin K → Fin s) (c : Fin s) : ℕ :=
  (Finset.univ.filter fun i => colour i = c).card

/-- The colour classes partition all positions of the ordered edge. -/
theorem sum_colourFiberCard {K s : ℕ} (colour : Fin K → Fin s) :
    ∑ c, colourFiberCard colour c = K := by
  simpa [colourFiberCard] using
    Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset (Fin K)) (Finset.univ : Finset (Fin s)) colour

/-- Every other colour consumes at least `minimum` positions. -/
theorem colourFiberCard_add_other_minimum_le {K s minimum : ℕ}
    (colour : Fin K → Fin s)
    (hminimum : ∀ c, minimum ≤ colourFiberCard colour c) (c : Fin s) :
    colourFiberCard colour c + (s - 1) * minimum ≤ K := by
  have hsum : (s - 1) * minimum ≤
      ∑ d ∈ Finset.univ.erase c, colourFiberCard colour d := by
    calc
      (s - 1) * minimum = ∑ _d ∈ Finset.univ.erase c, minimum := by simp
      _ ≤ ∑ d ∈ Finset.univ.erase c, colourFiberCard colour d := by
        exact Finset.sum_le_sum fun d _ => hminimum d
  have hpartition := Finset.sum_erase_add
    (s := (Finset.univ : Finset (Fin s)))
    (f := colourFiberCard colour) (Finset.mem_univ c)
  rw [sum_colourFiberCard] at hpartition
  omega

/-- The exact balanced-colouring bound in the manuscript. -/
theorem balanced_colourFiberCard_le {s : ℕ} (hs : 1 ≤ s)
    (colour : Fin (s * s) → Fin s)
    (hbalanced : ∀ c, s - 1 ≤ colourFiberCard colour c) (c : Fin s) :
    colourFiberCard colour c ≤ 2 * s - 1 := by
  have h := colourFiberCard_add_other_minimum_le colour hbalanced c
  have hsone : s - 1 + 1 = s := by omega
  have hbound : colourFiberCard colour c + 1 ≤ 2 * s := by nlinarith
  omega

/-- The neutral slot together with the real edge positions of one colour. -/
abbrev ColourSlot {K s : ℕ} (colour : Fin K → Fin s) (c : Fin s) :=
  Option {i : Fin K // colour i = c}

/-- Slot count includes exactly one extra neutral slot. -/
theorem card_colourSlot {K s : ℕ} (colour : Fin K → Fin s) (c : Fin s) :
    Fintype.card (ColourSlot colour c) = colourFiberCard colour c + 1 := by
  simp [ColourSlot, colourFiberCard, Fintype.card_subtype]

/-- The balanced colour and neutral slot fit into `2 * s` addresses. -/
theorem balanced_card_colourSlot_le {s : ℕ} (hs : 1 ≤ s)
    (colour : Fin (s * s) → Fin s)
    (hbalanced : ∀ c, s - 1 ≤ colourFiberCard colour c) (c : Fin s) :
    Fintype.card (ColourSlot colour c) ≤ 2 * s := by
  rw [card_colourSlot]
  have h := balanced_colourFiberCard_le hs colour hbalanced c
  omega

/-- With `s = 2^t`, the slots fit into the number of words of length `t+1`. -/
theorem pow_two_card_colourSlot_le (t : ℕ)
    (colour : Fin (2 ^ t * 2 ^ t) → Fin (2 ^ t))
    (hbalanced : ∀ c, 2 ^ t - 1 ≤ colourFiberCard colour c)
    (c : Fin (2 ^ t)) :
    Fintype.card (ColourSlot colour c) ≤ 2 ^ (t + 1) := by
  have h := balanced_card_colourSlot_le (Nat.one_le_pow t 2 (by omega))
    colour hbalanced c
  simpa [pow_succ, Nat.mul_comm] using h

end Paper2.YaoLookup
