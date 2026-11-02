import Paper2.CanonicalEndpointRankMachine
import Paper2.CanonicalActiveRankFormula

/-! Semantic bridge from the fixed endpoint-rank controller to the frozen,
audited closed formula `CanonicalActiveRankFormula.closedRankNat` and hence to
the executable canonical scan `SourceActiveRank.scanAtCanonical`.

Scope: the coordinate is already decoded to an edge-occurrence coordinate
`(g, (e, tag))` in the same group `g` as the item, and the three unary operand
words are the values `(edge e false).val`, `(edge e true).val` and the item
value.  Group comparison, padding detection, coordinate decoding and the
charged public-graph-to-unary conversion are NOT performed here; the separate
lemmas `closedRankNat_otherGroup` and `closedRankNat_padding` record that those
cases are `none` in the formula. -/

namespace Paper2.CanonicalEndpointRankBridge

open Turing
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.CanonicalEndpointRankMachine
open Paper2.CanonicalActiveRankFormula
open SourceItems SourceActiveRank CanonicalSourceLabels

/-- `none` is the edge coordinate; `some false`/`some true` are the left and
right labelled incidences. -/
def kindOfTag : Option Bool → Kind
  | none => .edge
  | some false => .leftIncidence
  | some true => .rightIncidence

/-- Vertex items versus auxiliary items. -/
def itemKindOf {V A : Type*} : V ⊕ A → ItemKind
  | .inl _ => .vertex
  | .inr _ => .auxiliary

/-- The numeric value carried by the unary item word. -/
def itemValue {n k : Nat} : Fin n ⊕ Fin k → Nat
  | .inl v => v.val
  | .inr a => a.val

private theorem card_filter_pair_lt {n : Nat} (a b w : Fin n)
    (hw : w = a ∨ w = b) :
    (({a, b} : Finset (Fin n)).filter (· < w)).card =
      if (decide (w.val = a.val) && decide (b.val < a.val)) ||
          (decide (w.val = b.val) && decide (a.val < b.val)) then 1 else 0 := by
  rcases hw with rfl | rfl
  · by_cases hab : w = b
    · subst hab
      simp
    · have hv : w.val ≠ b.val := fun h => hab (Fin.ext h)
      by_cases hlt : b < w
      · have hlt' : b.val < w.val := hlt
        rw [Finset.filter_insert, Finset.filter_singleton]
        simp [hlt, hv, hlt']
      · have hlt' : ¬ b.val < w.val := hlt
        rw [Finset.filter_insert, Finset.filter_singleton]
        simp [hlt, hv, hlt']
  · by_cases hab : a = w
    · subst hab
      simp
    · have hv : w.val ≠ a.val := fun h => hab (Fin.ext h).symm
      by_cases hlt : a < w
      · have hlt' : a.val < w.val := hlt
        rw [Finset.filter_insert, Finset.filter_singleton]
        simp [hlt, hv, hlt']
      · have hlt' : ¬ a.val < w.val := hlt
        rw [Finset.filter_insert, Finset.filter_singleton]
        simp [hlt, hv, hlt']

private theorem card_pair {n : Nat} (a b : Fin n) :
    ({a, b} : Finset (Fin n)).card = if a.val = b.val then 1 else 2 := by
  by_cases hab : a = b
  · subst hab
    simp
  · have hv : a.val ≠ b.val := fun h => hab (Fin.ext h)
    rw [Finset.card_pair hab]
    simp [hv]

/-- For an already-decoded edge-occurrence coordinate in the item's own group,
the closed formula is exactly the controller's semantic activity and rank on
the three selected unary operands. -/
theorem closedRankNat_selected {s n m r : Nat}
    (edge : Fin m → Bool → Fin n) (g : Fin (4 * s)) (e : Fin m)
    (tag : Option Bool) (z : Fin n ⊕ Fin (s - 3))
    (c : SourceItems.SourceCoord (Fin (4 * s)) (Fin m) r)
    (hc : c.1 = Sum.inl (g, (e, tag))) :
    closedRankNat edge (g, z) c =
      if semanticActive (kindOfTag tag) (itemKindOf z)
          (edge e false).val (edge e true).val (itemValue z) then
        some (semanticRank (kindOfTag tag) (itemKindOf z)
          (edge e false).val (edge e true).val (itemValue z))
      else none := by
  obtain ⟨pad, t⟩ := c
  simp only at hc
  subst hc
  cases z with
  | inl w =>
      cases tag with
      | none =>
          by_cases hw : w = edge e false ∨ w = edge e true
          · have hw' : (w.val == (edge e false).val ||
                w.val == (edge e true).val) = true := by
              rcases hw with h | h <;> simp [h]
            simp only [closedRankNat, kindOfTag, itemKindOf, itemValue,
              semanticActive, semanticRank, hw, hw', if_pos, card_filter_pair_lt _ _ _ hw]
            all_goals rfl
          · have hw' : (w.val == (edge e false).val ||
                w.val == (edge e true).val) = false := by
              have h1 : w.val ≠ (edge e false).val := fun h => hw (Or.inl (Fin.ext h))
              have h2 : w.val ≠ (edge e true).val := fun h => hw (Or.inr (Fin.ext h))
              simp [h1, h2]
            simp only [closedRankNat, if_true, kindOfTag, itemKindOf, itemValue,
              semanticActive, hw, hw', if_false]
            all_goals rfl
      | some b =>
          cases b with
          | false =>
              by_cases hw : w = edge e false
              · have hw' : (w.val == (edge e false).val) = true := by simp [hw]
                simp only [closedRankNat, kindOfTag, itemKindOf, itemValue,
                  semanticActive, semanticRank, hw, if_pos]
                all_goals (first | rfl | simp)
              · have hw' : (w.val == (edge e false).val) = false := by
                  have h1 : w.val ≠ (edge e false).val := fun h => hw (Fin.ext h)
                  simp [h1]
                simp only [closedRankNat, if_true, kindOfTag, itemKindOf, itemValue,
                  semanticActive, hw, hw', if_false]
                all_goals rfl
          | true =>
              by_cases hw : w = edge e true
              · have hw' : (w.val == (edge e true).val) = true := by simp [hw]
                simp only [closedRankNat, kindOfTag, itemKindOf, itemValue,
                  semanticActive, semanticRank, hw, if_pos]
                all_goals (first | rfl | simp)
              · have hw' : (w.val == (edge e true).val) = false := by
                  have h1 : w.val ≠ (edge e true).val := fun h => hw (Fin.ext h)
                  simp [h1]
                simp only [closedRankNat, if_true, kindOfTag, itemKindOf, itemValue,
                  semanticActive, hw, hw', if_false]
                all_goals rfl
  | inr a =>
      cases tag with
      | none =>
          simp only [closedRankNat, if_true, kindOfTag, itemKindOf, itemValue,
            semanticActive, semanticRank, card_pair, if_true]
          congr 1
          split_ifs <;> omega
      | some b =>
          cases b <;>
            simp only [closedRankNat, if_true, kindOfTag, itemKindOf, itemValue,
              semanticActive, semanticRank, if_true] <;>
            congr 1 <;> omega

/-- Items of a different group are `none` in the formula; the outer caller
must detect this before invoking the controller. -/
theorem closedRankNat_otherGroup {s n m r : Nat}
    (edge : Fin m → Bool → Fin n) (g g' : Fin (4 * s)) (e : Fin m)
    (tag : Option Bool) (z : Fin n ⊕ Fin (s - 3))
    (c : SourceItems.SourceCoord (Fin (4 * s)) (Fin m) r)
    (hc : c.1 = Sum.inl (g, (e, tag))) (hg : g' ≠ g) :
    closedRankNat edge (g', z) c = none := by
  obtain ⟨pad, t⟩ := c
  simp only at hc
  subst hc
  simp [closedRankNat, hg]

/-- Padding coordinates are `none` in the formula. -/
theorem closedRankNat_padding {s n m r : Nat}
    (edge : Fin m → Bool → Fin n) (i : SourceConstruction.Items s (Fin n))
    (c : SourceItems.SourceCoord (Fin (4 * s)) (Fin m) r)
    (p : Fin (SourceItems.sourceQ0 (Fin (4 * s)) (Fin m) -
      Fintype.card (SourceItems.Coord (Fin (4 * s)) (Fin m))))
    (hc : c.1 = Sum.inr p) :
    closedRankNat edge i c = none := by
  obtain ⟨pad, t⟩ := c
  simp only at hc
  subst hc
  rfl

/-- The fixed controller's final configuration, read back as the frozen
closed formula: after any clock `T ≥ max u (max v x) + 3` it has halted with
empty scratch operand stacks; its separate activity bit and the length of its
output stack give `closedRankNat` on the selected coordinate. -/
theorem run_closedRankNat {s n m r : Nat}
    (edge : Fin m → Bool → Fin n) (g : Fin (4 * s)) (e : Fin m)
    (tag : Option Bool) (z : Fin n ⊕ Fin (s - 3))
    (c : SourceItems.SourceCoord (Fin (4 * s)) (Fin m) r)
    (hc : c.1 = Sum.inl (g, (e, tag))) (T : Nat)
    (hT : max (edge e false).val (max (edge e true).val (itemValue z)) + 3 ≤ T) :
    let fin := (advance program)^[T]
      (initial (kindOfTag tag) (itemKindOf z)
        (edge e false).val (edge e true).val (itemValue z))
    fin = output (kindOfTag tag) (itemKindOf z)
        (edge e false).val (edge e true).val (itemValue z) ∧
    fin.l = none ∧ fin.stk 0 = [] ∧ fin.stk 1 = [] ∧ fin.stk 2 = [] ∧
    (∀ b ∈ fin.stk 3, b = true) ∧
    closedRankNat edge (g, z) c =
      if fin.var.active then some (fin.stk 3).length else none := by
  intro fin
  have hfin : fin = output (kindOfTag tag) (itemKindOf z)
      (edge e false).val (edge e true).val (itemValue z) :=
    run_after _ _ _ _ _ T hT
  refine ⟨hfin, ?_⟩
  rw [hfin, closedRankNat_selected edge g e tag z c hc]
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro b hb
    exact List.eq_of_mem_replicate hb
  · show _ = if semanticActive _ _ _ _ _ then
        some (List.replicate (semanticRank _ _ _ _ _) true).length else none
    rw [List.length_replicate]

/-- Numeric-coordinate consumer form: at a public canonical coordinate `a`
whose explicit `coordOrder` decoding is the selected edge-occurrence coordinate,
the executable canonical scan equals the controller's read-back. -/
theorem run_scanAtCanonical {s n m r q₂ : Nat} [NeZero s]
    (edge : Fin m → Bool → Fin n) (hs : 3 ≤ s)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin m) * r)
    (g : Fin (4 * s)) (e : Fin m) (tag : Option Bool)
    (z : Fin n ⊕ Fin (s - 3)) (a : Fin q₂)
    (ha : (coordOrder s m r q₂ hq a).1 = Sum.inl (g, (e, tag))) (T : Nat)
    (hT : max (edge e false).val (max (edge e true).val (itemValue z)) + 3 ≤ T) :
    let fin := (advance program)^[T]
      (initial (kindOfTag tag) (itemKindOf z)
        (edge e false).val (edge e true).val (itemValue z))
    Option.map Fin.val (scanAtCanonical edge hs hq (g, z) a) =
      if fin.var.active then some (fin.stk 3).length else none := by
  intro fin
  rw [scanAtCanonical_closedRankNat edge hs hq (g, z) a]
  exact (run_closedRankNat edge g e tag z _ ha T hT).2.2.2.2.2.2

#print axioms closedRankNat_selected
#print axioms closedRankNat_otherGroup
#print axioms closedRankNat_padding
#print axioms run_closedRankNat
#print axioms run_scanAtCanonical

end Paper2.CanonicalEndpointRankBridge
