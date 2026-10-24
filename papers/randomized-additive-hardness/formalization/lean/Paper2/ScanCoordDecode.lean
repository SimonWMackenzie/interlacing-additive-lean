import Paper2.CanonicalEndpointRankBridge

/-! Unit 3, segment (1), semantic half of the physical
`SourceActiveRank.scanAtCanonical`: numeric decoding of the public canonical
outer coordinate `a : Fin q₂` (lock v12 Section 4 source coordinates; the
explicit production decoder `CanonicalSourceLabels.coordOrder`, NOT the
choice-based `SourceConstruction.coordinateEquiv`).

With `j = a / r` (padded index; the copy index `a % r` is irrelevant), the
flattened true-coordinate order `j = g * (m * 3) + e * 3 + tag` gives
`g = j / 3 / m`, `e = j / 3 % m`, `tag = j % 3`; padding is exactly
`¬ (0 < m ∧ j / 3 / m < 4 s)`. Consequently:

* `scan_selected`: when `j / 3 / m = ig`, `j / 3 % m = e`, `j % 3 = index tag`,
  the canonical scan at the item `(ig, z)` is the endpoint-rank controller's
  semantic value (`semanticActive` / `semanticRank`, the production
  `CanonicalEndpointRankMachine` definitions) on
  `(edge e false).val, (edge e true).val, itemValue z`;
* `scan_none`: when `¬ (0 < m ∧ j / 3 / m = ig)` the scan is `none`
  (group test and padding test together).

These are the value targets for the unary division chain and equality test
of the physical scan (`ScanDecodeMachine`). No machine is claimed here. -/

namespace Paper2.ScanCoordDecode

open SourceItems SourceActiveRank CanonicalSourceLabels
open CanonicalActiveRankFormula CanonicalEndpointRankBridge CanonicalEndpointRankMachine

theorem paddedIndex_inl (s m : ℕ) (c : Coord (Fin (4 * s)) (Fin m)) :
    (paddedIndex s m (.inl c)).val = (coordIndex s m c).val := by
  simp [paddedIndex, finSumFinEquiv, finCongr_apply]

theorem paddedIndex_inr (s m : ℕ)
    (p : Fin (sourceQ0 (Fin (4 * s)) (Fin m) -
      Fintype.card (Coord (Fin (4 * s)) (Fin m)))) :
    12 * s * m ≤ (paddedIndex s m (.inr p)).val := by
  simp [paddedIndex, finSumFinEquiv, finCongr_apply]

/-- The flattened numeric identity of the decoded coordinate. -/
theorem coordOrder_index {s m r q₂ : ℕ}
    (hq : q₂ = sourceQ0 (Fin (4 * s)) (Fin m) * r) (a : Fin q₂) :
    (paddedIndex s m (coordOrder s m r q₂ hq a).1).val * r +
      (coordOrder s m r q₂ hq a).2.val = a.val := by
  have h1 : sourceCoordIndex s m r (coordOrder s m r q₂ hq a) = finCongr hq a := by
    simp [coordOrder]
  have h2 := sourceCoordIndex_val s m r (coordOrder s m r q₂ hq a)
  rw [h1] at h2
  simpa [finCongr_apply] using h2.symm

theorem padded_div {s m r q₂ : ℕ}
    (hq : q₂ = sourceQ0 (Fin (4 * s)) (Fin m) * r) (a : Fin q₂) :
    a.val / r = (paddedIndex s m (coordOrder s m r q₂ hq a).1).val := by
  have hidx := coordOrder_index hq a
  have ht := (coordOrder s m r q₂ hq a).2.isLt
  have hr : 0 < r := Nat.lt_of_le_of_lt (Nat.zero_le _) ht
  rw [← hidx, Nat.add_comm, Nat.add_mul_div_right _ _ hr, Nat.div_eq_of_lt ht, Nat.zero_add]

/-- True coordinates: the four numeric fields. -/
theorem decode_selected {s m r q₂ : ℕ}
    (hq : q₂ = sourceQ0 (Fin (4 * s)) (Fin m) * r) (a : Fin q₂)
    (g : Fin (4 * s)) (e : Fin m) (tag : Option Bool)
    (h : (coordOrder s m r q₂ hq a).1 = .inl (g, (e, tag))) :
    0 < m ∧ a.val / r / 3 / m = g.val ∧ a.val / r / 3 % m = e.val ∧
      a.val / r % 3 = (optionBoolIndex tag).val := by
  have hj := padded_div hq a
  rw [h, paddedIndex_inl, coordIndex_val] at hj
  have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) e.isLt
  have ht3 : (optionBoolIndex tag).val < 3 := (optionBoolIndex tag).isLt
  have hre : g.val * (m * 3) + e.val * 3 + (optionBoolIndex tag).val =
      (optionBoolIndex tag).val + (g.val * m + e.val) * 3 := by ring
  have hj3 : a.val / r / 3 = g.val * m + e.val := by
    rw [hj, hre, Nat.add_mul_div_right _ _ (by norm_num : 0 < 3), Nat.div_eq_of_lt ht3,
      Nat.zero_add]
  have hjm : a.val / r % 3 = (optionBoolIndex tag).val := by
    rw [hj, hre, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht3]
  have hre2 : g.val * m + e.val = e.val + g.val * m := by ring
  refine ⟨hm, ?_, ?_, hjm⟩
  · rw [hj3, hre2, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt e.isLt, Nat.zero_add]
  · rw [hj3, hre2, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt e.isLt]

/-- Padding coordinates fail the numeric test. -/
theorem decode_padding {s m r q₂ : ℕ}
    (hq : q₂ = sourceQ0 (Fin (4 * s)) (Fin m) * r) (a : Fin q₂)
    (p : Fin (sourceQ0 (Fin (4 * s)) (Fin m) -
      Fintype.card (Coord (Fin (4 * s)) (Fin m))))
    (h : (coordOrder s m r q₂ hq a).1 = .inr p) :
    ¬ (0 < m ∧ a.val / r / 3 / m < 4 * s) := by
  rintro ⟨hm, hlt⟩
  have hj := padded_div hq a
  rw [h] at hj
  have hge := paddedIndex_inr s m p
  rw [← hj] at hge
  -- `a / r ≥ 12 s m` gives `a / r / 3 ≥ 4 s m` and `a / r / 3 / m ≥ 4 s`.
  have h3 : 4 * s * m ≤ a.val / r / 3 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 3)]
    calc 4 * s * m * 3 = 12 * s * m := by ring
      _ ≤ a.val / r := hge
  have h4 : 4 * s ≤ a.val / r / 3 / m := by
    rw [Nat.le_div_iff_mul_le hm]
    exact h3
  omega

/-- Selected case: the canonical scan equals the endpoint-rank semantics on
the decoded edge occurrence and label. -/
theorem scan_selected {s n m r q₂ : ℕ} [NeZero s]
    (edge : Fin m → Bool → Fin n) (hs : 3 ≤ s)
    (hq : q₂ = sourceQ0 (Fin (4 * s)) (Fin m) * r)
    (ig : Fin (4 * s)) (z : Fin n ⊕ Fin (s - 3)) (a : Fin q₂)
    (e : Fin m) (tag : Option Bool)
    (hg : a.val / r / 3 / m = ig.val) (he : a.val / r / 3 % m = e.val)
    (ht : a.val / r % 3 = (optionBoolIndex tag).val) :
    Option.map Fin.val (scanAtCanonical edge hs hq (ig, z) a) =
      if semanticActive (kindOfTag tag) (itemKindOf z)
          (edge e false).val (edge e true).val (itemValue z) then
        some (semanticRank (kindOfTag tag) (itemKindOf z)
          (edge e false).val (edge e true).val (itemValue z))
      else none := by
  have hc : (coordOrder s m r q₂ hq a).1 = .inl (ig, (e, tag)) := by
    rcases hx : (coordOrder s m r q₂ hq a).1 with ⟨g', e', tag'⟩ | p
    · obtain ⟨_, h1, h2, h3⟩ := decode_selected hq a g' e' tag' hx
      have hg' : g' = ig := Fin.ext (by omega)
      have he' : e' = e := Fin.ext (by omega)
      have ht' : tag' = tag := optionBoolIndex.injective (Fin.ext (by omega))
      rw [hg', he', ht']
    · exfalso
      apply decode_padding hq a p hx
      exact ⟨Nat.lt_of_le_of_lt (Nat.zero_le _) e.isLt, by omega⟩
  rw [scanAtCanonical_closedRankNat edge hs hq (ig, z) a]
  exact closedRankNat_selected edge ig e tag z _ hc

/-- Unselected case (other group, padding, or no edges): `none`. -/
theorem scan_none {s n m r q₂ : ℕ} [NeZero s]
    (edge : Fin m → Bool → Fin n) (hs : 3 ≤ s)
    (hq : q₂ = sourceQ0 (Fin (4 * s)) (Fin m) * r)
    (ig : Fin (4 * s)) (z : Fin n ⊕ Fin (s - 3)) (a : Fin q₂)
    (hsel : ¬ (0 < m ∧ a.val / r / 3 / m = ig.val)) :
    scanAtCanonical edge hs hq (ig, z) a = none := by
  have hmap : Option.map Fin.val (scanAtCanonical edge hs hq (ig, z) a) = none := by
    rw [scanAtCanonical_closedRankNat edge hs hq (ig, z) a]
    rcases hx : (coordOrder s m r q₂ hq a).1 with ⟨g', e', tag'⟩ | p
    · obtain ⟨hm, h1, _, _⟩ := decode_selected hq a g' e' tag' hx
      have hne : ig ≠ g' := by
        intro h
        exact hsel ⟨hm, by rw [h1, h]⟩
      exact closedRankNat_otherGroup edge g' ig e' tag' z _ hx hne
    · exact closedRankNat_padding edge (ig, z) _ p hx
  simpa using hmap

#print axioms paddedIndex_inl
#print axioms coordOrder_index
#print axioms decode_selected
#print axioms decode_padding
#print axioms scan_selected
#print axioms scan_none

end Paper2.ScanCoordDecode
