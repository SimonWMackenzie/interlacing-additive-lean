import CurrentAdditive.EdgeIndexFacts
import Paper2.CanonicalEndpointRankBridge

/-! A local edge-only active-rank formula. The incidence source is only
used at its edge tag to reuse a proved finite rank-counting identity.
There is no identification of coordinate carriers or source widths. -/

namespace CurrentAdditive.LiteralEdgeEncoder

open Paper2

theorem itemOrder_eq_old (s n : ℕ) :
    itemOrder s n = CanonicalSourceLabels.itemOrder s n := rfl

theorem activity_unpadded_eq_scan {s n m r : ℕ} [NeZero s]
    (hs : 3 ≤ s) (e : Fin m → Bool → Fin n) (i : Items s n)
    (g : Fin (4*s)) (edgeIndex : Fin m) (rep : Fin r) :
    activity hs e i (coordinateNumber s m r (.inl (g,edgeIndex),rep)) =
      SourceActiveRank.scanActivity e hs r i
        (.inl (g,(edgeIndex,none)),rep) := by
  rw [activity_eq_ordered, Equiv.symm_apply_apply,
    SourceActiveRank.scanActivity_eq_orderedActivity]
  have hlabels : EdgeSourceMatrix.activeLabels (itemOrder s n) e r
      (.inl (g,edgeIndex),rep) =
      SourceConstruction.activeLabels (CanonicalSourceLabels.itemOrder s n) e r
        (.inl (g,(edgeIndex,none)),rep) := by
    ext j
    rw [itemOrder_eq_old]
    cases hz : ((CanonicalSourceLabels.itemOrder s n).symm j).2 <;>
      simp [EdgeSourceMatrix.activeLabels, SourceConstruction.activeLabels,
        EdgeSource.sourceActive, SourceItems.sourceActive, SourcePadding.repeatedActive,
        SourcePadding.paddedActive, EdgeSource.active, SourceItems.groupedActive,
        SourceItems.active, hz]
  rw [itemOrder_eq_old] at hlabels
  unfold EdgeSourceMatrix.orderedActivity SourceConstruction.orderedActivity
  simp only [itemOrder_eq_old, hlabels]
  split
  · apply congrArg some
    apply Fin.ext
    change
      (EdgeSourceMatrix.activeLabels (CanonicalSourceLabels.itemOrder s n) e r
        (.inl (g,edgeIndex),rep)).sort.idxOf (CanonicalSourceLabels.itemOrder s n i) =
      (SourceConstruction.activeLabels (CanonicalSourceLabels.itemOrder s n) e r
        (.inl (g,(edgeIndex,none)),rep)).sort.idxOf (CanonicalSourceLabels.itemOrder s n i)
    rw [hlabels]
  · rfl

theorem activity_unpadded_rank {s n m r : ℕ} [NeZero s]
    (hs : 3 ≤ s) (e : Fin m → Bool → Fin n) (g : Fin (4*s))
    (edgeIndex : Fin m) (rep : Fin r) (z : Fin n ⊕ Fin (s-3)) :
    Option.map Fin.val
      (activity hs e (g,z) (coordinateNumber s m r (.inl (g,edgeIndex),rep))) =
      if CanonicalEndpointRankMachine.semanticActive .edge
          (CanonicalEndpointRankBridge.itemKindOf z)
          (e edgeIndex false).val (e edgeIndex true).val
          (CanonicalEndpointRankBridge.itemValue z) then
        some (CanonicalEndpointRankMachine.semanticRank .edge
          (CanonicalEndpointRankBridge.itemKindOf z)
          (e edgeIndex false).val (e edgeIndex true).val
          (CanonicalEndpointRankBridge.itemValue z))
      else none := by
  rw [activity_unpadded_eq_scan,
    CanonicalActiveRankFormula.scanActivity_closedRankNat]
  exact CanonicalEndpointRankBridge.closedRankNat_selected e g edgeIndex none z _ rfl

theorem activity_inactive {s n m r : ℕ} [NeZero s] (hs : 3 ≤ s)
    (e : Fin m → Bool → Fin n) (i : Items s n)
    (a : Fin (EdgeSource.sourceQ0 (Fin (4*s)) (Fin m) * r))
    (ha : active e a i = false) : activity hs e i a = none := by
  have hnot : itemOrder s n i ∉ activeLabels e a := by
    simp [activeLabels, ha]
  simp [activity, hnot]

theorem coordinate_selected_iff {s m r : ℕ}
    (a : Fin (EdgeSource.sourceQ0 (Fin (4*s)) (Fin m) * r))
    (ig : Fin (4*s)) :
    (0 < m ∧ a.val / r / m = ig.val) ↔
      ∃ e : Fin m, ∃ rep : Fin r,
        coordinateNumber s m r (.inl (ig,e),rep) = a := by
  obtain ⟨⟨pad,rep⟩,rfl⟩ := (coordinateNumber s m r).surjective a
  cases pad with
  | inl c =>
      obtain ⟨g,e⟩ := c
      obtain ⟨hg,he,ht⟩ := coordinate_decode_edge g e rep
      rw [hg]
      constructor
      · intro h
        have hgi : g = ig := Fin.ext h.2
        subst g
        exact ⟨e,rep,rfl⟩
      · rintro ⟨e',rep',h⟩
        have h' := (coordinateNumber s m r).injective h
        have hgi : ig = g := by
          simpa using congrArg (fun c => match c.1 with
            | .inl p => p.1
            | .inr _ => ig) h'
        exact ⟨Nat.lt_of_le_of_lt (Nat.zero_le _) e.isLt,
          congrArg Fin.val hgi.symm⟩
  | inr j =>
      obtain ⟨hb,ht⟩ := coordinate_decode_padding j rep
      constructor
      · rintro ⟨hm,hg⟩
        have hbound : 4*s ≤
            (coordinateNumber s m r (.inr j,rep)).val / r / m := by
          rw [Nat.le_div_iff_mul_le hm, hb]
          omega
        have hig := ig.isLt
        omega
      · rintro ⟨e',rep',h⟩
        have h' := congrArg Prod.fst ((coordinateNumber s m r).injective h)
        change Sum.inl (ig,e') = Sum.inr j at h'
        cases h'

theorem activity_none {s n m r : ℕ} [NeZero s] (hs : 3 ≤ s)
    (e : Fin m → Bool → Fin n) (ig : Fin (4*s)) (z : Fin n ⊕ Fin (s-3))
    (a : Fin (EdgeSource.sourceQ0 (Fin (4*s)) (Fin m) * r))
    (ha : ¬ (0 < m ∧ a.val / r / m = ig.val)) :
    activity hs e (ig,z) a = none := by
  apply activity_inactive hs e
  obtain ⟨⟨pad,rep⟩,rfl⟩ := (coordinateNumber s m r).surjective a
  cases pad with
  | inr j => exact active_padding e j rep (ig,z)
  | inl c =>
      obtain ⟨g,j⟩ := c
      have hg : ig ≠ g := by
        intro heq
        apply ha
        exact ⟨Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt,
          (coordinate_decode_edge g j rep).1.trans (congrArg Fin.val heq.symm)⟩
      simp [active, hg]

theorem activity_selected {s n m r : ℕ} [NeZero s] (hs : 3 ≤ s)
    (e : Fin m → Bool → Fin n) (ig : Fin (4*s)) (z : Fin n ⊕ Fin (s-3))
    (a : Fin (EdgeSource.sourceQ0 (Fin (4*s)) (Fin m) * r))
    (ha : 0 < m ∧ a.val / r / m = ig.val) :
    let j : Fin m := ⟨a.val / r % m, Nat.mod_lt _ ha.1⟩
    Option.map Fin.val (activity hs e (ig,z) a) =
      if CanonicalEndpointRankMachine.semanticActive .edge
          (CanonicalEndpointRankBridge.itemKindOf z)
          (e j false).val (e j true).val
          (CanonicalEndpointRankBridge.itemValue z) then
        some (CanonicalEndpointRankMachine.semanticRank .edge
          (CanonicalEndpointRankBridge.itemKindOf z)
          (e j false).val (e j true).val
          (CanonicalEndpointRankBridge.itemValue z))
      else none := by
  intro j
  obtain ⟨j',rep,hnum⟩ := (coordinate_selected_iff a ig).mp ha
  have hj : j' = j := by
    apply Fin.ext
    have he := (coordinate_decode_edge ig j' rep).2.1
    rw [hnum] at he
    exact he.symm
  subst j'
  rw [← hnum]
  exact activity_unpadded_rank hs e ig j rep z

#print axioms activity_unpadded_eq_scan
#print axioms activity_unpadded_rank

end CurrentAdditive.LiteralEdgeEncoder
