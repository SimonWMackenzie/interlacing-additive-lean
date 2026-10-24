import Paper2.SourceActiveRank

/-! A closed, edge-local formula for the executable canonical activity rank.
The old source coordinate equivalence is deliberately absent. -/

namespace Paper2.CanonicalActiveRankFormula

open SourceItems SourceActiveRank CanonicalSourceLabels

private theorem itemOrder_val {s n : Nat}
    (i : SourceConstruction.Items s (Fin n)) :
    (itemOrder s n i).val = (itemIndex s n i).val := by
  simp [itemOrder, finCongr_apply]

private theorem vertex_before_vertex {s n : Nat}
    (g : Fin (4*s)) (v w : Fin n) :
    itemOrder s n (g, .inl v) < itemOrder s n (g, .inl w) ↔ v < w := by
  simp only [Fin.lt_def, itemOrder_val, itemIndex_vertex_val]
  omega

private theorem vertex_before_aux {s n : Nat}
    (g : Fin (4*s)) (v : Fin n) (a : Fin (s-3)) :
    itemOrder s n (g, .inl v) < itemOrder s n (g, .inr a) := by
  simp only [Fin.lt_def, itemOrder_val, itemIndex_vertex_val, itemIndex_aux_val]
  omega

private theorem aux_not_before_vertex {s n : Nat}
    (g : Fin (4*s)) (a : Fin (s-3)) (v : Fin n) :
    ¬ itemOrder s n (g, .inr a) < itemOrder s n (g, .inl v) := by
  simp only [Fin.lt_def, itemOrder_val, itemIndex_vertex_val, itemIndex_aux_val]
  omega

private theorem aux_before_aux {s n : Nat}
    (g : Fin (4*s)) (a b : Fin (s-3)) :
    itemOrder s n (g, .inr a) < itemOrder s n (g, .inr b) ↔ a < b := by
  simp only [Fin.lt_def, itemOrder_val, itemIndex_aux_val]
  omega

private noncomputable def localEarlier {s n m : Nat}
    (edge : Fin m → Bool → Fin n) (g : Fin (4*s))
    (e : Fin m) (tag : Option Bool) (z : Fin n ⊕ Fin (s-3)) :
    Finset (Fin n ⊕ Fin (s-3)) := by
  classical
  exact Finset.univ.filter (fun z' =>
    itemOrder s n (g, z') < itemOrder s n (g, z) ∧
      SourceItems.active edge (e, tag) z')

private theorem earlierActive_card_local {s n m r : Nat}
    (edge : Fin m → Bool → Fin n) (g : Fin (4*s))
    (e : Fin m) (tag : Option Bool) (t : Fin r)
    (z : Fin n ⊕ Fin (s-3)) :
    (earlierActive edge r (g, z) (.inl (g, (e, tag)), t)).card =
      (localEarlier edge g e tag z).card := by
  classical
  unfold localEarlier
  have hsource (g' : Fin (4*s)) (z' : Fin n ⊕ Fin (s-3)) :
      SourceItems.sourceActive edge r (.inl (g, (e, tag)), t) (g', z') ↔
        g' = g ∧ SourceItems.active edge (e, tag) z' := by
    simp [SourceItems.sourceActive, SourcePadding.repeatedActive,
      SourcePadding.paddedActive, SourceItems.groupedActive]
  apply Finset.card_bij
    (fun j _ => ((itemOrder s n).symm j).2)
  · intro j hj
    obtain ⟨hlt, hact⟩ := (Finset.mem_filter.mp hj).2
    obtain ⟨hg, ha⟩ := (hsource _ _).mp hact
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ha⟩
    have hj : (g, ((itemOrder s n).symm j).2) =
        (itemOrder s n).symm j := by
      apply Prod.ext
      · exact hg.symm
      · rfl
    simpa [hj] using hlt
  · intro j hj k hk heq
    have hjg : ((itemOrder s n).symm j).1 = g :=
      ((hsource _ _).mp (Finset.mem_filter.mp hj).2.2).1
    have hkg : ((itemOrder s n).symm k).1 = g :=
      ((hsource _ _).mp (Finset.mem_filter.mp hk).2.2).1
    have hitems : (itemOrder s n).symm j = (itemOrder s n).symm k := by
      apply Prod.ext
      · exact hjg.trans hkg.symm
      · exact heq
    exact (itemOrder s n).symm.injective hitems
  · intro z' hz'
    obtain ⟨hlt, ha⟩ := (Finset.mem_filter.mp hz').2
    refine ⟨itemOrder s n (g, z'), ?_, by simp⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, hlt, ?_⟩
    simpa [hsource] using (show (g = g ∧ SourceItems.active edge (e, tag) z') from
      ⟨rfl, ha⟩)

private def activeVertices {n m : Nat}
    (edge : Fin m → Bool → Fin n) (e : Fin m) (tag : Option Bool) :
    Finset (Fin n) :=
  match tag with
  | none => {edge e false, edge e true}
  | some b => {edge e b}

private theorem mem_activeVertices {n m : Nat}
    (edge : Fin m → Bool → Fin n) (e : Fin m) (tag : Option Bool)
    (v : Fin n) :
    v ∈ activeVertices edge e tag ↔
      SourceItems.active edge (e, tag) (.inl v : Fin n ⊕ Fin 0) := by
  cases tag <;> simp [activeVertices, SourceItems.active]

private theorem localEarlier_vertex_card {s n m : Nat}
    (edge : Fin m → Bool → Fin n) (g : Fin (4*s))
    (e : Fin m) (tag : Option Bool) (v : Fin n) :
    (localEarlier edge g e tag (.inl v)).card =
      ((activeVertices edge e tag).filter (· < v)).card := by
  classical
  have hset : localEarlier edge g e tag (.inl v) =
      ((activeVertices edge e tag).filter (· < v)).image Sum.inl := by
    ext z'
    cases z' with
    | inl w =>
        cases tag <;>
          simp [localEarlier, activeVertices, SourceItems.active,
            vertex_before_vertex, and_comm, eq_comm]
    | inr a =>
        simp [localEarlier, aux_not_before_vertex]
  rw [hset]
  exact Finset.card_image_of_injective _ Sum.inl_injective

private theorem localEarlier_aux_card {s n m : Nat}
    (edge : Fin m → Bool → Fin n) (g : Fin (4*s))
    (e : Fin m) (tag : Option Bool) (a : Fin (s-3)) :
    (localEarlier edge g e tag (.inr a)).card =
      (activeVertices edge e tag).card + a.val := by
  classical
  have hset : localEarlier edge g e tag (.inr a) =
      (activeVertices edge e tag).image Sum.inl ∪
        (Finset.Iio a).image Sum.inr := by
    ext z'
    cases z' with
    | inl v =>
        cases tag <;>
          simp [localEarlier, activeVertices, SourceItems.active,
            vertex_before_aux, eq_comm]
    | inr b =>
        simp [localEarlier, SourceItems.active, aux_before_aux]
  rw [hset]
  have hd : Disjoint ((activeVertices edge e tag).image Sum.inl)
      ((Finset.Iio a).image Sum.inr) := by
    simp [Finset.disjoint_left]
  rw [Finset.card_union_of_disjoint hd]
  rw [Finset.card_image_of_injective _ Sum.inl_injective]
  rw [Finset.card_image_of_injective _ Sum.inr_injective]
  simp [Fin.card_Iio]

/-- The rank in the canonical item order, using only the selected indexed edge.
`none` is padding, a different group, or an inactive vertex. -/
def closedRankNat {s n m r : Nat}
    (edge : Fin m → Bool → Fin n)
    (i : SourceConstruction.Items s (Fin n))
    (c : SourceItems.SourceCoord (Fin (4*s)) (Fin m) r) : Option Nat :=
  match c.1 with
  | .inr _ => none
  | .inl (g, (e, tag)) =>
      if i.1 = g then
        match i.2 with
        | .inl v =>
            match tag with
            | none =>
                if v = edge e false ∨ v = edge e true then
                  some (({edge e false, edge e true} : Finset (Fin n)).filter
                    (· < v)).card
                else none
            | some b => if v = edge e b then some 0 else none
        | .inr a =>
            match tag with
            | none => some (({edge e false, edge e true} : Finset (Fin n)).card + a.val)
            | some _ => some (1 + a.val)
      else none

/-- The finite scan has the edge-local closed rank at every coordinate,
including padding and repeated copies. The ordinal is the dense canonical
item-order ordinal, not the older endpoint-labelled public slot. -/
theorem scanActivity_closedRankNat {s n m r : Nat} [NeZero s]
    (edge : Fin m → Bool → Fin n) (hs : 3 ≤ s)
    (i : SourceConstruction.Items s (Fin n))
    (c : SourceItems.SourceCoord (Fin (4*s)) (Fin m) r) :
    Option.map Fin.val (scanActivity edge hs r i c) =
      closedRankNat edge i c := by
  obtain ⟨pad, t⟩ := c
  cases pad with
  | inr p =>
      simp [scanActivity, closedRankNat, SourceItems.sourceActive,
        SourcePadding.repeatedActive, SourcePadding.paddedActive]
  | inl core =>
      obtain ⟨g, e, tag⟩ := core
      obtain ⟨g', z⟩ := i
      by_cases hg : g' = g
      · subst g'
        cases z with
        | inl v =>
            cases tag with
            | none =>
                by_cases hv : v = edge e false ∨ v = edge e true
                · simp [scanActivity, closedRankNat, SourceItems.sourceActive,
                    SourcePadding.repeatedActive, SourcePadding.paddedActive,
                    SourceItems.groupedActive, SourceItems.active, hv,
                    earlierActive_card_local, localEarlier_vertex_card,
                    activeVertices]
                · simp [scanActivity, closedRankNat, SourceItems.sourceActive,
                    SourcePadding.repeatedActive, SourcePadding.paddedActive,
                    SourceItems.groupedActive, SourceItems.active, hv]
            | some b =>
                by_cases hv : v = edge e b
                · simp [scanActivity, closedRankNat, SourceItems.sourceActive,
                    SourcePadding.repeatedActive, SourcePadding.paddedActive,
                    SourceItems.groupedActive, SourceItems.active, hv,
                    earlierActive_card_local, localEarlier_vertex_card,
                    activeVertices]
                · simp [scanActivity, closedRankNat, SourceItems.sourceActive,
                    SourcePadding.repeatedActive, SourcePadding.paddedActive,
                    SourceItems.groupedActive, SourceItems.active, hv]
        | inr a =>
            cases tag with
            | none =>
                simp [scanActivity, closedRankNat, SourceItems.sourceActive,
                  SourcePadding.repeatedActive, SourcePadding.paddedActive,
                  SourceItems.groupedActive, SourceItems.active,
                  earlierActive_card_local, localEarlier_aux_card,
                  activeVertices]
            | some b =>
                simp [scanActivity, closedRankNat, SourceItems.sourceActive,
                  SourcePadding.repeatedActive, SourcePadding.paddedActive,
                  SourceItems.groupedActive, SourceItems.active,
                  earlierActive_card_local, localEarlier_aux_card,
                  activeVertices]
      · simp [scanActivity, closedRankNat, SourceItems.sourceActive,
          SourcePadding.repeatedActive, SourcePadding.paddedActive,
          SourceItems.groupedActive, hg]

/-- The numeric canonical-coordinate consumer, with the same explicit decoder
used by the source. -/
theorem scanAtCanonical_closedRankNat {s n m r q₂ : Nat} [NeZero s]
    (edge : Fin m → Bool → Fin n) (hs : 3 ≤ s)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4*s)) (Fin m) * r)
    (i : SourceConstruction.Items s (Fin n)) (a : Fin q₂) :
    Option.map Fin.val (scanAtCanonical edge hs hq i a) =
      closedRankNat edge i (coordOrder s m r q₂ hq a) := by
  exact scanActivity_closedRankNat edge hs i _

#print axioms scanActivity_closedRankNat
#print axioms scanAtCanonical_closedRankNat

end Paper2.CanonicalActiveRankFormula
