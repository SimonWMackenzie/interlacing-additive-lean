import Mathlib
import Paper2.SourceItems

/-!
Edge-only source object in the selected v37 construction.  The old Paper2
source has three coordinates per edge; only its generic item and counting
lemmas are imported.  Activity here is defined directly on one edge per group.
-/

namespace CurrentAdditive.EdgeSource

open Paper2

variable {G V E A B : Type*}

abbrev Item (G V A : Type*) := SourceItems.Item G V A
abbrev Coord (G E : Type*) := G × E

def active (edge : E → Bool → V) (c : Coord G E) (i : Item G V A) : Prop :=
  i.1 = c.1 ∧ (match i.2 with
    | .inl v => v = edge c.2 false ∨ v = edge c.2 true
    | .inr _ => True)

theorem active_eq_old (edge : E → Bool → V) (c : Coord G E) (i : Item G V A) :
    active edge c i ↔ SourceItems.groupedActive edge (c.1, (c.2, none)) i := by
  cases c with
  | mk g e =>
    cases i with
    | mk g' i =>
      cases i <;> simp [active, SourceItems.groupedActive, SourceItems.active]

@[simp] theorem card_coord [Fintype G] [Fintype E] :
    Fintype.card (Coord G E) = Fintype.card G * Fintype.card E := by
  simp [Coord]

def sourceQ0 (G E : Type*) [Fintype G] [Fintype E] : ℕ :=
  SourcePadding.powTwoCeil (Fintype.card (Coord G E))

abbrev SourceCoord (G E : Type*) [Fintype G] [Fintype E] (r : ℕ) :=
  SourcePadding.Repeated (Coord G E) (sourceQ0 G E) r

def sourceActive [Fintype G] [Fintype E] (edge : E → Bool → V) (r : ℕ) :
    SourceCoord G E r → Item G V A → Prop :=
  SourcePadding.repeatedActive (active edge) (sourceQ0 G E) r

theorem card_sourceCoord [Fintype G] [Fintype E] (r : ℕ) :
    Fintype.card (SourceCoord G E r) = sourceQ0 G E * r :=
  SourcePadding.card_repeated (SourcePadding.le_powTwoCeil _)

theorem card_sourceCoord_div [Fintype G] [Fintype E] (q₂ : ℕ)
    (hdiv : sourceQ0 G E ∣ q₂) :
    Fintype.card (SourceCoord G E (q₂ / sourceQ0 G E)) = q₂ := by
  rw [card_sourceCoord]
  exact Nat.mul_div_cancel' hdiv

theorem sourceQ0_pow_two [Fintype G] [Fintype E] :
    ∃ k : ℕ, sourceQ0 G E = 2 ^ k := by
  exact ⟨Nat.clog 2 (Fintype.card (Coord G E)), rfl⟩

theorem sourceQ0_pos [Fintype G] [Fintype E] : 0 < sourceQ0 G E := by
  obtain ⟨k, hk⟩ := sourceQ0_pow_two (G := G) (E := E)
  rw [hk]
  positivity

theorem sourceQ0_literal [Fintype E] (s : ℕ) :
    sourceQ0 (Fin (4 * s)) E =
      SourcePadding.powTwoCeil (4 * s * Fintype.card E) := by
  simp [sourceQ0, Coord]

theorem sourceQ2_pos [Fintype G] [Fintype E] {r : ℕ} (hr : 0 < r) :
    0 < sourceQ0 G E * r := Nat.mul_pos sourceQ0_pos hr

theorem padding_inactive [Fintype G] [Fintype E]
    (edge : E → Bool → V) (r : ℕ)
    (j : Fin (sourceQ0 G E - Fintype.card (Coord G E)))
    (k : Fin r) (i : Item G V A) :
    ¬ sourceActive edge r (.inr j, k) i := by
  simp [sourceActive, SourcePadding.repeatedActive, SourcePadding.paddedActive]

theorem card_active_le (edge : E → Bool → V) {s : ℕ} (hs : 3 ≤ s)
    (c : Coord G E) :
    Nat.card {i : Item G V (Fin (s - 3)) // active edge c i} ≤ s := by
  classical
  let f : {i : Item G V (Fin (s - 3)) // active edge c i} → Fin s :=
    fun i => SourceItems.publicSlot edge hs (c.2, none) i.val.2
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    have hi := (active_eq_old edge c i.val).mp i.property
    have hj := (active_eq_old edge c j.val).mp j.property
    exact Prod.ext (hi.1.trans hj.1.symm)
      (SourceItems.publicSlot_active_injective edge hs (c.2, none)
        hi.2 hj.2 hij)
  simpa using Nat.card_le_card_of_injective f hf

/-- The active vertex endpoints receive positions 0 and 1; auxiliary
positions start at 2.  Padding carries no active positions. -/
noncomputable def sourceActivity [Fintype G] [Fintype E]
    (edge : E → Bool → V) {s : ℕ} (hs : 3 ≤ s) (r : ℕ)
    (i : Item G V (Fin (s - 3))) (c : SourceCoord G E r) : Option (Fin s) :=
  match c.1 with
  | .inl c => SourceItems.activity edge hs i (c.1, (c.2, none))
  | .inr _ => none

theorem sourceActivity_some_iff [Fintype G] [Fintype E]
    (edge : E → Bool → V) {s : ℕ} (hs : 3 ≤ s) (r : ℕ)
    (i : Item G V (Fin (s - 3))) (c : SourceCoord G E r) :
    (∃ b, sourceActivity edge hs r i c = some b) ↔ sourceActive edge r c i := by
  obtain ⟨c, j⟩ := c
  cases c with
  | inl c => simp [sourceActivity, SourceItems.activity_some_iff,
      sourceActive, SourcePadding.repeatedActive, SourcePadding.paddedActive,
      active_eq_old]
  | inr c => simp [sourceActivity, sourceActive,
      SourcePadding.repeatedActive, SourcePadding.paddedActive]

theorem sourceActivity_position_injective [Fintype G] [Fintype E]
    (edge : E → Bool → V) {s : ℕ} (hs : 3 ≤ s) (r : ℕ)
    (c : SourceCoord G E r) {i j : Item G V (Fin (s - 3))} {b : Fin s}
    (hi : sourceActivity edge hs r i c = some b)
    (hj : sourceActivity edge hs r j c = some b) : i = j := by
  obtain ⟨c, k⟩ := c
  cases c with
  | inl c => exact SourceItems.activity_position_injective edge hs (c.1, (c.2, none)) hi hj
  | inr c => simp [sourceActivity] at hi

theorem source_yes [Fintype G] [Fintype E]
    (edge : E → Bool → V) {s : ℕ} (hs : 3 ≤ s) (r : ℕ)
    (colour : V → Fin 3) (proper : ∀ e, colour (edge e false) ≠ colour (edge e true))
    (c : SourceCoord G E r) :
    Set.InjOn (SourceItems.yesAssignment hs colour)
      {i | sourceActive edge r c i} := by
  apply SourcePadding.repeated_active_injective (active edge)
    (SourceItems.yesAssignment hs colour) _ (sourceQ0 G E) r c
  intro c i hi j hj hij
  apply SourceItems.grouped_yes edge colour proper (c.1, (c.2, none))
    ((active_eq_old edge c i).mp hi) ((active_eq_old edge c j).mp hj)
  exact (SourceItems.binEquiv hs).injective hij

/-- Every old incidence collision is also a collision at its edge coordinate.
This is a proved transport, not an identification of the two coordinate sets. -/
theorem old_active_implies_edge (edge : E → Bool → V)
    (e : E) (o : Option Bool) (i : SourceItems.LocalItem V A)
    (h : SourceItems.active edge (e, o) i) :
    SourceItems.active edge (e, none) i := by
  cases i with
  | inr a => trivial
  | inl v =>
    cases o with
    | none => exact h
    | some b =>
      cases b with
      | false => exact Or.inl h
      | true => exact Or.inr h

noncomputable def edgeCollisions [Fintype E] (edge : E → Bool → V)
    (keep : SourceItems.LocalItem V A → Prop)
    (bin : SourceItems.LocalItem V A → B) : Finset E := by
  classical
  exact Finset.univ.filter (fun e => SourceItems.Collision edge keep bin (e, none))

@[simp] theorem mem_edgeCollisions [Fintype E] (edge : E → Bool → V)
    (keep : SourceItems.LocalItem V A → Prop)
    (bin : SourceItems.LocalItem V A → B) (e : E) :
    e ∈ edgeCollisions edge keep bin ↔
      SourceItems.Collision edge keep bin (e, none) := by
  classical
  simp [edgeCollisions]

theorem old_collision_implies_edge (edge : E → Bool → V)
    (keep : SourceItems.LocalItem V A → Prop)
    (bin : SourceItems.LocalItem V A → B) (e : E) (o : Option Bool)
    (h : SourceItems.Collision edge keep bin (e, o)) :
    SourceItems.Collision edge keep bin (e, none) := by
  obtain ⟨i, j, hij, hi, hj, hai, haj, hb⟩ := h
  exact ⟨i, j, hij, hi, hj, old_active_implies_edge edge e o i hai,
    old_active_implies_edge edge e o j haj, hb⟩

theorem card_old_collisions_le_three_edge [Fintype E]
    (edge : E → Bool → V)
    (keep : SourceItems.LocalItem V A → Prop)
    (bin : SourceItems.LocalItem V A → B) :
    (SourceItems.collisions edge keep bin).card ≤
      3 * (edgeCollisions edge keep bin).card := by
  classical
  have hsub : SourceItems.collisions edge keep bin ⊆
      (edgeCollisions edge keep bin).product
        (Finset.univ : Finset (Option Bool)) := by
    intro eo heo
    have hc : SourceItems.Collision edge keep bin eo := by
      simpa [SourceItems.collisions] using heo
    exact Finset.mem_product.mpr ⟨(mem_edgeCollisions edge keep bin eo.1).mpr
      (old_collision_implies_edge edge keep bin eo.1 eo.2 hc), Finset.mem_univ _⟩
  have hc := Finset.card_le_card hsub
  simpa [Finset.card_product, Nat.mul_comm] using hc

theorem local_edge_collision_sixth [Fintype V] [Fintype E] [Fintype A] [Fintype B]
    (edge : E → Bool → V) (loopless : ∀ e, edge e false ≠ edge e true)
    (keep : SourceItems.LocalItem V A → Prop)
    (bin : SourceItems.LocalItem V A → B)
    (allAux : ∀ a, keep (.inr a))
    (hcard : Fintype.card B ≤ Fintype.card A + 3)
    (Δ : ℕ) (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (γ : ℝ) (hγ : γ ≤ 1)
    (gap : ∀ colour : V → Fin 3, γ * Fintype.card E ≤
      ((Finset.univ.filter (fun e => colour (edge e false) = colour (edge e true))).card : ℝ))
    (hdelete : (Δ : ℝ) * (SourceItems.deletedVertices keep).card ≤
      γ * Fintype.card E / 2) :
    γ * Fintype.card E / 6 ≤ (edgeCollisions edge keep bin).card := by
  have hlocal := SourceItems.local_collision_half_gap edge loopless keep bin
    allAux hcard Δ hdegree γ hγ gap hdelete
  have hthree := card_old_collisions_le_three_edge edge keep bin
  have hthree' : ((SourceItems.collisions edge keep bin).card : ℝ) ≤
      3 * ((edgeCollisions edge keep bin).card : ℝ) := by exact_mod_cast hthree
  linarith

noncomputable def witnesses [Fintype G] [Fintype E]
    (edge : E → Bool → V) (keep : Item G V A → Prop)
    (bin : Item G V A → B) : Finset (Coord G E) :=
  SourcePadding.witnessCoords (active edge) keep bin

/-- A foreign retained item supplies the required inactive third item. -/
theorem edge_collision_to_witness [Fintype G]
    (edge : E → Bool → V) (K : Finset (Item G V A))
    (bin : Item G V A → B) (g : G) (e : E)
    (hg : g ∉ SourceExclusiveBins.exclusiveGroups Prod.fst bin K)
    (hc : SourceItems.Collision edge (fun i => (g, i) ∈ K)
      (fun i => bin (g, i)) (e, none)) :
    SourcePadding.Witness (active edge) (fun i => i ∈ K) bin (g, e) := by
  obtain ⟨i, j, hij, hi, hj, hai, haj, hbin⟩ := hc
  obtain ⟨h, hh, hbinh, hforeign⟩ :=
    SourceExclusiveBins.exists_foreign_of_not_mem Prod.fst bin K hi hg
  refine ⟨(g, i), (g, j), h, ?_, hi, hj, hh,
    (active_eq_old edge (g, e) (g, i)).mpr ⟨rfl, hai⟩,
    (active_eq_old edge (g, e) (g, j)).mpr ⟨rfl, haj⟩,
    ?_, hbin, hbinh.symm⟩
  · exact fun h => hij (congrArg Prod.snd h)
  · exact fun h => hforeign h.1

theorem sum_edge_collisions_le_witnesses [Fintype G] [Fintype E]
    (edge : E → Bool → V) (K : Finset (Item G V A))
    (bin : Item G V A → B) (H : Finset G)
    (hH : ∀ g ∈ H, g ∉ SourceExclusiveBins.exclusiveGroups Prod.fst bin K) :
    (∑ g ∈ H, (edgeCollisions edge (fun i => (g, i) ∈ K)
      (fun i => bin (g, i))).card) ≤
      (witnesses edge (fun i => i ∈ K) bin).card := by
  classical
  let W := witnesses edge (fun i => i ∈ K) bin
  have hf (g : G) (hg : g ∈ H) :
      (edgeCollisions edge (fun i => (g, i) ∈ K)
        (fun i => bin (g, i))).card ≤
        (W.filter (fun c => c.1 = g)).card := by
    apply Finset.card_le_card_of_injOn (fun e => (g, e))
    · intro e he
      apply Finset.mem_filter.mpr
      refine ⟨?_, rfl⟩
      exact (SourcePadding.mem_witnessCoords _ _ _ _).mpr
        (edge_collision_to_witness edge K bin g e (hH g hg)
          ((mem_edgeCollisions edge _ _ e).mp he))
    · intro e _ f _ hef
      exact congrArg Prod.snd hef
  calc
    _ ≤ ∑ g ∈ H, (W.filter (fun c => c.1 = g)).card := Finset.sum_le_sum hf
    _ = (W.filter (fun c => c.1 ∈ H)).card :=
      Finset.sum_card_fiberwise_eq_card_filter W H Prod.fst
    _ ≤ W.card := Finset.card_filter_le _ _

theorem grouped_no [Fintype G] [Fintype V] [Fintype E] [Fintype A] [Fintype B]
    (edge : E → Bool → V) (loopless : ∀ e, edge e false ≠ edge e true)
    (K : Finset (Item G V A)) (bin : Item G V A → B)
    (s Δ : ℕ) (hgroups : Fintype.card G = 4 * s)
    (hbins : Fintype.card B = s)
    (hcard : Fintype.card B ≤ Fintype.card A + 3)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (γ D : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hD : 0 < D)
    (hE : 0 < Fintype.card E)
    (hDgap : (Δ : ℝ) * D ≤ γ * Fintype.card E / 2)
    (gap : ∀ colour : V → Fin 3, γ * Fintype.card E ≤
      ((Finset.univ.filter (fun e => colour (edge e false) = colour (edge e true))).card : ℝ))
    (hd : (∑ g, ((SourceItems.deletedVertices
      (fun i => (g, i) ∈ K)).card : ℝ)) < (s : ℝ) / 2 * D)
    (ha : (∑ g, ((SourceItems.deletedAuxiliaries
      (fun i => (g, i) ∈ K)).card : ℝ)) < (s : ℝ) / 2) :
    γ * s * Fintype.card E / 3 <
      (witnesses edge (fun i => i ∈ K) bin).card := by
  classical
  let d : G → ℕ := fun g => (SourceItems.deletedVertices
    (fun i => (g, i) ∈ K)).card
  let a : G → ℕ := fun g => (SourceItems.deletedAuxiliaries
    (fun i => (g, i) ∈ K)).card
  let X := SourceExclusiveBins.exclusiveGroups Prod.fst bin K
  let H := SourceGroupCounting.goodGroups d a D \ X
  have hX : X.card ≤ s := by
    simpa only [hbins] using SourceExclusiveBins.card_exclusiveGroups_le Prod.fst bin K
  have hH : 2 * (s : ℝ) < (H.card : ℝ) :=
    SourceGroupCounting.two_mul_lt_card_remaining d a hgroups hD hd ha X hX
  have hlocal (g : G) (hg : g ∈ H) :
      γ * Fintype.card E / 6 ≤
        ((edgeCollisions edge (fun i => (g, i) ∈ K)
          (fun i => bin (g, i))).card : ℝ) := by
    obtain ⟨hag, hdg⟩ :=
      (SourceGroupCounting.mem_goodGroups d a D g).mp (Finset.mem_sdiff.mp hg).1
    have haux : ∀ b : A, (g, Sum.inr b) ∈ K := by
      have he : SourceItems.deletedAuxiliaries (fun i => (g, i) ∈ K) = ∅ :=
        Finset.card_eq_zero.mp hag
      intro b
      by_contra hb
      have hm : b ∈ SourceItems.deletedAuxiliaries
          (fun i => (g, i) ∈ K) := by
        simpa [SourceItems.deletedAuxiliaries] using hb
      simp [he] at hm
    apply local_edge_collision_sixth edge loopless _ _ haux hcard Δ hdegree γ hγ1 gap
    exact (mul_le_mul_of_nonneg_left hdg (Nat.cast_nonneg Δ)).trans hDgap
  have hsum : (H.card : ℝ) * (γ * Fintype.card E / 6) ≤
      (witnesses edge (fun i => i ∈ K) bin).card := by
    calc
      _ = ∑ _g ∈ H, γ * Fintype.card E / 6 := by simp
      _ ≤ ∑ g ∈ H,
          ((edgeCollisions edge (fun i => (g, i) ∈ K)
            (fun i => bin (g, i))).card : ℝ) :=
        Finset.sum_le_sum hlocal
      _ ≤ _ := by
        exact_mod_cast sum_edge_collisions_le_witnesses edge K bin H
          (fun g hg => (Finset.mem_sdiff.mp hg).2)
  have hp : 0 < γ * (Fintype.card E : ℝ) / 6 :=
    div_pos (mul_pos hγ (Nat.cast_pos.mpr hE)) (by norm_num)
  have hm := mul_lt_mul_of_pos_right hH hp
  nlinarith

theorem grouped_no_counted [Fintype G] [Fintype V] [Fintype E]
    [Fintype A] [Fintype B]
    (edge : E → Bool → V) (loopless : ∀ e, edge e false ≠ edge e true)
    (K : Finset (Item G V A)) (bin : Item G V A → B)
    (s Δ : ℕ) (hgroups : Fintype.card G = 4 * s)
    (hbins : Fintype.card B = s)
    (hcard : Fintype.card B ≤ Fintype.card A + 3)
    (hΔ : 0 < Δ) (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (γ : ℝ) (hγ : 0 < γ) (hE : 0 < Fintype.card E)
    (gap : ∀ colour : V → Fin 3, γ * Fintype.card E ≤
      ((Finset.univ.filter (fun e => colour (edge e false) = colour (edge e true))).card : ℝ))
    (hd : ((SourceItems.deletedVertexItems K).card : ℝ) <
      (s : ℝ) / 2 * (γ * Fintype.card E / (2 * Δ)))
    (ha : ((SourceItems.deletedAuxiliaryItems K).card : ℝ) < (s : ℝ) / 2) :
    γ * s * Fintype.card E / 3 <
      (witnesses edge (fun i => i ∈ K) bin).card := by
  have hΔ' : (0 : ℝ) < Δ := Nat.cast_pos.mpr hΔ
  have hE' : (0 : ℝ) < Fintype.card E := Nat.cast_pos.mpr hE
  have hγ1 : γ ≤ 1 := by
    have hc := gap (fun _ => 0)
    simp at hc
    nlinarith
  apply grouped_no edge loopless K bin s Δ hgroups hbins hcard hdegree
    γ (γ * Fintype.card E / (2 * Δ)) hγ hγ1
    (div_pos (mul_pos hγ hE') (mul_pos (by norm_num) hΔ')) hE
  · have heq : (Δ : ℝ) * (γ * Fintype.card E / (2 * Δ)) =
        γ * Fintype.card E / 2 := by field_simp
    exact heq.le
  · exact gap
  · simpa only [SourceItems.card_deletedVertexItems, Nat.cast_sum] using hd
  · simpa only [SourceItems.card_deletedAuxiliaryItems, Nat.cast_sum] using ha

theorem source_fraction [Fintype G] [Fintype E]
    (edge : E → Bool → V) (K : Finset (Item G V A))
    (bin : Item G V A → B) (s r : ℕ) (hs : 0 < s)
    (hgroups : Fintype.card G = 4 * s) (hE : 0 < Fintype.card E)
    (γ : ℝ) (hγ : 0 ≤ γ)
    (hw : γ * s * Fintype.card E / 3 ≤
      (witnesses edge (fun i => i ∈ K) bin).card) :
    γ / 24 * (sourceQ0 G E * r) ≤
      (SourcePadding.witnessCoords (sourceActive edge r)
        (fun i => i ∈ K) bin).card := by
  have hc : Fintype.card (Coord G E) = 4 * s * Fintype.card E := by
    rw [card_coord, hgroups]
  have hcp : 0 < Fintype.card (Coord G E) := by rw [hc]; positivity
  have hq : (sourceQ0 G E : ℝ) ≤ 8 * s * Fintype.card E := by
    have hn : sourceQ0 G E ≤ 8 * s * Fintype.card E := by
      have hb := (SourcePadding.powTwoCeil_lt_two_mul hcp).le
      unfold sourceQ0
      rw [hc] at hb ⊢
      calc
        _ ≤ 2 * (4 * s * Fintype.card E) := hb
        _ = 8 * s * Fintype.card E := by ring
    exact_mod_cast hn
  have hqw : γ / 24 * (sourceQ0 G E : ℝ) ≤
      (witnesses edge (fun i => i ∈ K) bin).card := by
    have hm := mul_le_mul_of_nonneg_left hq
      (div_nonneg hγ (by norm_num : (0 : ℝ) ≤ 24))
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hqw
    (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
  rw [sourceActive, SourcePadding.card_witnessCoords_repeated]
  change γ / 24 * (sourceQ0 G E * r) ≤
    ((witnesses edge (fun i => i ∈ K) bin).card * r : ℕ)
  push_cast
  nlinarith

/-- The literal v37 edge-only source witness, with `4s|E|` unpadded
coordinates, inactive power-of-two padding and labelled repetition. -/
theorem collisions_after_deletion [Fintype V] [Fintype E]
    (edge : E → Bool → V) (loopless : ∀ e, edge e false ≠ edge e true)
    {s : ℕ} (hs : 4 ≤ s) (r Δ : ℕ) (hΔ : 0 < Δ)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (K : Finset (Item (Fin (4 * s)) V (Fin (s - 3))))
    (bin : Item (Fin (4 * s)) V (Fin (s - 3)) → Fin s)
    (γ : ℝ) (hγ : 0 < γ) (hE : 0 < Fintype.card E)
    (gap : ∀ colour : V → Fin 3, γ * Fintype.card E ≤
      ((Finset.univ.filter (fun e => colour (edge e false) = colour (edge e true))).card : ℝ))
    (hd : ((SourceItems.deletedVertexItems K).card : ℝ) <
      (s : ℝ) / 2 * (γ * Fintype.card E / (2 * Δ)))
    (ha : ((SourceItems.deletedAuxiliaryItems K).card : ℝ) < (s : ℝ) / 2) :
    γ / 24 * (sourceQ0 (Fin (4 * s)) E * r) ≤
      (SourcePadding.witnessCoords (sourceActive edge r)
        (fun i => i ∈ K) bin).card := by
  apply source_fraction edge K bin s r (by omega) (by simp) hE γ hγ.le
  exact (grouped_no_counted edge loopless K bin s Δ (by simp) (by simp)
    (by simp only [Fintype.card_fin]; omega) hΔ hdegree γ hγ hE gap hd ha).le

/-- The same witness statement for assignments defined only on retained items. -/
theorem collisions_after_deletion_retained [Fintype V] [Fintype E]
    (edge : E → Bool → V) (loopless : ∀ e, edge e false ≠ edge e true)
    {s : ℕ} (hs : 4 ≤ s) (r Δ : ℕ) (hΔ : 0 < Δ)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (K : Finset (Item (Fin (4 * s)) V (Fin (s - 3))))
    (bin : {i // i ∈ K} → Fin s)
    (γ : ℝ) (hγ : 0 < γ) (hE : 0 < Fintype.card E)
    (gap : ∀ colour : V → Fin 3, γ * Fintype.card E ≤
      ((Finset.univ.filter (fun e => colour (edge e false) = colour (edge e true))).card : ℝ))
    (hd : ((SourceItems.deletedVertexItems K).card : ℝ) <
      (s : ℝ) / 2 * (γ * Fintype.card E / (2 * Δ)))
    (ha : ((SourceItems.deletedAuxiliaryItems K).card : ℝ) < (s : ℝ) / 2) :
    γ / 24 * (sourceQ0 (Fin (4 * s)) E * r) ≤
      (SourcePadding.witnessCoords (sourceActive edge r)
        (fun i => i ∈ K)
        (SourceItems.extendBins (by omega : 0 < s) K bin)).card := by
  exact collisions_after_deletion edge loopless hs r Δ hΔ hdegree K
    (SourceItems.extendBins (by omega) K bin) γ hγ hE gap hd ha

#print axioms active_eq_old
#print axioms card_coord
#print axioms card_sourceCoord
#print axioms card_sourceCoord_div
#print axioms sourceQ0_pow_two
#print axioms sourceQ0_pos
#print axioms sourceQ0_literal
#print axioms sourceQ2_pos
#print axioms padding_inactive
#print axioms card_active_le
#print axioms sourceActivity_some_iff
#print axioms sourceActivity_position_injective
#print axioms source_yes
#print axioms old_active_implies_edge
#print axioms old_collision_implies_edge
#print axioms card_old_collisions_le_three_edge
#print axioms local_edge_collision_sixth
#print axioms edge_collision_to_witness
#print axioms sum_edge_collisions_le_witnesses
#print axioms grouped_no
#print axioms grouped_no_counted
#print axioms source_fraction
#print axioms collisions_after_deletion
#print axioms collisions_after_deletion_retained

end CurrentAdditive.EdgeSource
