import Mathlib
import Paper2.SourceExclusiveBins
import Paper2.SourceGroupCounting
import Paper2.SourcePadding

/-!
# The colouring-to-item construction

Frozen v12, Section 4, `src:item-witness`. Edge occurrences retain their
labels, including parallel edges. A coordinate is either an edge occurrence
or one of its two labelled incidences. All auxiliary items of its group are
active; items of other groups are inactive. The constructor never consults
a colouring. The external gap-colouring reduction is not proved here.
-/

namespace Paper2.SourceItems

variable {V E A B G : Type*}

abbrev LocalItem (V A : Type*) := V ⊕ A
abbrev LocalCoord (E : Type*) := E × Option Bool
abbrev Item (G V A : Type*) := G × LocalItem V A
abbrev Coord (G E : Type*) := G × LocalCoord E

/-- `none` is the edge coordinate; `some b` is its endpoint incidence. -/
def active (edge : E → Bool → V) (c : LocalCoord E) : LocalItem V A → Prop
  | .inr _ => True
  | .inl v => match c.2 with
    | none => v = edge c.1 false ∨ v = edge c.1 true
    | some b => v = edge c.1 b

def groupedActive (edge : E → Bool → V) (c : Coord G E) (i : Item G V A) : Prop :=
  i.1 = c.1 ∧ active edge c.2 i.2

def Collision (edge : E → Bool → V) (keep : LocalItem V A → Prop)
    (bin : LocalItem V A → B) (c : LocalCoord E) : Prop :=
  ∃ i j, i ≠ j ∧ keep i ∧ keep j ∧ active edge c i ∧ active edge c j ∧ bin i = bin j

def Witness (edge : E → Bool → V) (keep : Item G V A → Prop)
    (bin : Item G V A → B) (c : Coord G E) : Prop :=
  ∃ i j h, i ≠ j ∧ keep i ∧ keep j ∧ keep h ∧
    groupedActive edge c i ∧ groupedActive edge c j ∧ ¬ groupedActive edge c h ∧
    bin i = bin j ∧ bin i = bin h

@[simp] theorem card_localCoord [Fintype E] :
    Fintype.card (LocalCoord E) = 3 * Fintype.card E := by
  simp [LocalCoord, Fintype.card_option, Nat.mul_comm]

@[simp] theorem card_coord [Fintype G] [Fintype E] :
    Fintype.card (Coord G E) = 3 * Fintype.card G * Fintype.card E := by
  simp [Coord, Nat.mul_left_comm, Nat.mul_comm]

@[simp] theorem card_items [Fintype G] [Fintype V] [Fintype A] :
    Fintype.card (Item G V A) = Fintype.card G * (Fintype.card V + Fintype.card A) := by
  simp [Item, LocalItem]

theorem card_source_items [Fintype V] (s : ℕ) :
    Fintype.card (Item (Fin (4 * s)) V (Fin (s - 3))) =
      4 * s * (Fintype.card V + (s - 3)) := by
  simp

/-- The public YES assignment uses three vertex bins and separate auxiliary
bins. The same assignment is reused in every group. -/
def properAssignment (colour : V → Fin 3) : LocalItem V A → (Fin 3 ⊕ A) :=
  Sum.map colour id

theorem properAssignment_active_injective (edge : E → Bool → V)
    (colour : V → Fin 3) (proper : ∀ e, colour (edge e false) ≠ colour (edge e true))
    (c : LocalCoord E) : Set.InjOn (properAssignment (A := A) colour)
      {i | active edge c i} := by
  intro i hi j hj hij
  cases i with
  | inr a =>
    cases j with
    | inl v => simp [properAssignment] at hij
    | inr b => simpa [properAssignment] using hij
  | inl v =>
    cases j with
    | inr b => simp [properAssignment] at hij
    | inl w =>
      have heq : colour v = colour w := by simpa [properAssignment] using hij
      obtain ⟨e, o⟩ := c
      cases o with
      | some b =>
        change v = edge e b at hi
        change w = edge e b at hj
        simp [hi, hj]
      | none =>
        change v = edge e false ∨ v = edge e true at hi
        change w = edge e false ∨ w = edge e true at hj
        rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
        · rfl
        · exact False.elim (proper e heq)
        · exact False.elim (proper e heq.symm)
        · rfl

theorem grouped_yes (edge : E → Bool → V) (colour : V → Fin 3)
    (proper : ∀ e, colour (edge e false) ≠ colour (edge e true))
    (c : Coord G E) : Set.InjOn
      (fun i : Item G V A => properAssignment colour i.2)
      {i | groupedActive edge c i} := by
  intro i hi j hj hij
  exact Prod.ext (hi.1.trans hj.1.symm)
    (properAssignment_active_injective edge colour proper c.2 hi.2 hj.2 hij)

/-- Public active positions, independent of every colouring, retained set,
or bin assignment: endpoint slots are 0 and 1, auxiliary slots start at 2.
This is an explicit injection, not an identification with a separately chosen
dense ordinal enumeration of the active items. The T11 activity/witness
theorems do not depend on which public injection is subsequently used. -/
noncomputable def publicSlot (edge : E → Bool → V) {s : ℕ} (hs : 3 ≤ s)
    (c : LocalCoord E) : LocalItem V (Fin (s - 3)) → Fin s := by
  classical
  exact fun i => match i with
    | .inl v => if v = edge c.1 false then ⟨0, by omega⟩ else ⟨1, by omega⟩
    | .inr a => ⟨a.val + 2, by omega⟩

theorem publicSlot_active_injective (edge : E → Bool → V) {s : ℕ} (hs : 3 ≤ s)
    (c : LocalCoord E) : Set.InjOn (publicSlot edge hs c) {i | active edge c i} := by
  classical
  intro i hi j hj hij
  have hv := congrArg Fin.val hij
  cases i with
  | inr a =>
    cases j with
    | inr b =>
      apply congrArg Sum.inr
      apply Fin.ext
      simpa [publicSlot] using hv
    | inl w =>
      by_cases h : w = edge c.1 false <;> simp [publicSlot, h] at hv
  | inl v =>
    cases j with
    | inr b =>
      by_cases h : v = edge c.1 false <;> simp [publicSlot, h] at hv
    | inl w =>
      obtain ⟨e, o⟩ := c
      cases o with
      | some b =>
        change v = edge e b at hi
        change w = edge e b at hj
        simp [hi, hj]
      | none =>
        change v = edge e false ∨ v = edge e true at hi
        change w = edge e false ∨ w = edge e true at hj
        rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
        · rfl
        · by_cases h : edge e false = edge e true
          · exact congrArg Sum.inl h
          · simp [publicSlot, Ne.symm h] at hv
        · by_cases h : edge e false = edge e true
          · exact congrArg Sum.inl h.symm
          · simp [publicSlot, Ne.symm h] at hv
        · rfl

/-- Optional active positions in the exact shape consumed by the source
matrix. The activity map is fixed before any proper colouring is supplied. -/
noncomputable def activity (edge : E → Bool → V) {s : ℕ} (hs : 3 ≤ s)
    (i : Item G V (Fin (s - 3))) (c : Coord G E) : Option (Fin s) := by
  classical
  exact if groupedActive edge c i then some (publicSlot edge hs c.2 i.2) else none

theorem activity_some_iff (edge : E → Bool → V) {s : ℕ} (hs : 3 ≤ s)
    (i : Item G V (Fin (s - 3))) (c : Coord G E) (r : Fin s) :
    activity edge hs i c = some r ↔
      groupedActive edge c i ∧ publicSlot edge hs c.2 i.2 = r := by
  classical
  by_cases h : groupedActive edge c i <;> simp [activity, h]

theorem activity_position_injective (edge : E → Bool → V) {s : ℕ} (hs : 3 ≤ s)
    (c : Coord G E) {i j : Item G V (Fin (s - 3))} {r : Fin s}
    (hi : activity edge hs i c = some r) (hj : activity edge hs j c = some r) : i = j := by
  obtain ⟨hai, hri⟩ := (activity_some_iff edge hs i c r).mp hi
  obtain ⟨haj, hrj⟩ := (activity_some_iff edge hs j c r).mp hj
  exact Prod.ext (hai.1.trans haj.1.symm)
    (publicSlot_active_injective edge hs c.2 hai.2 haj.2 (hri.trans hrj.symm))

/-- YES correctness in the matrix-facing optional-activity interface. -/
theorem activity_yes (edge : E → Bool → V) {s : ℕ} (hs : 3 ≤ s)
    (colour : V → Fin 3) (proper : ∀ e, colour (edge e false) ≠ colour (edge e true))
    (c : Coord G E) {i j : Item G V (Fin (s - 3))} {r r' : Fin s}
    (hi : activity edge hs i c = some r) (hj : activity edge hs j c = some r')
    (hbin : properAssignment colour i.2 = properAssignment colour j.2) : i = j :=
  grouped_yes edge colour proper c ((activity_some_iff edge hs i c r).mp hi).1
    ((activity_some_iff edge hs j c r').mp hj).1 hbin

theorem card_active_le
    (edge : E → Bool → V) {s : ℕ} (hs : 3 ≤ s) (c : Coord G E) :
    Nat.card {i : Item G V (Fin (s - 3)) // groupedActive edge c i} ≤ s := by
  classical
  let f : {i : Item G V (Fin (s - 3)) // groupedActive edge c i} → Fin s :=
    fun i => publicSlot edge hs c.2 i.val.2
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    exact Prod.ext (i.property.1.trans j.property.1.symm)
      (publicSlot_active_injective edge hs c.2 i.property.2 j.property.2 hij)
  simpa using Nat.card_le_card_of_injective f hf

/-- Relabel the three vertex bins and `s-3` auxiliary bins by `[s]`. -/
noncomputable def binEquiv {s : ℕ} (hs : 3 ≤ s) : (Fin 3 ⊕ Fin (s - 3)) ≃ Fin s :=
  Fintype.equivOfCardEq (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)

noncomputable def yesAssignment {s : ℕ} (hs : 3 ≤ s) (colour : V → Fin 3) :
    Item G V (Fin (s - 3)) → Fin s :=
  fun i => binEquiv hs (properAssignment colour i.2)

theorem yesAssignment_collisionFree (edge : E → Bool → V) {s : ℕ} (hs : 3 ≤ s)
    (colour : V → Fin 3) (proper : ∀ e, colour (edge e false) ≠ colour (edge e true))
    (c : Coord G E) {i j : Item G V (Fin (s - 3))} {r r' : Fin s}
    (hi : activity edge hs i c = some r) (hj : activity edge hs j c = some r')
    (hbin : yesAssignment hs colour i = yesAssignment hs colour j) : i = j := by
  apply activity_yes edge hs colour proper c hi hj
  exact (binEquiv hs).injective hbin

/-- A collision of auxiliary items collides at every local coordinate. -/
theorem auxiliary_collision (edge : E → Bool → V) (keep : LocalItem V A → Prop)
    (bin : LocalItem V A → B) (a b : A) (hab : a ≠ b)
    (ha : keep (.inr a)) (hb : keep (.inr b))
    (heq : bin (.inr a) = bin (.inr b)) (c : LocalCoord E) :
    Collision edge keep bin c := by
  exact ⟨.inr a, .inr b, by simpa using hab, ha, hb, trivial, trivial, heq⟩

/-- If a retained vertex uses an auxiliary bin, each of its labelled
incidences is a collision; no looplessness assumption is needed for this. -/
theorem incidence_collision (edge : E → Bool → V) (keep : LocalItem V A → Prop)
    (bin : LocalItem V A → B) (e : E) (b : Bool) (a : A)
    (hv : keep (.inl (edge e b))) (ha : keep (.inr a))
    (heq : bin (.inl (edge e b)) = bin (.inr a)) :
    Collision edge keep bin (e, some b) := by
  exact ⟨.inl (edge e b), .inr a, by simp, hv, ha, rfl, trivial, heq⟩

/-- At most three bins remain when all auxiliary items occupy different
bins. Their names need not be the last three public bin labels. -/
theorem exists_unused_colour [Fintype A] [Fintype B]
    (aux : A → B) (hinj : Function.Injective aux)
    (hcard : Fintype.card B ≤ Fintype.card A + 3) :
    ∃ colour : B → Fin 3, Set.InjOn colour (Set.range aux)ᶜ := by
  classical
  let emb : A ↪ B := ⟨aux, hinj⟩
  have hrange : Fintype.card (Set.range aux) = Fintype.card A :=
    Fintype.card_range emb
  have hc : Fintype.card {b : B // b ∉ Set.range aux} ≤ 3 := by
    rw [Fintype.card_subtype_compl, hrange]
    omega
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le
    (α := {b : B // b ∉ Set.range aux}) (β := Fin 3) (by simpa only [Fintype.card_fin] using hc)
  refine ⟨fun b => if h : b ∉ Set.range aux then f ⟨b, h⟩ else 0, ?_⟩
  intro b hb c hc hbc
  simp only [Set.mem_compl_iff] at hb hc
  simp only [dif_pos hb, dif_pos hc] at hbc
  exact congrArg Subtype.val (f.injective hbc)

noncomputable def collisions [Fintype E] (edge : E → Bool → V)
    (keep : LocalItem V A → Prop) (bin : LocalItem V A → B) : Finset (LocalCoord E) :=
  by classical exact Finset.univ.filter (Collision edge keep bin)

noncomputable def deletedIncidences [Fintype E] (edge : E → Bool → V)
    (keep : LocalItem V A → Prop) : Finset (E × Bool) :=
  by classical exact Finset.univ.filter (fun eb => ¬ keep (.inl (edge eb.1 eb.2)))

noncomputable def deletedVertices [Fintype V] (keep : LocalItem V A → Prop) : Finset V :=
  by classical exact Finset.univ.filter (fun v => ¬ keep (.inl v))

noncomputable def deletedAuxiliaries [Fintype A] (keep : LocalItem V A → Prop) : Finset A :=
  by classical exact Finset.univ.filter (fun a => ¬ keep (.inr a))

noncomputable def degree [Fintype E] (edge : E → Bool → V) (v : V) : ℕ :=
  by classical exact (Finset.univ.filter (fun eb : E × Bool => edge eb.1 eb.2 = v)).card

/-- Counting labelled incidences treats parallel edges with their actual
multiplicity, exactly as in the bounded-degree graph promise. -/
theorem deletedIncidences_le [Fintype V] [Fintype E]
    (edge : E → Bool → V) (keep : LocalItem V A → Prop) (Δ : ℕ)
    (hdegree : ∀ v, degree edge v ≤ Δ) :
    (deletedIncidences edge keep).card ≤
      Δ * (deletedVertices keep).card := by
  classical
  apply Finset.card_le_mul_card_image_of_maps_to
    (f := fun eb : E × Bool => edge eb.1 eb.2)
    (t := deletedVertices keep)
    (by simp [deletedIncidences, deletedVertices])
  intro v _
  apply le_trans (Finset.card_le_card ?_) (hdegree v)
  intro eb heb
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
    (Finset.mem_filter.mp heb).2

/-- With distinct auxiliary bins, every monochromatic source edge either
already supplies an edge/incidence collision or touches a deleted vertex. -/
theorem monochromatic_certificate [Fintype A] [Fintype B]
    (edge : E → Bool → V) (loopless : ∀ e, edge e false ≠ edge e true)
    (keep : LocalItem V A → Prop) (bin : LocalItem V A → B)
    (allAux : ∀ a, keep (.inr a))
    (hinj : Function.Injective (fun a => bin (.inr a)))
    (hcard : Fintype.card B ≤ Fintype.card A + 3) :
    ∃ colour : V → Fin 3, ∀ e, colour (edge e false) = colour (edge e true) →
      (∃ c : LocalCoord E, c.1 = e ∧ Collision edge keep bin c) ∨
      (∃ b, ¬ keep (.inl (edge e b))) := by
  classical
  obtain ⟨colour, hcolour⟩ := exists_unused_colour (fun a => bin (.inr a)) hinj hcard
  refine ⟨fun v => colour (bin (.inl v)), ?_⟩
  intro e heq
  by_cases hkeep : ∀ b, keep (.inl (edge e b))
  · by_cases haux : ∃ b a, bin (.inl (edge e b)) = bin (.inr a)
    · obtain ⟨b, a, ha⟩ := haux
      exact Or.inl ⟨(e, some b), rfl,
        incidence_collision edge keep bin e b a (hkeep b) (allAux a) ha⟩
    · have hnot (b : Bool) : bin (.inl (edge e b)) ∉ Set.range (fun a => bin (.inr a)) := by
        rintro ⟨a, ha⟩
        exact haux ⟨b, a, ha.symm⟩
      have hb := hcolour (hnot false) (hnot true) heq
      refine Or.inl ⟨(e, none), rfl, .inl (edge e false), .inl (edge e true),
        ?_, hkeep false, hkeep true, Or.inl rfl, Or.inr rfl, hb⟩
      simpa using loopless e
  · exact Or.inr (by simpa only [not_forall] using hkeep)

/-- The entire gap can be charged injectively to local collision coordinates
and deleted labelled incidences. This is the quantitative NO core before
discarding globally exclusive bins. -/
theorem local_collision_gap [Fintype E] [Fintype A] [Fintype B]
    (edge : E → Bool → V) (loopless : ∀ e, edge e false ≠ edge e true)
    (keep : LocalItem V A → Prop) (bin : LocalItem V A → B)
    (allAux : ∀ a, keep (.inr a))
    (hcard : Fintype.card B ≤ Fintype.card A + 3)
    (γ : ℝ) (hγ : γ ≤ 1)
    (gap : ∀ colour : V → Fin 3, γ * Fintype.card E ≤
      ((Finset.univ.filter (fun e => colour (edge e false) = colour (edge e true))).card : ℝ)) :
    γ * Fintype.card E ≤ (collisions edge keep bin).card +
      (deletedIncidences edge keep).card := by
  classical
  by_cases hinj : Function.Injective (fun a => bin (.inr a))
  · obtain ⟨colour, hc⟩ := monochromatic_certificate edge loopless keep bin allAux hinj hcard
    have hs : Finset.univ.filter (fun e => colour (edge e false) = colour (edge e true)) ⊆
        ((collisions edge keep bin).image Prod.fst) ∪
          ((deletedIncidences edge keep).image Prod.fst) := by
      intro e he
      rcases hc e (Finset.mem_filter.mp he).2 with ⟨c, hec, hcoll⟩ | ⟨b, hb⟩
      · apply Finset.mem_union_left
        exact Finset.mem_image.mpr ⟨c, by simpa [collisions] using hcoll, hec⟩
      · apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨(e, b), by simpa [deletedIncidences] using hb, rfl⟩
    have hbound := (Finset.card_le_card hs).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add (Finset.card_image_le)
        (Finset.card_image_le)))
    exact (gap colour).trans (by exact_mod_cast hbound)
  · obtain ⟨a, b, heq, hab⟩ := Function.not_injective_iff.mp hinj
    have hall : collisions edge keep bin = Finset.univ := by
      ext c
      simp only [collisions, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact auxiliary_collision edge keep bin a b hab (allAux a) (allAux b) heq c
    rw [hall, Finset.card_univ, card_localCoord, Nat.cast_mul, Nat.cast_ofNat]
    have he : (0 : ℝ) ≤ Fintype.card E := Nat.cast_nonneg _
    have hd : (0 : ℝ) ≤ (deletedIncidences edge keep).card := Nat.cast_nonneg _
    nlinarith

theorem local_collision_half_gap [Fintype V] [Fintype E] [Fintype A] [Fintype B]
    (edge : E → Bool → V) (loopless : ∀ e, edge e false ≠ edge e true)
    (keep : LocalItem V A → Prop) (bin : LocalItem V A → B)
    (allAux : ∀ a, keep (.inr a))
    (hcard : Fintype.card B ≤ Fintype.card A + 3)
    (Δ : ℕ) (hdegree : ∀ v, degree edge v ≤ Δ)
    (γ : ℝ) (hγ : γ ≤ 1)
    (gap : ∀ colour : V → Fin 3, γ * Fintype.card E ≤
      ((Finset.univ.filter (fun e => colour (edge e false) = colour (edge e true))).card : ℝ))
    (hdelete : (Δ : ℝ) * (deletedVertices keep).card ≤
      γ * Fintype.card E / 2) :
    γ * Fintype.card E / 2 ≤ (collisions edge keep bin).card := by
  have hlocal := local_collision_gap edge loopless keep bin allAux hcard γ hγ gap
  have hd : ((deletedIncidences edge keep).card : ℝ) ≤
      (Δ : ℝ) * (deletedVertices keep).card := by
    exact_mod_cast deletedIncidences_le edge keep Δ hdegree
  linarith

noncomputable def witnesses [Fintype G] [Fintype E]
    (edge : E → Bool → V) (keep : Item G V A → Prop) (bin : Item G V A → B) :
    Finset (Coord G E) := by
  classical exact Finset.univ.filter (Witness edge keep bin)

/-- A nonexclusive group supplies the third, inactive item in every bin
already containing a local active collision. -/
theorem collision_to_witness [Fintype G]
    (edge : E → Bool → V) (K : Finset (Item G V A)) (bin : Item G V A → B)
    (g : G) (c : LocalCoord E)
    (hg : g ∉ SourceExclusiveBins.exclusiveGroups Prod.fst bin K)
    (hc : Collision edge (fun i => (g, i) ∈ K) (fun i => bin (g, i)) c) :
    Witness edge (fun i => i ∈ K) bin (g, c) := by
  obtain ⟨i, j, hij, hi, hj, hai, haj, hbin⟩ := hc
  obtain ⟨h, hh, hbinh, hforeign⟩ :=
    SourceExclusiveBins.exists_foreign_of_not_mem Prod.fst bin K hi hg
  refine ⟨(g, i), (g, j), h, ?_, hi, hj, hh, ⟨rfl, hai⟩, ⟨rfl, haj⟩,
    ?_, hbin, hbinh.symm⟩
  · exact fun h => hij (congrArg Prod.snd h)
  · exact fun h => hforeign h.1

/-- Distinct groups have disjoint coordinate sets, so their local collision
counts add rather than merely contributing a maximum. -/
theorem sum_collisions_le_witnesses [Fintype G] [Fintype E]
    (edge : E → Bool → V) (K : Finset (Item G V A)) (bin : Item G V A → B)
    (H : Finset G)
    (hH : ∀ g ∈ H, g ∉ SourceExclusiveBins.exclusiveGroups Prod.fst bin K) :
    (∑ g ∈ H, (collisions edge (fun i => (g, i) ∈ K) (fun i => bin (g, i))).card) ≤
      (witnesses edge (fun i => i ∈ K) bin).card := by
  classical
  let W := witnesses edge (fun i => i ∈ K) bin
  have hf (g : G) (hg : g ∈ H) :
      (collisions edge (fun i => (g, i) ∈ K) (fun i => bin (g, i))).card ≤
        (W.filter (fun c => c.1 = g)).card := by
    apply Finset.card_le_card_of_injOn (fun c => (g, c))
    · intro c hc
      apply Finset.mem_filter.mpr
      refine ⟨?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        collision_to_witness edge K bin g c (hH g hg) (Finset.mem_filter.mp hc).2⟩
    · intro c _ d _ h
      exact congrArg Prod.snd h
  calc
    _ ≤ ∑ g ∈ H, (W.filter (fun c => c.1 = g)).card := Finset.sum_le_sum hf
    _ = (W.filter (fun c => c.1 ∈ H)).card :=
      Finset.sum_card_fiberwise_eq_card_filter W H Prod.fst
    _ ≤ W.card := Finset.card_filter_le _ _

/-- The quantitative grouped NO statement on real coordinates. Here `D`
is the allowed number of deleted vertices in one good group; the manuscript
uses `D = δ_v n = γ |E| / (2 Δ)`. All bins and retained items are arbitrary. -/
theorem grouped_no [Fintype G] [Fintype V] [Fintype E] [Fintype A] [Fintype B]
    (edge : E → Bool → V) (loopless : ∀ e, edge e false ≠ edge e true)
    (K : Finset (Item G V A)) (bin : Item G V A → B)
    (s Δ : ℕ) (hgroups : Fintype.card G = 4 * s) (hbins : Fintype.card B = s)
    (hcard : Fintype.card B ≤ Fintype.card A + 3)
    (hdegree : ∀ v, degree edge v ≤ Δ)
    (γ D : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hD : 0 < D)
    (hE : 0 < Fintype.card E) (hDgap : (Δ : ℝ) * D ≤ γ * Fintype.card E / 2)
    (gap : ∀ colour : V → Fin 3, γ * Fintype.card E ≤
      ((Finset.univ.filter (fun e => colour (edge e false) = colour (edge e true))).card : ℝ))
    (hd : (∑ g, ((deletedVertices (fun i => (g, i) ∈ K)).card : ℝ)) < (s : ℝ) / 2 * D)
    (ha : (∑ g, ((deletedAuxiliaries (fun i => (g, i) ∈ K)).card : ℝ)) < (s : ℝ) / 2) :
    γ * s * Fintype.card E < (witnesses edge (fun i => i ∈ K) bin).card := by
  classical
  let d : G → ℕ := fun g => (deletedVertices (fun i => (g, i) ∈ K)).card
  let a : G → ℕ := fun g => (deletedAuxiliaries (fun i => (g, i) ∈ K)).card
  let X := SourceExclusiveBins.exclusiveGroups Prod.fst bin K
  let H := SourceGroupCounting.goodGroups d a D \ X
  have hX : X.card ≤ s := by
    simpa only [hbins] using SourceExclusiveBins.card_exclusiveGroups_le Prod.fst bin K
  have hH : 2 * (s : ℝ) < (H.card : ℝ) :=
    SourceGroupCounting.two_mul_lt_card_remaining d a hgroups hD hd ha X hX
  have hlocal (g : G) (hg : g ∈ H) :
      γ * Fintype.card E / 2 ≤
        ((collisions edge (fun i => (g, i) ∈ K) (fun i => bin (g, i))).card : ℝ) := by
    obtain ⟨hag, hdg⟩ :=
      (SourceGroupCounting.mem_goodGroups d a D g).mp (Finset.mem_sdiff.mp hg).1
    have haux : ∀ b : A, (g, Sum.inr b) ∈ K := by
      have he : deletedAuxiliaries (fun i => (g, i) ∈ K) = ∅ := Finset.card_eq_zero.mp hag
      intro b
      by_contra hb
      have hm : b ∈ deletedAuxiliaries (fun i => (g, i) ∈ K) := by
        simpa [deletedAuxiliaries] using hb
      simp [he] at hm
    apply local_collision_half_gap edge loopless _ _ haux hcard Δ hdegree γ hγ1 gap
    exact (mul_le_mul_of_nonneg_left hdg (Nat.cast_nonneg Δ)).trans hDgap
  have hsum : (H.card : ℝ) * (γ * Fintype.card E / 2) ≤
      (witnesses edge (fun i => i ∈ K) bin).card := by
    calc
      _ = ∑ _g ∈ H, γ * Fintype.card E / 2 := by simp
      _ ≤ ∑ g ∈ H,
          ((collisions edge (fun i => (g, i) ∈ K) (fun i => bin (g, i))).card : ℝ) :=
        Finset.sum_le_sum hlocal
      _ ≤ _ := by
        exact_mod_cast sum_collisions_le_witnesses edge K bin H
          (fun g hg => (Finset.mem_sdiff.mp hg).2)
  have hp : 0 < γ * (Fintype.card E : ℝ) / 2 :=
    div_pos (mul_pos hγ (Nat.cast_pos.mpr hE)) (by norm_num)
  have hm := mul_lt_mul_of_pos_right hH hp
  nlinarith

noncomputable def deletedVertexItems [Fintype G] [Fintype V]
    (K : Finset (Item G V A)) : Finset (G × V) :=
  SourceGroupCounting.grouped (fun g v => (g, Sum.inl v) ∉ K)

noncomputable def deletedAuxiliaryItems [Fintype G] [Fintype A]
    (K : Finset (Item G V A)) : Finset (G × A) :=
  SourceGroupCounting.grouped (fun g a => (g, Sum.inr a) ∉ K)

theorem card_deletedVertexItems [Fintype G] [Fintype V] (K : Finset (Item G V A)) :
    (deletedVertexItems K).card = ∑ g, (deletedVertices (fun i => (g, i) ∈ K)).card := by
  classical
  unfold deletedVertexItems
  rw [SourceGroupCounting.card_grouped_eq_sum_fiber]
  apply Finset.sum_congr rfl
  intro g _
  congr 1
  ext v
  simp [SourceGroupCounting.fiber, deletedVertices]

theorem card_deletedAuxiliaryItems [Fintype G] [Fintype A] (K : Finset (Item G V A)) :
    (deletedAuxiliaryItems K).card = ∑ g, (deletedAuxiliaries (fun i => (g, i) ∈ K)).card := by
  classical
  unfold deletedAuxiliaryItems
  rw [SourceGroupCounting.card_grouped_eq_sum_fiber]
  apply Finset.sum_congr rfl
  intro g _
  congr 1
  ext a
  simp [SourceGroupCounting.fiber, deletedAuxiliaries]

/-- Source tolerances stated as actual numbers of deleted labelled items.
The vertex budget is `(s/2) δ_v n`, after cancelling the positive `n` in
`δ_v = γ |E|/(2 Δ n)`. -/
theorem grouped_no_counted [Fintype G] [Fintype V] [Fintype E] [Fintype A] [Fintype B]
    (edge : E → Bool → V) (loopless : ∀ e, edge e false ≠ edge e true)
    (K : Finset (Item G V A)) (bin : Item G V A → B)
    (s Δ : ℕ) (hgroups : Fintype.card G = 4 * s) (hbins : Fintype.card B = s)
    (hcard : Fintype.card B ≤ Fintype.card A + 3)
    (hΔ : 0 < Δ) (hdegree : ∀ v, degree edge v ≤ Δ)
    (γ : ℝ) (hγ : 0 < γ) (hE : 0 < Fintype.card E)
    (gap : ∀ colour : V → Fin 3, γ * Fintype.card E ≤
      ((Finset.univ.filter (fun e => colour (edge e false) = colour (edge e true))).card : ℝ))
    (hd : ((deletedVertexItems K).card : ℝ) <
      (s : ℝ) / 2 * (γ * Fintype.card E / (2 * Δ)))
    (ha : ((deletedAuxiliaryItems K).card : ℝ) < (s : ℝ) / 2) :
    γ * s * Fintype.card E < (witnesses edge (fun i => i ∈ K) bin).card := by
  have hΔ' : (0 : ℝ) < Δ := Nat.cast_pos.mpr hΔ
  have hE' : (0 : ℝ) < Fintype.card E := Nat.cast_pos.mpr hE
  have hγ1 : γ ≤ 1 := by
    have hc := gap (fun _ => 0)
    simp at hc
    nlinarith
  apply grouped_no edge loopless K bin s Δ hgroups hbins hcard hdegree
    γ (γ * Fintype.card E / (2 * Δ)) hγ hγ1
    (div_pos (mul_pos hγ hE') (mul_pos (by norm_num) hΔ')) hE
  · have heq : (Δ : ℝ) * (γ * Fintype.card E / (2 * Δ)) = γ * Fintype.card E / 2 := by
      field_simp
    exact heq.le
  · exact gap
  · simpa only [card_deletedVertexItems, Nat.cast_sum] using hd
  · simpa only [card_deletedAuxiliaryItems, Nat.cast_sum] using ha

/-- The smallest power-of-two padded coordinate count. -/
def sourceQ0 (G E : Type*) [Fintype G] [Fintype E] : ℕ :=
  SourcePadding.powTwoCeil (Fintype.card (Coord G E))

abbrev SourceCoord (G E : Type*) [Fintype G] [Fintype E] (r : ℕ) :=
  SourcePadding.Repeated (Coord G E) (sourceQ0 G E) r

def sourceActive [Fintype G] [Fintype E] (edge : E → Bool → V) (r : ℕ) :
    SourceCoord G E r → Item G V A → Prop :=
  SourcePadding.repeatedActive (groupedActive edge) (sourceQ0 G E) r

theorem card_sourceCoord [Fintype G] [Fintype E] (r : ℕ) :
    Fintype.card (SourceCoord G E r) = sourceQ0 G E * r :=
  SourcePadding.card_repeated (SourcePadding.le_powTwoCeil _)

theorem card_sourceCoord_div [Fintype G] [Fintype E] (q₂ : ℕ)
    (hdiv : sourceQ0 G E ∣ q₂) :
    Fintype.card (SourceCoord G E (q₂ / sourceQ0 G E)) = q₂ := by
  rw [card_sourceCoord]
  exact Nat.mul_div_cancel' hdiv

/-- Optional activity with the literal padding and repetitions included. -/
noncomputable def sourceActivity [Fintype G] [Fintype E]
    (edge : E → Bool → V) {s : ℕ} (hs : 3 ≤ s) (r : ℕ)
    (i : Item G V (Fin (s - 3))) (c : SourceCoord G E r) : Option (Fin s) :=
  match c.1 with
  | .inl c => activity edge hs i c
  | .inr _ => none

theorem sourceActivity_some_iff [Fintype G] [Fintype E]
    (edge : E → Bool → V) {s : ℕ} (hs : 3 ≤ s) (r : ℕ)
    (i : Item G V (Fin (s - 3))) (c : SourceCoord G E r) :
    (∃ b, sourceActivity edge hs r i c = some b) ↔ sourceActive edge r c i := by
  obtain ⟨c, j⟩ := c
  cases c with
  | inl c => simp [sourceActivity, activity_some_iff, sourceActive,
      SourcePadding.repeatedActive, SourcePadding.paddedActive]
  | inr c => simp [sourceActivity, sourceActive,
      SourcePadding.repeatedActive, SourcePadding.paddedActive]

theorem sourceActivity_position_injective [Fintype G] [Fintype E]
    (edge : E → Bool → V) {s : ℕ} (hs : 3 ≤ s) (r : ℕ)
    (c : SourceCoord G E r) {i j : Item G V (Fin (s - 3))} {b : Fin s}
    (hi : sourceActivity edge hs r i c = some b)
    (hj : sourceActivity edge hs r j c = some b) : i = j := by
  obtain ⟨c, k⟩ := c
  cases c with
  | inl c => exact activity_position_injective edge hs c hi hj
  | inr c => simp [sourceActivity] at hi

theorem sourceActivity_yes [Fintype G] [Fintype E]
    (edge : E → Bool → V) {s : ℕ} (hs : 3 ≤ s) (r : ℕ)
    (colour : V → Fin 3) (proper : ∀ e, colour (edge e false) ≠ colour (edge e true))
    (c : SourceCoord G E r) {i j : Item G V (Fin (s - 3))} {b b' : Fin s}
    (hi : sourceActivity edge hs r i c = some b)
    (hj : sourceActivity edge hs r j c = some b')
    (hbin : yesAssignment hs colour i = yesAssignment hs colour j) : i = j := by
  obtain ⟨c, k⟩ := c
  cases c with
  | inl c => exact yesAssignment_collisionFree edge hs colour proper c hi hj hbin
  | inr c => simp [sourceActivity] at hi

theorem source_fraction [Fintype G] [Fintype E]
    (edge : E → Bool → V) (K : Finset (Item G V A)) (bin : Item G V A → B)
    (s r : ℕ) (hs : 0 < s) (hgroups : Fintype.card G = 4 * s)
    (hE : 0 < Fintype.card E) (γ : ℝ) (hγ : 0 ≤ γ)
    (hw : γ * s * Fintype.card E ≤ (witnesses edge (fun i => i ∈ K) bin).card) :
    γ / 24 * (sourceQ0 G E * r) ≤
      (SourcePadding.witnessCoords (sourceActive edge r) (fun i => i ∈ K) bin).card := by
  have hc : Fintype.card (Coord G E) = 12 * s * Fintype.card E := by
    rw [card_coord, hgroups]
    ring
  have hcp : 0 < Fintype.card (Coord G E) := by rw [hc]; positivity
  have hq : (sourceQ0 G E : ℝ) ≤ 24 * s * Fintype.card E := by
    have hn : sourceQ0 G E ≤ 24 * s * Fintype.card E := by
      have hb := (SourcePadding.powTwoCeil_lt_two_mul hcp).le
      unfold sourceQ0
      rw [hc] at hb ⊢
      calc
        _ ≤ 2 * (12 * s * Fintype.card E) := hb
        _ = 24 * s * Fintype.card E := by ring
    exact_mod_cast hn
  have hqw : γ / 24 * (sourceQ0 G E : ℝ) ≤
      (witnesses edge (fun i => i ∈ K) bin).card := by
    have hm := mul_le_mul_of_nonneg_left hq (div_nonneg hγ (by norm_num : (0 : ℝ) ≤ 24))
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hqw (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
  rw [sourceActive, SourcePadding.card_witnessCoords_repeated]
  change γ / 24 * (sourceQ0 G E * r) ≤
    ((witnesses edge (fun i => i ∈ K) bin).card * r : ℕ)
  push_cast
  nlinarith

/-- T11 on the manuscript's actual item counts, with literal least-power-of-two
inactive padding and `r` labelled copies of each coordinate. In particular,
`q₂ = sourceQ0 (Fin (4*s)) E * r` has at least `(γ/24) q₂` witnesses.
Only the graph's explicit violated-edge gap is an input hypothesis; no
collision property of the item system is assumed. -/
theorem collisions_after_deletion [Fintype V] [Fintype E]
    (edge : E → Bool → V) (loopless : ∀ e, edge e false ≠ edge e true)
    {s : ℕ} (hs : 3 ≤ s) (r Δ : ℕ) (hΔ : 0 < Δ)
    (hdegree : ∀ v, degree edge v ≤ Δ)
    (K : Finset (Item (Fin (4 * s)) V (Fin (s - 3))))
    (bin : Item (Fin (4 * s)) V (Fin (s - 3)) → Fin s)
    (γ : ℝ) (hγ : 0 < γ) (hE : 0 < Fintype.card E)
    (gap : ∀ colour : V → Fin 3, γ * Fintype.card E ≤
      ((Finset.univ.filter (fun e => colour (edge e false) = colour (edge e true))).card : ℝ))
    (hd : ((deletedVertexItems K).card : ℝ) <
      (s : ℝ) / 2 * (γ * Fintype.card E / (2 * Δ)))
    (ha : ((deletedAuxiliaryItems K).card : ℝ) < (s : ℝ) / 2) :
    γ / 24 * (sourceQ0 (Fin (4 * s)) E * r) ≤
      (SourcePadding.witnessCoords (sourceActive edge r) (fun i => i ∈ K) bin).card := by
  apply source_fraction edge K bin s r (by omega) (by simp) hE γ hγ.le
  apply (grouped_no_counted edge loopless K bin s Δ (by simp) (by simp)
    (by simp only [Fintype.card_fin]; omega) hΔ hdegree γ hγ hE gap hd ha).le

/-- The counted vertex budget is precisely the displayed `δ_v n` budget,
not a stronger deletion hypothesis. -/
theorem vertex_deletion_budget (γ : ℝ) (s m Δ n : ℕ) (hΔ : 0 < Δ) (hn : 0 < n) :
    (s : ℝ) / 2 * (γ * m / (2 * Δ * n)) * n =
      (s : ℝ) / 2 * (γ * m / (2 * Δ)) := by
  have hΔ' : (Δ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hΔ)
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  field_simp

theorem source_yes [Fintype G] [Fintype E]
    (edge : E → Bool → V) {s : ℕ} (hs : 3 ≤ s) (r : ℕ)
    (colour : V → Fin 3) (proper : ∀ e, colour (edge e false) ≠ colour (edge e true))
    (c : SourceCoord G E r) :
    Set.InjOn (yesAssignment hs colour) {i | sourceActive edge r c i} := by
  apply SourcePadding.repeated_active_injective (groupedActive edge)
    (yesAssignment hs colour) _ (sourceQ0 G E) r c
  intro c i hi j hj hij
  apply grouped_yes edge colour proper c hi hj
  exact (binEquiv hs).injective hij

/-- Extending an assignment is an analysis step only. The item system and
activity map do not use this extension or the retained set. -/
noncomputable def extendBins {I : Type*} {s : ℕ} (hs : 0 < s)
    (K : Finset I) (bin : {i // i ∈ K} → Fin s) (i : I) : Fin s := by
  classical
  exact if hi : i ∈ K then bin ⟨i, hi⟩ else ⟨0, hs⟩

theorem extendBins_eq {I : Type*} {s : ℕ} (hs : 0 < s)
    (K : Finset I) (bin : {i // i ∈ K} → Fin s) (i : {i // i ∈ K}) :
    extendBins hs K bin i.val = bin i := by
  classical
  simp [extendBins, i.property]

/-- The NO theorem for an assignment defined only on the remaining items.
Every witness uses retained items, whose extended bins equal the given bins. -/
theorem collisions_after_deletion_retained [Fintype V] [Fintype E]
    (edge : E → Bool → V) (loopless : ∀ e, edge e false ≠ edge e true)
    {s : ℕ} (hs : 3 ≤ s) (r Δ : ℕ) (hΔ : 0 < Δ)
    (hdegree : ∀ v, degree edge v ≤ Δ)
    (K : Finset (Item (Fin (4 * s)) V (Fin (s - 3))))
    (bin : {i // i ∈ K} → Fin s)
    (γ : ℝ) (hγ : 0 < γ) (hE : 0 < Fintype.card E)
    (gap : ∀ colour : V → Fin 3, γ * Fintype.card E ≤
      ((Finset.univ.filter (fun e => colour (edge e false) = colour (edge e true))).card : ℝ))
    (hd : ((deletedVertexItems K).card : ℝ) <
      (s : ℝ) / 2 * (γ * Fintype.card E / (2 * Δ)))
    (ha : ((deletedAuxiliaryItems K).card : ℝ) < (s : ℝ) / 2) :
    γ / 24 * (sourceQ0 (Fin (4 * s)) E * r) ≤
      (SourcePadding.witnessCoords (sourceActive edge r) (fun i => i ∈ K)
        (extendBins (by omega : 0 < s) K bin)).card := by
  exact collisions_after_deletion edge loopless hs r Δ hΔ hdegree K
    (extendBins (by omega) K bin) γ hγ hE gap hd ha

end Paper2.SourceItems
