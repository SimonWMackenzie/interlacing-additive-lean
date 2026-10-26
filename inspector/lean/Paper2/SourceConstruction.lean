import Paper2.SourceItems
import Paper2.SourceProtocols
import Paper2.SourceRank

/-!
# Connecting the graph items to the source matrix

Frozen Paper 2 v12, Section 4 and the rank/upper-bound part of the amplifier
proof. The graph, public coordinate width and base matrix determine the
matrix. A proper colouring is introduced only in the proof of its cheaper
protocol, never in the constructor. Uniform padding and replication are the
actual `SourceItems` construction. Finite carrier equivalences here are
proof-level relabellings, not a machine-time materialization claim.
-/

namespace Paper2.SourceConstruction

open Workspace.Types.CommComplexity RankLeaves

variable {V E X Y : Type*} [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] {s q₁ q₂ : ℕ} [NeZero s]

abbrev Items (s : ℕ) (V : Type*) := SourceItems.Item (Fin (4 * s)) V (Fin (s - 3))

theorem card_items (hs : 3 ≤ s) :
    Fintype.card (Items s V) = 4 * s * (Fintype.card V + s - 3) := by
  simp only [Items, SourceItems.Item, SourceItems.LocalItem, Fintype.card_prod,
    Fintype.card_sum, Fintype.card_fin]
  congr 1
  omega

noncomputable def coordinateEquiv (r : ℕ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) E * r) :
    Fin q₂ ≃ SourceItems.SourceCoord (Fin (4 * s)) E r :=
  Fintype.equivOfCardEq (by rw [Fintype.card_fin, SourceItems.card_sourceCoord, hq])

/-- Active labels in a single fixed public ordering of all items. -/
noncomputable def activeLabels (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (r : ℕ)
    (c : SourceItems.SourceCoord (Fin (4 * s)) E r) :
    Finset (Fin (Fintype.card (Items s V))) := by
  classical
  exact Finset.univ.filter (fun j => SourceItems.sourceActive edge r c (order.symm j))

theorem activeLabels_card_le (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ)
    (c : SourceItems.SourceCoord (Fin (4 * s)) E r) :
    (activeLabels order edge r c).card ≤ s := by
  classical
  let A := activeLabels order edge r c
  have hex (j : A) : ∃ b, SourceItems.sourceActivity edge hs r (order.symm j) c = some b := by
    apply (SourceItems.sourceActivity_some_iff edge hs r _ c).mpr
    exact (Finset.mem_filter.mp j.property).2
  let f : A → Fin s := fun j => Classical.choose (hex j)
  have hf : Function.Injective f := by
    intro i j hij
    have hi := Classical.choose_spec (hex i)
    have hj := Classical.choose_spec (hex j)
    change SourceItems.sourceActivity edge hs r (order.symm i) c = some (f i) at hi
    change SourceItems.sourceActivity edge hs r (order.symm j) c = some (f j) at hj
    rw [← hij] at hj
    have he := SourceItems.sourceActivity_position_injective edge hs r c hi hj
    exact Subtype.ext (order.symm.injective he)
  have h := Fintype.card_le_of_injective f hf
  simpa [A] using h

/-- Dense ordinal position of each active item in the fixed public item
order. This matches the manuscript's ordered injection, rather than using
the endpoint/auxiliary slots used to prove the cardinality bound. -/
noncomputable def orderedActivity
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ)
    (i : Items s V) (c : SourceItems.SourceCoord (Fin (4 * s)) E r) : Option (Fin s) := by
  classical
  let A := activeLabels order edge r c
  exact if hi : order i ∈ A then
    some (Fin.castLE (activeLabels_card_le order edge hs r c)
      ((A.orderIsoOfFin rfl).symm ⟨order i, hi⟩))
  else none

theorem orderedActivity_some_iff
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ)
    (i : Items s V) (c : SourceItems.SourceCoord (Fin (4 * s)) E r) :
    (∃ b, orderedActivity order edge hs r i c = some b) ↔
      SourceItems.sourceActive edge r c i := by
  classical
  simp [orderedActivity, activeLabels]

theorem orderedActivity_injective
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ)
    (c : SourceItems.SourceCoord (Fin (4 * s)) E r) (i j : Items s V) (b : Fin s)
    (hi : orderedActivity order edge hs r i c = some b)
    (hj : orderedActivity order edge hs r j c = some b) : i = j := by
  classical
  have hai : order i ∈ activeLabels order edge r c := by
    simpa [activeLabels] using (orderedActivity_some_iff order edge hs r i c).mp ⟨b, hi⟩
  have haj : order j ∈ activeLabels order edge r c := by
    simpa [activeLabels] using (orderedActivity_some_iff order edge hs r j c).mp ⟨b, hj⟩
  unfold orderedActivity at hi hj
  dsimp only at hi hj
  rw [dif_pos hai] at hi
  rw [dif_pos haj] at hj
  have he := Option.some.inj (hi.trans hj.symm)
  have hf : ((activeLabels order edge r c).orderIsoOfFin rfl).symm ⟨order i, hai⟩ =
      ((activeLabels order edge r c).orderIsoOfFin rfl).symm ⟨order j, haj⟩ :=
    Fin.ext (congrArg (fun x : Fin s => x.val) he)
  have hsub := (Finset.orderIsoOfFin (activeLabels order edge r c) rfl).symm.injective hf
  exact order.injective (congrArg Subtype.val hsub)

noncomputable def activity
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) E * r) :
    Items s V → Fin q₂ → Option (Fin s) :=
  fun i α => orderedActivity order edge hs r i (coordinateEquiv r hq α)

theorem activity_collisionFree
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) E * r)
    (colour : V → Fin 3) (proper : ∀ e, colour (edge e false) ≠ colour (edge e true)) :
    SourceMatrix.CollisionFree (SourceItems.yesAssignment hs colour)
      (activity order edge hs r hq) := by
  intro α i j b b' hi hj heq
  have hai := (orderedActivity_some_iff order edge hs r i _).mp ⟨b, hi⟩
  have haj := (orderedActivity_some_iff order edge hs r j _).mp ⟨b', hj⟩
  obtain ⟨ci, hci⟩ := (SourceItems.sourceActivity_some_iff edge hs r i _).mpr hai
  obtain ⟨cj, hcj⟩ := (SourceItems.sourceActivity_some_iff edge hs r j _).mpr haj
  exact SourceItems.sourceActivity_yes edge hs r colour proper _ hci hcj heq

/-- The public source table: no colouring, retained set or promise appears
among its construction inputs. -/
noncomputable def matrix
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) E * r)
    (R : X → Y → Bool) (ξ₀ : SourceMatrix.Tail s Y) :=
  SourceMatrix.N (q₁ := q₁) R (activity order edge hs r hq) ξ₀

theorem actual_item_rank_guard (hs : 3 ≤ s)
    (hq : 2 * (Fintype.card V + s - 3) ≤ q₂) :
    Fintype.card (Items s V) ≤ 2 * s * q₂ := by
  rw [card_items hs]
  nlinarith

/-- No isolated vertices give the incidence-size bound used in the source
rank calculation, counting parallel edge occurrences separately. -/
theorem vertices_le_twice_edges (edge : E → Bool → V)
    (hincident : ∀ v, ∃ e b, edge e b = v) :
    Fintype.card V ≤ 2 * Fintype.card E := by
  have hs : Function.Surjective (fun eb : E × Bool => edge eb.1 eb.2) := by
    intro v
    obtain ⟨e, b, h⟩ := hincident v
    exact ⟨(e, b), h⟩
  simpa [Fintype.card_prod, Nat.mul_comm] using Fintype.card_le_of_surjective _ hs

/-- The actual padded width already supplies the item-count rank guard
whenever at least one copy of each padded coordinate is retained. -/
theorem padded_item_rank_guard (edge : E → Bool → V)
    (hs : 3 ≤ s) (r : ℕ) (hr : 1 ≤ r)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) E * r)
    (hE : 0 < Fintype.card E) (hincident : ∀ v, ∃ e b, edge e b = v) :
    Fintype.card (Items s V) ≤ 2 * s * q₂ := by
  have hn := vertices_le_twice_edges edge hincident
  have hq₀ : 12 * s * Fintype.card E ≤ SourceItems.sourceQ0 (Fin (4 * s)) E := by
    have h := SourcePadding.le_powTwoCeil (Fintype.card (SourceItems.Coord (Fin (4 * s)) E))
    have hc : Fintype.card (SourceItems.Coord (Fin (4 * s)) E) =
        12 * s * Fintype.card E := by
      rw [SourceItems.card_coord, Fintype.card_fin]
      ring
    simpa only [SourceItems.sourceQ0, hc] using h
  have hq₀q : SourceItems.sourceQ0 (Fin (4 * s)) E ≤ q₂ := by
    rw [hq]
    exact Nat.le_mul_of_pos_right _ (by omega)
  apply actual_item_rank_guard hs
  have ht : Fintype.card V + s - 3 ≤ Fintype.card V + s := Nat.sub_le _ _
  have he : s ≤ s * Fintype.card E := Nat.le_mul_of_pos_right _ hE
  have hsE : 3 * Fintype.card E ≤ s * Fintype.card E := Nat.mul_le_mul_right _ hs
  nlinarith

variable [NeZero q₂]

/-- Both source upper budgets for the same graph-constructed table, with
the YES saving derived from a proper colouring. -/
theorem matrix_upper_budgets
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) E * r)
    (R : X → Y → Bool) (ξ₀ : SourceMatrix.Tail s Y) (a b : ℕ)
    (hq₁ : q₁ + 2 = s) (hsa : s = 2 ^ a) (hqb : q₂ = 2 ^ b) :
    D (matrix (q₁ := q₁) order edge hs r hq R ξ₀) ≤ D R + a + b + a + 1 ∧
      (∀ colour : V → Fin 3, (∀ e, colour (edge e false) ≠ colour (edge e true)) →
        D (matrix (q₁ := q₁) order edge hs r hq R ξ₀) ≤ D R + a + b + a) := by
  obtain ⟨hu, hy⟩ := SourceMatrix.source_upper_budgets
    (activity order edge hs r hq) R ξ₀ a b hq₁ hsa hqb
  refine ⟨hu, fun colour proper => ?_⟩
  exact hy (SourceItems.yesAssignment hs colour)
    (activity_collisionFree order edge hs r hq colour proper)

/-- The same upper bounds hold for every labelled restriction, including
repeated labels. This is a pullback of the identical constructed table. -/
theorem matrix_restriction_budgets {A B : Type*} [Fintype A] [Fintype B]
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) E * r)
    (R : X → Y → Bool) (ξ₀ : SourceMatrix.Tail s Y) (a b y : ℕ)
    (hq₁ : q₁ + 2 = s) (hsa : s = 2 ^ a) (hqb : q₂ = 2 ^ b) (hy : D R ≤ y)
    (rows : A → SourceMatrix.TaggedColumn q₁ q₂ s Y)
    (cols : B → SourceMatrix.RawRow q₁ q₂ s X (Items s V)) :
    D (fun x y' => matrix order edge hs r hq R ξ₀ (rows x) (cols y')) ≤ y + a + b + a + 1 ∧
      (∀ colour : V → Fin 3, (∀ e, colour (edge e false) ≠ colour (edge e true)) →
        D (fun x y' => matrix order edge hs r hq R ξ₀ (rows x) (cols y')) ≤ y + a + b + a) := by
  have hm := Workspace.ProofLemmas.SublemmaPrecompNoIncrease
    (matrix order edge hs r hq R ξ₀) rows cols
  obtain ⟨hu, hyes⟩ := matrix_upper_budgets order edge hs r hq R ξ₀ a b hq₁ hsa hqb
  refine ⟨by omega, ?_⟩
  intro colour proper
  have := hyes colour proper
  omega

theorem actual_successor_rank_bound
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ) (hr : 1 ≤ r)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) E * r)
    (hE : 0 < Fintype.card E) (hincident : ∀ v, ∃ e b, edge e b = v)
    (R : X → Y → Bool) (ξ₀ : SourceMatrix.Tail s Y) (w Q a b c d : ℕ)
    (hq₁ : q₁ + 2 = s) (hsa : s = 2 ^ a) (hqb : q₂ = 2 ^ b)
    (hw : w = 2 ^ c) (hQ : Q = 2 ^ d) :
    (realMatrix (SourceMatrix.successor (q₁ := q₁) R
      (activity order edge hs r hq) ξ₀ w Q)).rank ≤
        2 ^ (a + a + b + c + d) * (realMatrix R).rank :=
  SourceMatrix.successor_rank_le_pow R (activity order edge hs r hq) ξ₀ w Q a b c d
    (padded_item_rank_guard edge hs r hr hq hE hincident) hq₁ hsa hqb hw hQ

end Paper2.SourceConstruction
