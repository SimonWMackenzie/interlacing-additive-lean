import Mathlib

/-!
# Removing repeated vertex occurrences from hyperedges

Frozen v12 Appendix B, `yao:clones`. Every original vertex has K*S
labelled clones. The new edge carrier consists of ALL injective lifts of
each original ordered edge, not a promise-dependent choice. Majority colours
are chosen only in the soundness proof. This module proves the finite
construction, colour transfer and exact size bounds, not the external
Guruswami--Lee hardness theorem or a machine-runtime bound.
-/

namespace Paper2.HypergraphClones

variable {V E : Type*} {K S : ℕ}

/-- Duplicate labels remain genuine separate vertices. -/
abbrev Vertex (V : Type*) (K S : ℕ) := V × Fin (K * S)

/-- All choices of clone labels making this ordered edge injective. -/
abbrev Lift (edge : Fin K → V) (S : ℕ) :=
  {r : Fin K → Fin (K * S) // Function.Injective (fun i => (edge i, r i))}

/-- The incidence data is explicit and independent of all colourings. -/
def liftedEdge (edge : Fin K → V) (r : Lift edge S) : Fin K → Vertex V K S :=
  fun i => (edge i, r.val i)

theorem liftedEdge_injective (edge : Fin K → V) (r : Lift edge S) :
    Function.Injective (liftedEdge edge r) := r.property

abbrev Edge (edges : E → Fin K → V) (S : ℕ) := Σ e : E, Lift (edges e) S

def incidence (edges : E → Fin K → V) : Edge edges S → Fin K → Vertex V K S :=
  fun e => liftedEdge (edges e.1) e.2

theorem incidence_injective (edges : E → Fin K → V) (e : Edge edges S) :
    Function.Injective (incidence edges e) := e.2.property

/-- No edge disappears: distinct global occurrence indices already give
one injective lift when at least one colour is available. -/
theorem lift_nonempty (hS : 0 < S) (edge : Fin K → V) : Nonempty (Lift edge S) := by
  have hk : K ≤ K * S := by nlinarith
  let code : Fin K ↪ Fin (K * S) := Fin.castLEEmb hk
  refine ⟨⟨code, ?_⟩⟩
  intro i j hij
  exact code.injective (congrArg Prod.snd hij)

/-- A literal finite enumerator for one edge's lifts. Its input is only the
original edge, never a colouring or promise witness. -/
def enumerateLifts [DecidableEq V] (edge : Fin K → V) (S : ℕ) :
    Finset (Fin K → Fin (K * S)) :=
  Finset.univ.filter (fun r => Function.Injective (fun i => (edge i, r i)))

theorem mem_enumerateLifts [DecidableEq V] (edge : Fin K → V)
    (r : Fin K → Fin (K * S)) :
    r ∈ enumerateLifts edge S ↔ Function.Injective (fun i => (edge i, r i)) := by
  simp [enumerateLifts]

/-- Any original colouring lifts with its ENTIRE ordered colour vector
unchanged, hence preserves every bound on colour multiplicity. -/
theorem lifted_colours {C : Type*} (colour : V → C)
    (edges : E → Fin K → V) (e : Edge edges S) :
    (fun i => colour (incidence edges e i).1) = fun i => colour (edges e.1 i) := rfl

theorem colour_multiplicity [DecidableEq C] (colour : V → C)
    (edges : E → Fin K → V) (e : Edge edges S) (c : C) :
    (Finset.univ.filter (fun i => colour (incidence edges e i).1 = c)).card =
      (Finset.univ.filter (fun i => colour (edges e.1 i) = c)).card := rfl

/-- Pigeonhole gives at least K clones of one colour, with S>0. -/
theorem exists_frequent_colour (hS : 0 < S) (colour : Fin (K * S) → Fin S) :
    ∃ c : Fin S, K ≤ Fintype.card {r : Fin (K * S) // colour r = c} := by
  classical
  letI : Nonempty (Fin S) := ⟨⟨0, hS⟩⟩
  obtain ⟨c, hc⟩ := Fintype.exists_le_card_fiber_of_mul_le_card colour
    (n := K) (by simp [Nat.mul_comm])
  exact ⟨c, by simpa only [Fintype.card_subtype] using hc⟩

/-- For each vertex, K differently labelled clones of its selected colour.
The injection uses occurrence positions, so even K repetitions of one
vertex can be lifted to distinct vertices. -/
theorem exists_colour_embeddings (hS : 0 < S) (colour : Vertex V K S → Fin S) :
    ∃ c : V → Fin S, ∃ pick : V → (Fin K ↪ Fin (K * S)),
      ∀ v i, colour (v, pick v i) = c v := by
  classical
  have h (v : V) := exists_frequent_colour (K := K) hS (fun r => colour (v, r))
  choose c hc using h
  have hp (v : V) : Nonempty (Fin K ↪ {r : Fin (K * S) // colour (v, r) = c v}) := by
    apply Function.Embedding.nonempty_of_card_le
    simpa using hc v
  let emb (v : V) := Classical.choice (hp v)
  refine ⟨c, fun v => (emb v).trans (Function.Embedding.subtype _), ?_⟩
  intro v i
  exact (emb v i).property

/-- A monochromatic original occurrence edge has a genuinely injective
monochromatic lift under the selected majority colouring. -/
theorem monochromatic_lift (edge : Fin K → V)
    (colour : Vertex V K S → Fin S) (c : V → Fin S)
    (pick : V → (Fin K ↪ Fin (K * S)))
    (hpick : ∀ v i, colour (v, pick v i) = c v)
    (b : Fin S) (hedge : ∀ i, c (edge i) = b) :
    ∃ r : Lift edge S, ∀ i, colour (liftedEdge edge r i) = b := by
  let r : Fin K → Fin (K * S) := fun i => pick (edge i) i
  have hr : Function.Injective (fun i => (edge i, r i)) := by
    intro i j hij
    have hv : edge i = edge j := congrArg Prod.fst hij
    have hc : pick (edge i) i = pick (edge j) j := congrArg Prod.snd hij
    rw [← hv] at hc
    exact (pick (edge i)).injective hc
  refine ⟨⟨r, hr⟩, ?_⟩
  intro i
  exact (hpick (edge i) i).trans (hedge i)

def HasMonochromaticEdge {C : Type*} (edges : E → Fin K → V) (colour : V → C) : Prop :=
  ∃ e : E, ∃ c : C, ∀ i, colour (edges e i) = c

/-- Soundness for the actual hypergraph containing all distinct lifts. -/
theorem no_proper_colouring_preserved (hS : 0 < S)
    (edges : E → Fin K → V)
    (hno : ∀ colour : V → Fin S, HasMonochromaticEdge edges colour) :
    ∀ colour : Vertex V K S → Fin S,
      HasMonochromaticEdge (incidence (S := S) edges) colour := by
  intro colour
  obtain ⟨c, pick, hpick⟩ := exists_colour_embeddings hS colour
  obtain ⟨e, b, he⟩ := hno c
  obtain ⟨r, hr⟩ := monochromatic_lift (edges e) colour c pick hpick b he
  exact ⟨⟨e, r⟩, b, hr⟩

theorem card_vertices [Fintype V] : Fintype.card (Vertex V K S) =
    Fintype.card V * (K * S) := by simp [Vertex]

theorem card_lifts_le (edge : Fin K → V) :
    Nat.card (Lift edge S) ≤ (K * S) ^ K := by
  classical
  rw [Nat.card_eq_fintype_card]
  calc
    _ ≤ Fintype.card (Fin K → Fin (K * S)) :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    _ = _ := by simp

theorem card_edges_le [Fintype E] (edges : E → Fin K → V) :
    Nat.card (Edge edges S) ≤ Fintype.card E * (K * S) ^ K := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  calc
    _ ≤ ∑ _e : E, (K * S) ^ K := Finset.sum_le_sum (fun e _ => by
      simpa only [Nat.card_eq_fintype_card] using card_lifts_le (S := S) (edges e))
    _ = _ := by simp

end Paper2.HypergraphClones
