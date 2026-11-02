import Mathlib
import Paper2.SourceItems
import EthInapproximability.CurrentPaper.EncodedGraph

/-!
Finite graph-copy padding for selected v37, `sampling.tex:202-220`.
The mathematical vertex and edge occurrence labels carry their copy number.
This file does not claim a fixed-machine implementation of graph printing.
-/

namespace Paper2.CurrentAdditive.GraphCopyPadding

open EthInapproximability.CurrentPaper

variable {V E : Type*}

abbrev Vertices (c : ℕ) (V : Type*) := Fin c × V
abbrev Edges (c : ℕ) (E : Type*) := Fin c × E

def copyEdge (c : ℕ) (edge : E → Bool → V) :
    Edges c E → Bool → Vertices c V :=
  fun e b => (e.1, edge e.2 b)

theorem copyEdge_loopless (c : ℕ) (edge : E → Bool → V)
    (h : ∀ e, edge e false ≠ edge e true) :
    ∀ e, copyEdge c edge e false ≠ copyEdge c edge e true := by
  intro ⟨j, e⟩ he
  exact h e (congrArg Prod.snd he)

theorem colourable_iff [Nonempty (Fin c)] (edge : E → Bool → V) :
    (∃ colour : V → Fin 3, ∀ e, colour (edge e false) ≠ colour (edge e true)) ↔
    (∃ colour : Vertices c V → Fin 3,
      ∀ e, colour (copyEdge c edge e false) ≠ colour (copyEdge c edge e true)) := by
  constructor
  · rintro ⟨colour, hc⟩
    exact ⟨fun x => colour x.2, fun e => hc e.2⟩
  · rintro ⟨colour, hc⟩
    let j : Fin c := Classical.choice inferInstance
    exact ⟨fun v => colour (j, v), fun e => hc (j, e)⟩

def monochromatic [Fintype E] [DecidableEq (Fin 3)] (edge : E → Bool → V)
    (colour : V → Fin 3) : Finset E := by
  classical
  exact Finset.univ.filter (fun e => colour (edge e false) = colour (edge e true))

theorem monochromatic_copy [Fintype E] [DecidableEq (Fin 3)]
    (c : ℕ) (edge : E → Bool → V) (colour : Vertices c V → Fin 3) :
    (Finset.univ.filter (fun e : Edges c E =>
      colour (copyEdge c edge e false) = colour (copyEdge c edge e true))).card =
      ∑ j : Fin c, (monochromatic edge (fun v => colour (j, v))).card := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [monochromatic, Finset.sum_filter]
  rfl

theorem monochromatic_gap [Fintype E] [DecidableEq (Fin 3)]
    (c : ℕ) (edge : E → Bool → V) (γ : ℚ)
    (hgap : ∀ colour : V → Fin 3,
      γ * (Fintype.card E : ℚ) ≤ (monochromatic edge colour).card) :
    ∀ colour : Vertices c V → Fin 3,
      γ * (Fintype.card (Edges c E) : ℚ) ≤
        ((Finset.univ.filter (fun e : Edges c E =>
          colour (copyEdge c edge e false) = colour (copyEdge c edge e true))).card : ℚ) := by
  intro colour
  rw [monochromatic_copy]
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_sum]
  calc
    γ * ((c : ℚ) * Fintype.card E) =
        ∑ _j : Fin c, γ * (Fintype.card E : ℚ) := by simp; ring
    _ ≤ ∑ j : Fin c, ((monochromatic edge (fun v => colour (j, v))).card : ℚ) :=
      Finset.sum_le_sum (fun j _ => hgap _)

theorem no_isolates [Fintype E] [Nonempty (Fin c)]
    (edge : E → Bool → V)
    (h : ∀ v : V, ∃ e b, edge e b = v) :
    ∀ v : Vertices c V, ∃ e b, copyEdge c edge e b = v := by
  rintro ⟨j, v⟩
  obtain ⟨e, b, he⟩ := h v
  exact ⟨(j, e), b, by simp [copyEdge, he]⟩

theorem degree_copy [Fintype E] (c : ℕ) (edge : E → Bool → V)
    (j : Fin c) (v : V) :
    SourceItems.degree (copyEdge c edge) (j, v) = SourceItems.degree edge v := by
  classical
  simp only [SourceItems.degree, Finset.card_eq_sum_ones,
    Finset.sum_filter, Fintype.sum_prod_type]
  have hcalc :
      (∑ x : Fin c, ∑ x_1 : E, ∑ x_2 : Bool,
      if (x, edge x_1 x_2) = (j, v) then 1 else 0) =
      ∑ x_1 : E, ∑ x_2 : Bool,
        if edge x_1 x_2 = v then 1 else 0 := by
    calc
      (∑ x : Fin c, ∑ x_1 : E, ∑ x_2 : Bool,
        if (x, edge x_1 x_2) = (j, v) then 1 else 0) =
      ∑ x : Fin c, if x = j then
        ∑ x_1 : E, ∑ x_2 : Bool, if edge x_1 x_2 = v then 1 else 0
        else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hx : x = j <;> simp [hx]
      _ = ∑ x_1 : E, ∑ x_2 : Bool,
        if edge x_1 x_2 = v then 1 else 0 := by simp
  simpa [copyEdge] using hcalc

theorem degree_bound [Fintype E] (c : ℕ) (edge : E → Bool → V)
    (Δ : ℕ) (h : ∀ v, SourceItems.degree edge v ≤ Δ) :
    ∀ v, SourceItems.degree (copyEdge c edge) v ≤ Δ := by
  rintro ⟨j, v⟩
  rw [degree_copy]
  exact h v

theorem copy_card_vertices [Fintype V] (c : ℕ) :
    Fintype.card (Vertices c V) = c * Fintype.card V := by simp [Vertices]

theorem copy_card_edges [Fintype E] (c : ℕ) :
    Fintype.card (Edges c E) = c * Fintype.card E := by simp [Edges]

theorem edge_vertex_ratio [Fintype V] [Fintype E]
    (c : ℕ) (hc : 0 < c) (hn : 0 < Fintype.card V) :
    (Fintype.card (Edges c E) : ℚ) / Fintype.card (Vertices c V) =
      (Fintype.card E : ℚ) / Fintype.card V := by
  rw [copy_card_edges, copy_card_vertices]
  push_cast
  field_simp

def copies (nStar nIn : ℕ) : ℕ := max 1 ((nStar + nIn - 1) / nIn)

theorem copies_pos (nStar nIn : ℕ) : 0 < copies nStar nIn := by
  simp [copies]

theorem copies_bounds (nStar nIn : ℕ) (hStar : 2 ≤ nStar) (hIn : 0 < nIn) :
    nIn ≤ copies nStar nIn * nIn ∧
    nStar ≤ copies nStar nIn * nIn ∧
    copies nStar nIn * nIn < nIn + nStar := by
  let a := nStar + nIn - 1
  let q := a / nIn
  have hq : 1 ≤ q := (Nat.le_div_iff_mul_le hIn).2 (by dsimp [a]; omega)
  have hc : copies nStar nIn = q := by
    simp [copies, q, a, max_eq_right hq]
  have hmod := Nat.mod_lt a hIn
  have hdiv : a = q * nIn + a % nIn := by
    simpa only [q, Nat.mul_comm] using (Nat.div_add_mod a nIn).symm
  have hqmul : nIn ≤ q * nIn := by
    simpa using Nat.mul_le_mul_right nIn hq
  have hlow : nStar ≤ q * nIn := by
    dsimp [a] at hdiv hmod
    omega
  have hupp : q * nIn < nIn + nStar := by
    dsimp [a] at hdiv
    omega
  rw [hc]
  exact ⟨hqmul, hlow, hupp⟩

/-- A concrete finite encoded graph: copy `j` shifts every endpoint by `j*n`.
The edge list retains occurrence order and parallel edges. -/
def encodedCopies (g : EncodedGraph.Graph) (c : ℕ) : EncodedGraph.Graph :=
  { vertices := c * g.vertices
    edges := (List.range c).flatMap fun j =>
      g.edges.map fun p => (j * g.vertices + p.1, j * g.vertices + p.2) }

theorem encodedCopies_valid (g : EncodedGraph.Graph) (hg : g.Valid)
    (c : ℕ) : (encodedCopies g c).Valid := by
  intro p hp
  change p ∈ (List.range c).flatMap (fun j =>
    g.edges.map fun q => (j * g.vertices + q.1, j * g.vertices + q.2)) at hp
  obtain ⟨j, hj, hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  have hjc : j < c := List.mem_range.mp hj
  obtain ⟨hu, hv, hne⟩ := hg q hq
  change j * g.vertices + q.1 < c * g.vertices ∧
    j * g.vertices + q.2 < c * g.vertices ∧
    j * g.vertices + q.1 ≠ j * g.vertices + q.2
  have hmul := Nat.mul_le_mul_right g.vertices (Nat.succ_le_iff.mpr hjc)
  constructor
  · nlinarith
  constructor
  · nlinarith
  · omega

theorem encodedCopies_edges_length (g : EncodedGraph.Graph) (c : ℕ) :
    (encodedCopies g c).edges.length = c * g.edges.length := by
  simp [encodedCopies, List.length_flatMap, List.length_map]

theorem encodedCopies_vertices (g : EncodedGraph.Graph) (c : ℕ) :
    (encodedCopies g c).vertices = c * g.vertices := rfl

theorem encodedCopies_edge_mem (g : EncodedGraph.Graph) (c : ℕ) (p : ℕ × ℕ) :
    p ∈ (encodedCopies g c).edges ↔
      ∃ j < c, ∃ q ∈ g.edges,
        p = (j * g.vertices + q.1, j * g.vertices + q.2) := by
  simp only [encodedCopies, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j, hj, q, hq, hp⟩
    exact ⟨j, hj, q, hq, hp.symm⟩
  · rintro ⟨j, hj, q, hq, hp⟩
    exact ⟨j, hj, q, hq, hp.symm⟩

def monoCountNat (g : EncodedGraph.Graph) (colour : ℕ → Fin 3) : ℕ :=
  (g.edges.filter fun p => colour p.1 = colour p.2).length

theorem monoCount_encodedCopies (g : EncodedGraph.Graph) (c : ℕ)
    (colour : ℕ → Fin 3) :
    monoCountNat (encodedCopies g c) colour =
      ((List.range c).map fun j =>
        monoCountNat g (fun v => colour (j * g.vertices + v))).sum := by
  simp [monoCountNat, encodedCopies, List.filter_flatMap, List.filter_map,
    List.length_flatMap, Function.comp_def]

private theorem sum_range_gap (c : ℕ) (a : ℚ) (f : ℕ → ℕ)
    (h : ∀ j < c, a ≤ (f j : ℚ)) :
    (c : ℚ) * a ≤ (((List.range c).map f).sum : ℚ) := by
  induction c with
  | zero => simp
  | succ c ih =>
    have hc := ih (fun j hj => h j (by omega))
    have hj := h c (by omega)
    rw [List.sum_range_succ]
    simp only [Nat.cast_add, Nat.cast_succ]
    nlinarith

theorem encodedCopies_gap (g : EncodedGraph.Graph) (c : ℕ) (γ : ℚ)
    (hgap : ∀ colour : ℕ → Fin 3,
      γ * (g.edges.length : ℚ) ≤ monoCountNat g colour) :
    ∀ colour : ℕ → Fin 3,
      γ * ((encodedCopies g c).edges.length : ℚ) ≤
        monoCountNat (encodedCopies g c) colour := by
  intro colour
  rw [monoCount_encodedCopies, encodedCopies_edges_length]
  have h := sum_range_gap c (γ * (g.edges.length : ℚ))
    (fun j => monoCountNat g (fun v => colour (j * g.vertices + v)))
    (fun j hj => hgap _)
  calc
    γ * ((c * g.edges.length : ℕ) : ℚ) =
        (c : ℚ) * (γ * (g.edges.length : ℚ)) := by push_cast; ring
    _ ≤ (((List.range c).map fun j =>
        monoCountNat g (fun v => colour (j * g.vertices + v))).sum : ℚ) := h

#print axioms copyEdge_loopless
#print axioms colourable_iff
#print axioms monochromatic_gap
#print axioms no_isolates
#print axioms degree_copy
#print axioms degree_bound
#print axioms edge_vertex_ratio
#print axioms copies_bounds
#print axioms encodedCopies_valid
#print axioms encodedCopies_edges_length
#print axioms encodedCopies_edge_mem
#print axioms monoCount_encodedCopies
#print axioms encodedCopies_gap

end Paper2.CurrentAdditive.GraphCopyPadding
