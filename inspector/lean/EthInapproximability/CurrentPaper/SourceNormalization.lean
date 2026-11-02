import EthInapproximability.ParameterizedNP.GuardedSourceGraph
import Mathlib.Data.Sum.Order

/-!
# Removing isolated vertices and padding the graph source

Source: locked v8, `06-eth.tex`, proof of `thm:paper-sparse-gap-source`.
This is the actual finite graph transformation, including the empty-graph
case. Cited hardness theorems and bit-machine running time are not asserted.
The raw graph allows empty carriers; adjoining an edge produces the nonempty
`EndpointGraph` consumed by the communication reduction.
-/

namespace EthInapproximability.CurrentPaper.SourceNormalization

open EthInapproximability.ParameterizedNP.GuardedSourceGraph

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- An ordered loopless multigraph, before the paper removes isolated vertices.
Neither the vertex nor the edge carrier is assumed nonempty. -/
structure RawGraph (V E : Type*) [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] where
  orderV : LinearOrder V
  orderE : LinearOrder E
  bd₀ : E → V
  bd₁ : E → V
  loopless : ∀ e, bd₀ e ≠ bd₁ e

namespace RawGraph

def ofEndpointGraph (G : EndpointGraph V E) : RawGraph V E :=
  ⟨G.orderV, G.orderE, G.bd₀, G.bd₁, G.loopless⟩

def bd (G : RawGraph V E) (e : E) (b : Fin 2) : V :=
  if b = 0 then G.bd₀ e else G.bd₁ e

def degree (G : RawGraph V E) (v : V) : ℕ :=
  (Finset.univ.filter fun p : E × Fin 2 => G.bd p.1 p.2 = v).card

def Colourable (G : RawGraph V E) : Prop :=
  ∃ χ : V → Fin 3, ∀ e, χ (G.bd₀ e) ≠ χ (G.bd₁ e)

def monoFinset (G : RawGraph V E) (χ : V → Fin 3) : Finset E :=
  Finset.univ.filter fun e => χ (G.bd₀ e) = χ (G.bd₁ e)

def Gap (G : RawGraph V E) (γ : ℚ) : Prop :=
  ∀ χ : V → Fin 3, γ * (Fintype.card E : ℚ) ≤ ((G.monoFinset χ).card : ℚ)

/-- Vertex support, with its original inherited order; isolated vertices are
literally absent from this carrier. -/
abbrev Support (G : RawGraph V E) := {v : V // ∃ e : E, v = G.bd₀ e ∨ v = G.bd₁ e}

abbrev PaddedVertex (G : RawGraph V E) := G.Support ⊕ Fin 2
abbrev PaddedEdge (_G : RawGraph V E) := E ⊕ Unit

def endpoint₀ (G : RawGraph V E) (e : E) : G.Support :=
  ⟨G.bd₀ e, e, Or.inl rfl⟩

def endpoint₁ (G : RawGraph V E) (e : E) : G.Support :=
  ⟨G.bd₁ e, e, Or.inr rfl⟩

/-- Delete isolated vertices and adjoin the disjoint edge `K₂`. The original
vertices/edge occurrences precede the new ones in the ordered sum. -/
def padded (G : RawGraph V E) : EndpointGraph G.PaddedVertex G.PaddedEdge where
  orderV := by
    letI := G.orderV
    exact LinearOrder.lift' (fun p : G.PaddedVertex => (toLex p : G.Support ⊕ₗ Fin 2))
      (fun _ _ h => h)
  orderE := by
    letI := G.orderE
    exact LinearOrder.lift' (fun p : G.PaddedEdge => (toLex p : E ⊕ₗ Unit))
      (fun _ _ h => h)
  vertexNonempty := ⟨Sum.inr 0⟩
  edgeNonempty := ⟨Sum.inr ()⟩
  bd₀ := Sum.elim (fun e => Sum.inl (G.endpoint₀ e)) (fun _ => Sum.inr 0)
  bd₁ := Sum.elim (fun e => Sum.inl (G.endpoint₁ e)) (fun _ => Sum.inr 1)
  loopless := by
    rintro (e | u) h
    · exact G.loopless e (congrArg Subtype.val (Sum.inl.inj h))
    · exact (by decide : (0 : Fin 2) ≠ 1) (Sum.inr.inj h)

@[simp] theorem padded_bd_old (G : RawGraph V E) (e : E) (b : Fin 2) :
    (G.padded.bd (Sum.inl e) b) = Sum.inl
      ⟨G.bd e b, by fin_cases b <;> simp [bd]; exact ⟨e, Or.inl rfl⟩; exact ⟨e, Or.inr rfl⟩⟩ := by
  fin_cases b <;> rfl

@[simp] theorem padded_bd_new (G : RawGraph V E) (b : Fin 2) :
    G.padded.bd (Sum.inr ()) b = Sum.inr b := by
  fin_cases b <;> rfl

@[simp] theorem padded_edge_count (G : RawGraph V E) :
    Fintype.card G.PaddedEdge = Fintype.card E + 1 := by
  simp [PaddedEdge]

@[simp] theorem padded_vertex_count (G : RawGraph V E) :
    Fintype.card G.PaddedVertex = Fintype.card G.Support + 2 := by
  simp [PaddedVertex]

theorem padded_degree_old (G : RawGraph V E) (v : G.Support) :
    G.padded.degree (Sum.inl v) = G.degree v.val := by
  classical
  unfold EndpointGraph.degree degree
  symm
  apply Finset.card_bij (fun p _ => (Sum.inl p.1, p.2))
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simpa [EndpointGraph.mem_incFinset, EndpointGraph.vert, Subtype.ext_iff] using hp
  · intro p hp q hq hpq
    apply Prod.ext
    · simpa using congrArg (fun x : G.PaddedEdge × Fin 2 => x.1) hpq
    · exact congrArg (fun x : G.PaddedEdge × Fin 2 => x.2) hpq
  · rintro ⟨e | u, b⟩ hp
    · refine ⟨(e, b), ?_, rfl⟩
      simpa [EndpointGraph.mem_incFinset, EndpointGraph.vert, Subtype.ext_iff] using hp
    · cases u
      simp [EndpointGraph.mem_incFinset, EndpointGraph.vert] at hp

theorem padded_degree_new (G : RawGraph V E) (v : Fin 2) :
    G.padded.degree (Sum.inr v) = 1 := by
  classical
  have heq : G.padded.incFinset (Sum.inr v) = {((Sum.inr () : G.PaddedEdge), v)} := by
    ext ⟨e | u, b⟩
    · simp [EndpointGraph.mem_incFinset, EndpointGraph.vert]
    · cases u
      simp [EndpointGraph.mem_incFinset, EndpointGraph.vert]
  rw [EndpointGraph.degree, heq, Finset.card_singleton]

theorem support_degree_pos (G : RawGraph V E) (v : G.Support) :
    1 ≤ G.degree v.val := by
  obtain ⟨e, h | h⟩ := v.property
  · exact Finset.card_pos.mpr ⟨(e, 0), by simp [bd, h]⟩
  · exact Finset.card_pos.mpr ⟨(e, 1), by simp [bd, h]⟩

theorem padded_no_isolates (G : RawGraph V E) (v : G.PaddedVertex) :
    1 ≤ G.padded.degree v := by
  rcases v with v | v
  · rw [padded_degree_old]; exact G.support_degree_pos v
  · rw [padded_degree_new]

theorem padded_degree_bound (G : RawGraph V E) {Δ : ℕ} (hΔ : 1 ≤ Δ)
    (hdeg : ∀ v, G.degree v ≤ Δ) (v : G.PaddedVertex) :
    G.padded.degree v ≤ Δ := by
  rcases v with v | v
  · rw [padded_degree_old]; exact hdeg v.val
  · rw [padded_degree_new]; exact hΔ

theorem padded_colourable (G : RawGraph V E) (h : G.Colourable) :
    G.padded.SourceYES := by
  obtain ⟨χ, hχ⟩ := h
  refine ⟨Sum.elim (fun v => χ v.val) (fun b => ⟨b.val, by omega⟩), ?_⟩
  rintro (e | u)
  · exact hχ e
  · change (0 : Fin 3) ≠ 1
    decide

def extendColouring (G : RawGraph V E) (χ : G.Support → Fin 3) (v : V) : Fin 3 :=
  if h : ∃ e : E, v = G.bd₀ e ∨ v = G.bd₁ e then χ ⟨v, h⟩ else 0

@[simp] theorem extendColouring_support (G : RawGraph V E) (χ : G.Support → Fin 3)
    (v : G.Support) : G.extendColouring χ v.val = χ v := by
  simp [extendColouring, v.property]

@[simp] theorem extendColouring_bd₀ (G : RawGraph V E) (χ : G.Support → Fin 3)
    (e : E) : G.extendColouring χ (G.bd₀ e) = χ (G.endpoint₀ e) :=
  G.extendColouring_support χ (G.endpoint₀ e)

@[simp] theorem extendColouring_bd₁ (G : RawGraph V E) (χ : G.Support → Fin 3)
    (e : E) : G.extendColouring χ (G.bd₁ e) = χ (G.endpoint₁ e) :=
  G.extendColouring_support χ (G.endpoint₁ e)

theorem padded_colourable_iff (G : RawGraph V E) :
    G.padded.SourceYES ↔ G.Colourable := by
  constructor
  · rintro ⟨χ, hχ⟩
    refine ⟨G.extendColouring (fun v => χ (Sum.inl v)), fun e => ?_⟩
    simpa only [extendColouring_bd₀, extendColouring_bd₁] using hχ (Sum.inl e)
  · exact G.padded_colourable

theorem edge_pos_of_not_colourable (G : RawGraph V E) (h : ¬ G.Colourable) :
    0 < Fintype.card E := by
  by_contra hn
  have hempty : IsEmpty E := Fintype.card_eq_zero_iff.mp (by omega)
  exact h ⟨fun _ => 0, fun e => isEmptyElim e⟩

theorem padded_gap (G : RawGraph V E) {γ : ℚ} (hγ : 0 ≤ γ)
    (hedge : 0 < Fintype.card E) (h : G.Gap γ) : G.padded.SourceNO (γ / 2) := by
  intro χ
  let χ₀ := G.extendColouring (fun v => χ (Sum.inl v))
  have hsubset : (G.monoFinset χ₀).image (Sum.inl : E → G.PaddedEdge)
      ⊆ G.padded.monoFinset χ := by
    intro e he
    obtain ⟨e, hmono, rfl⟩ := Finset.mem_image.mp he
    have he' : χ₀ (G.bd₀ e) = χ₀ (G.bd₁ e) := (Finset.mem_filter.mp hmono).2
    rw [EndpointGraph.mem_monoFinset]
    change χ (Sum.inl (G.endpoint₀ e)) = χ (Sum.inl (G.endpoint₁ e))
    simpa only [χ₀, extendColouring_bd₀, extendColouring_bd₁] using he'
  have hc : (G.monoFinset χ₀).card ≤ (G.padded.monoFinset χ).card := by
    simpa only [Finset.card_image_of_injective _ Sum.inl_injective]
      using (Finset.card_le_card hsubset)
  have hg := h χ₀
  have hcq : ((G.monoFinset χ₀).card : ℚ) ≤ ((G.padded.monoFinset χ).card : ℚ) := by
    exact_mod_cast hc
  have heq : (1 : ℚ) ≤ (Fintype.card E : ℚ) := by exact_mod_cast hedge
  rw [padded_edge_count]
  push_cast
  nlinarith

/-- The literal copy number `max (1, ceil (n/(m₀+1)))`. -/
abbrev repetitions (_G : RawGraph V E) (n : ℕ) := copyCount n (Fintype.card E)
abbrev NormalizedVertex (G : RawGraph V E) (n : ℕ) := Fin (G.repetitions n) × G.PaddedVertex
abbrev NormalizedEdge (G : RawGraph V E) (n : ℕ) := Fin (G.repetitions n) × G.PaddedEdge

def normalize (G : RawGraph V E) (n : ℕ) :
    EndpointGraph (G.NormalizedVertex n) (G.NormalizedEdge n) :=
  G.padded.copies (G.repetitions n) (copyCount_pos n (Fintype.card E))

theorem normalized_edge_count (G : RawGraph V E) (n : ℕ) :
    Fintype.card (G.NormalizedEdge n) = G.repetitions n * (Fintype.card E + 1) := by
  simp [NormalizedEdge, Fintype.card_prod]

theorem normalized_edge_bounds (G : RawGraph V E) (n : ℕ) :
    n ≤ Fintype.card (G.NormalizedEdge n) ∧
      Fintype.card (G.NormalizedEdge n) ≤ n + Fintype.card E + 1 := by
  rw [normalized_edge_count]
  exact ⟨le_copyCount_mul _ _, copyCount_mul_le _ _⟩

theorem normalized_no_isolates (G : RawGraph V E) (n : ℕ) (v : G.NormalizedVertex n) :
    1 ≤ (G.normalize n).degree v := by
  rw [normalize, EndpointGraph.degree_copies]
  exact G.padded_no_isolates v.2

theorem normalized_degree_bound (G : RawGraph V E) (n : ℕ) {Δ : ℕ}
    (hΔ : 1 ≤ Δ) (hdeg : ∀ v, G.degree v ≤ Δ) (v : G.NormalizedVertex n) :
    (G.normalize n).degree v ≤ Δ := by
  rw [normalize, EndpointGraph.degree_copies]
  exact G.padded_degree_bound hΔ hdeg v.2

theorem normalized_vertex_bound (G : RawGraph V E) (n : ℕ) :
    Fintype.card (G.NormalizedVertex n) ≤ 2 * Fintype.card (G.NormalizedEdge n) :=
  (G.normalize n).card_vertex_le_two_mul_card_edge (G.normalized_no_isolates n)

theorem normalized_total_size (G : RawGraph V E) (n : ℕ) :
    Fintype.card (G.NormalizedVertex n) + Fintype.card (G.NormalizedEdge n)
      ≤ 3 * (n + Fintype.card E + 1) := by
  have hv := G.normalized_vertex_bound n
  have he := (G.normalized_edge_bounds n).2
  omega

theorem normalized_colourable (G : RawGraph V E) (n : ℕ) (h : G.Colourable) :
    (G.normalize n).SourceYES :=
  G.padded.sourceYES_copies _ _ (G.padded_colourable h)

theorem normalized_colourable_iff (G : RawGraph V E) (n : ℕ) :
    (G.normalize n).SourceYES ↔ G.Colourable := by
  constructor
  · rintro ⟨χ, hχ⟩
    apply G.padded_colourable_iff.mp
    let c : Fin (G.repetitions n) := ⟨0, copyCount_pos _ _⟩
    refine ⟨fun v => χ (c, v), fun e => ?_⟩
    exact hχ (c, e)
  · exact G.normalized_colourable n

theorem normalized_gap (G : RawGraph V E) (n : ℕ) {γ : ℚ} (hγ : 0 ≤ γ)
    (hnot : ¬ G.Colourable) (hgap : G.Gap γ) :
    (G.normalize n).SourceNO (γ / 2) :=
  G.padded.sourceNO_copies _ _ (G.padded_gap hγ (G.edge_pos_of_not_colourable hnot) hgap)

/-- The two endpoint-graph predicates are exactly the corresponding raw
predicates, not hypotheses added by normalization. -/
theorem ofEndpointGraph_colourable (G : EndpointGraph V E) :
    (ofEndpointGraph G).Colourable ↔ G.SourceYES := Iff.rfl

theorem ofEndpointGraph_gap (G : EndpointGraph V E) (γ : ℚ) :
    (ofEndpointGraph G).Gap γ ↔ G.SourceNO γ := Iff.rfl

theorem ofEndpointGraph_degree (G : EndpointGraph V E) (v : V) :
    (ofEndpointGraph G).degree v = G.degree v := rfl

/-- The paper may choose any smaller positive rational gap after padding. -/
theorem normalized_gap_mono (G : RawGraph V E) (n : ℕ) {γ γ' : ℚ}
    (hγ : 0 ≤ γ) (hnot : ¬ G.Colourable) (hgap : G.Gap γ) (hle : γ' ≤ γ / 2) :
    (G.normalize n).SourceNO γ' := (G.normalized_gap n hγ hnot hgap).mono hle

/-! ## Boundary and nonvacuity regressions -/

def emptyGraph : RawGraph (Fin 0) (Fin 0) where
  orderV := inferInstance
  orderE := inferInstance
  bd₀ := Fin.elim0
  bd₁ := Fin.elim0
  loopless := fun e => Fin.elim0 e

theorem emptyGraph_colourable : emptyGraph.Colourable :=
  ⟨Fin.elim0, fun e => Fin.elim0 e⟩

theorem empty_normalization_colourable (n : ℕ) :
    (emptyGraph.normalize n).SourceYES :=
  emptyGraph.normalized_colourable n emptyGraph_colourable

theorem empty_normalization_edge_count (n : ℕ) :
    Fintype.card (emptyGraph.NormalizedEdge n) = max 1 n := by
  simp [repetitions, copyCount]

/-- K4 with one extra isolated vertex: the source does not accidentally retain
that vertex when the support subtype is constructed. -/
def k4WithIsolate : RawGraph (Fin 5) (Fin 6) where
  orderV := inferInstance
  orderE := inferInstance
  bd₀ := ![0, 0, 0, 1, 1, 2]
  bd₁ := ![1, 2, 3, 2, 3, 3]
  loopless := by decide

theorem k4WithIsolate_support_card : Fintype.card k4WithIsolate.Support = 4 := by decide

theorem k4WithIsolate_isolated_degree : k4WithIsolate.degree 4 = 0 := by decide

theorem k4WithIsolate_gap : k4WithIsolate.Gap (1 / 6) := by
  intro χ
  let χ₄ : Fin 4 → Fin 3 := fun v => χ v.castSucc
  have h := k4_sourceNO χ₄
  have heq : k4WithIsolate.monoFinset χ = K4.monoFinset χ₄ := by
    ext e
    fin_cases e <;> rfl
  simpa only [heq] using h

theorem k4WithIsolate_not_colourable : ¬ k4WithIsolate.Colourable := by
  rintro ⟨χ, hχ⟩
  apply k4_not_sourceYES
  refine ⟨fun v => χ v.castSucc, fun e => ?_⟩
  have h := hχ e
  fin_cases e <;> exact h

theorem k4_normalization_gap (n : ℕ) :
    (k4WithIsolate.normalize n).SourceNO (1 / 12) := by
  convert k4WithIsolate.normalized_gap n (by norm_num : (0 : ℚ) ≤ 1 / 6)
    k4WithIsolate_not_colourable k4WithIsolate_gap using 1
  norm_num

end RawGraph

/-! ## Public ordered endpoint encoding

This is an ordered list of bounded natural endpoint labels, not yet a binary
string parser or a claimed bit-machine time bound. -/

def vertexEnumeration (G : EndpointGraph V E) : Fin (Fintype.card V) ≃ V := by
  letI := G.orderV
  exact (Fintype.orderIsoFinOfCardEq V rfl).toEquiv

def edgeEnumeration (G : EndpointGraph V E) : Fin (Fintype.card E) ≃ E := by
  letI := G.orderE
  exact (Fintype.orderIsoFinOfCardEq E rfl).toEquiv

def endpointPair (G : EndpointGraph V E) (i : Fin (Fintype.card E)) :
    Fin (Fintype.card V) × Fin (Fintype.card V) :=
  ((vertexEnumeration G).symm (G.bd₀ (edgeEnumeration G i)),
   (vertexEnumeration G).symm (G.bd₁ (edgeEnumeration G i)))

def endpointList (G : EndpointGraph V E) : List (ℕ × ℕ) :=
  List.ofFn fun i => ((endpointPair G i).1.val, (endpointPair G i).2.val)

theorem endpointList_length (G : EndpointGraph V E) :
    (endpointList G).length = Fintype.card E := by
  simp [endpointList]

theorem endpointPair_recovers (G : EndpointGraph V E) (i : Fin (Fintype.card E)) :
    (vertexEnumeration G (endpointPair G i).1 = G.bd₀ (edgeEnumeration G i)) ∧
    (vertexEnumeration G (endpointPair G i).2 = G.bd₁ (edgeEnumeration G i)) := by
  simp [endpointPair]

theorem endpointPair_loopless (G : EndpointGraph V E) (i : Fin (Fintype.card E)) :
    (endpointPair G i).1 ≠ (endpointPair G i).2 := by
  intro h
  exact G.loopless _ ((endpointPair_recovers G i).1.symm.trans
    ((congrArg (vertexEnumeration G) h).trans (endpointPair_recovers G i).2))

theorem endpointPair_bounds (G : EndpointGraph V E) (i : Fin (Fintype.card E)) :
    (endpointPair G i).1.val < Fintype.card V ∧
      (endpointPair G i).2.val < Fintype.card V :=
  ⟨(endpointPair G i).1.isLt, (endpointPair G i).2.isLt⟩

theorem vertexEnumeration_increasing (G : EndpointGraph V E)
    (i j : Fin (Fintype.card V)) :
    (letI := G.orderV; vertexEnumeration G i ≤ vertexEnumeration G j) ↔ i ≤ j := by
  letI := G.orderV
  exact (Fintype.orderIsoFinOfCardEq V rfl).le_iff_le

theorem edgeEnumeration_increasing (G : EndpointGraph V E)
    (i j : Fin (Fintype.card E)) :
    (letI := G.orderE; edgeEnumeration G i ≤ edgeEnumeration G j) ↔ i ≤ j := by
  letI := G.orderE
  exact (Fintype.orderIsoFinOfCardEq E rfl).le_iff_le

end EthInapproximability.CurrentPaper.SourceNormalization
