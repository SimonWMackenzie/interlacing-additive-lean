import EthInapproximability.CurrentPaper.Construction
import EthInapproximability.CurrentPaper.EdgeSourceGap

/-!
# The current paper's edge-only graph-vector producer

Source: v8 `A-stage4-details.tex`, `eq:paper-guarded-carriers`,
`eq:paper-guarded-q2`, `eq:paper-guarded-edge-evaluator`,
`eq:paper-guarded-size`; v8 `03-parameterized-construction.tex`,
`eq:paper-source-support` and `eq:paper-active-injection`.

The graph record, the unchanged least-power-of-two width, and the local
EDGE-coordinate evaluator/count are reused after inspection. The old global
edge-plus-incidence vector system is NOT used. Current real coordinates are
exactly `[4s] × E`, so parallel edge occurrences remain distinct. The explicit
item permutation below gives the original copy-major public order.

This module supplies actual vectors, their support bound, and the YES/NO
source conclusions under the explicit graph promises. It does not supply a
balanced second family, a graph-promise reduction, or a communication lower bound.
-/

namespace EthInapproximability.CurrentPaper.GraphVectors

open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open EthInapproximability.ParameterizedNP.GuardedSourceSlab
open Workspace.Types.CommComplexity

universe u v w

variable {V : Type u} {E : Type v}
  [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Increasing public vertex enumeration, using the graph's stored order. -/
def vertexEnum (G : EndpointGraph V E) : Fin (Fintype.card V) ≃ V := by
  letI := G.orderV
  exact (Fintype.orderIsoFinOfCardEq V rfl).toEquiv

/-- Increasing public EDGE-OCCURRENCE enumeration, not unordered endpoint pairs. -/
def edgeEnum (G : EndpointGraph V E) : Fin (Fintype.card E) ≃ E := by
  letI := G.orderE
  exact (Fintype.orderIsoFinOfCardEq E rfl).toEquiv

abbrev Item (V : Type u) (s : ℕ) := Fin (4 * s) × (V ⊕ Fin (s - 3))
abbrev RealCoordinate (E : Type v) (s : ℕ) := Fin (4 * s) × E

def vertexCount (V : Type u) [Fintype V] (s : ℕ) : ℕ := 4 * s * Fintype.card V
def auxiliaryCount (s : ℕ) : ℕ := 4 * s * (s - 3)

def vertexLabels (G : EndpointGraph V E) (s : ℕ) :
    Fin (vertexCount V s) ≃ Fin (4 * s) × V :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl _) (vertexEnum G))

def auxiliaryLabels (s : ℕ) :
    Fin (auxiliaryCount s) ≃ Fin (4 * s) × Fin (s - 3) := finProdFinEquiv.symm

/-- Copy-major rank: copy first, then vertices followed by auxiliary items. -/
def itemIndex (G : EndpointGraph V E) (s : ℕ) :
    Item V s ≃ Fin (vertexCount V s + auxiliaryCount s) :=
  ((Equiv.prodCongr (Equiv.refl (Fin (4 * s)))
      ((Equiv.sumCongr (vertexEnum G).symm (Equiv.refl (Fin (s - 3)))).trans
        finSumFinEquiv)).trans finProdFinEquiv).trans
    (finCongr (by simp only [vertexCount, auxiliaryCount]; ring))

/-- Grouped labels are converted back to actual copied graph items. -/
def groupedItems (G : EndpointGraph V E) (s : ℕ) :
    Fin (vertexCount V s + auxiliaryCount s) ≃ Item V s :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumCongr (vertexLabels G s) (auxiliaryLabels s)).trans
      (Equiv.prodSumDistrib (Fin (4 * s)) V (Fin (s - 3))).symm)

/-- This is the order parameter required by `Construction.rawMatrix`. -/
def itemOrder (G : EndpointGraph V E) (s : ℕ) :
    Construction.ItemOrder (vertexCount V s) (auxiliaryCount s) :=
  (groupedItems G s).trans (itemIndex G s)

theorem itemIndex_vertex_val (G : EndpointGraph V E) (s : ℕ)
    (r : Fin (4 * s)) (v : V) :
    (itemIndex G s (r, Sum.inl v)).val =
      r.val * (Fintype.card V + (s - 3)) + ((vertexEnum G).symm v).val := by
  simp [itemIndex, finProdFinEquiv]
  ring

theorem itemIndex_auxiliary_val (G : EndpointGraph V E) (s : ℕ)
    (r : Fin (4 * s)) (b : Fin (s - 3)) :
    (itemIndex G s (r, Sum.inr b)).val =
      r.val * (Fintype.card V + (s - 3)) + Fintype.card V + b.val := by
  simp [itemIndex, finProdFinEquiv]
  ring

@[simp] theorem itemOrder_vertex (G : EndpointGraph V E) (s : ℕ)
    (i : Fin (vertexCount V s)) :
    Construction.vertexIndex (itemOrder G s) i =
      itemIndex G s ((vertexLabels G s i).1, Sum.inl (vertexLabels G s i).2) := by
  simp [Construction.vertexIndex, itemOrder, groupedItems]

@[simp] theorem itemOrder_auxiliary (G : EndpointGraph V E) (s : ℕ)
    (i : Fin (auxiliaryCount s)) :
    Construction.auxiliaryIndex (itemOrder G s) i =
      itemIndex G s ((auxiliaryLabels s i).1, Sum.inr (auxiliaryLabels s i).2) := by
  simp [Construction.auxiliaryIndex, itemOrder, groupedItems]

/-- The real-coordinate rank is edge-major inside each copy, with no incidence slots. -/
def realIndex (G : EndpointGraph V E) (s : ℕ) :
    RealCoordinate E s ≃ Fin (4 * s * Fintype.card E) :=
  (Equiv.prodCongr (Equiv.refl _) (edgeEnum G).symm).trans finProdFinEquiv

theorem realIndex_val (G : EndpointGraph V E) (s : ℕ)
    (r : Fin (4 * s)) (e : E) :
    (realIndex G s (r, e)).val = r.val * Fintype.card E + ((edgeEnum G).symm e).val := by
  simp [realIndex, finProdFinEquiv]
  ring

theorem realCount_le_width (G : EndpointGraph V E) (s : ℕ) :
    4 * s * Fintype.card E ≤ q2 G s := by
  have h := card_le_q2 G s
  nlinarith

/-- Zero-based lexicographic rank of a real coordinate in the padded column carrier. -/
def coordinate (G : EndpointGraph V E) (s : ℕ) (z : RealCoordinate E s) : Fin (q2 G s) :=
  ⟨(realIndex G s z).val, (realIndex G s z).isLt.trans_le (realCount_le_width G s)⟩

theorem coordinate_injective (G : EndpointGraph V E) (s : ℕ) :
    Function.Injective (coordinate G s) := by
  intro z z' h
  have hv := congrArg (fun j : Fin (q2 G s) => j.val) h
  apply (realIndex G s).injective
  apply Fin.ext
  exact hv

theorem coordinate_exists_iff (G : EndpointGraph V E) (s : ℕ) (α : Fin (q2 G s)) :
    (∃ z, coordinate G s z = α) ↔ α.val < 4 * s * Fintype.card E := by
  constructor
  · rintro ⟨z, rfl⟩
    exact (realIndex G s z).isLt
  · intro h
    refine ⟨(realIndex G s).symm ⟨α.val, h⟩, ?_⟩
    apply Fin.ext
    simp [coordinate]

@[simp] theorem coordinate_val (G : EndpointGraph V E) (s : ℕ)
    (r : Fin (4 * s)) (e : E) :
    (coordinate G s (r, e)).val = r.val * Fintype.card E + ((edgeEnum G).symm e).val :=
  realIndex_val G s r e

/-- The genuine current edge-only evaluator on copied graph items. -/
def vector (G : EndpointGraph V E) (s : ℕ) (i : Item V s) (α : Fin (q2 G s)) : Bool :=
  decide (∃ z : RealCoordinate E s, coordinate G s z = α ∧ i.1 = z.1 ∧
    G.unslabbedRow s i.2 (Sum.inl z.2) = true)

@[simp] theorem vector_at_coordinate (G : EndpointGraph V E) (s : ℕ)
    (i : Item V s) (z : RealCoordinate E s) :
    vector G s i (coordinate G s z) = true ↔
      i.1 = z.1 ∧ G.unslabbedRow s i.2 (Sum.inl z.2) = true := by
  simp only [vector, decide_eq_true_eq]
  constructor
  · rintro ⟨w, hw, h1, h2⟩
    obtain rfl := coordinate_injective G s hw
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨z, rfl, h1, h2⟩

theorem vector_padding (G : EndpointGraph V E) (s : ℕ)
    (i : Item V s) (α : Fin (q2 G s)) (h : ∀ z, coordinate G s z ≠ α) :
    vector G s i α = false := by
  simp only [vector, decide_eq_false_iff_not]
  rintro ⟨z, hz, -, -⟩
  exact h z hz

theorem vector_padding_of_rank (G : EndpointGraph V E) (s : ℕ)
    (i : Item V s) (α : Fin (q2 G s)) (h : 4 * s * Fintype.card E ≤ α.val) :
    vector G s i α = false := by
  apply vector_padding
  intro z hz
  have hlt := (coordinate_exists_iff G s α).1 ⟨z, hz⟩
  omega

theorem vector_cross_copy (G : EndpointGraph V E) (s : ℕ)
    (r r' : Fin (4 * s)) (h : r ≠ r') (a : V ⊕ Fin (s - 3)) (e : E) :
    vector G s (r, a) (coordinate G s (r', e)) = false := by
  rw [Bool.eq_false_iff]
  intro ht
  exact h ((vector_at_coordinate G s (r, a) (r', e)).1 ht).1

@[simp] theorem vector_vertex (G : EndpointGraph V E) (s : ℕ)
    (r r' : Fin (4 * s)) (v : V) (e : E) :
    vector G s (r, Sum.inl v) (coordinate G s (r', e)) = true ↔
      r = r' ∧ (v = G.bd₀ e ∨ v = G.bd₁ e) := by
  simp [vector_at_coordinate, EndpointGraph.unslabbedRow]

@[simp] theorem vector_auxiliary (G : EndpointGraph V E) (s : ℕ)
    (r r' : Fin (4 * s)) (b : Fin (s - 3)) (e : E) :
    vector G s (r, Sum.inr b) (coordinate G s (r', e)) = true ↔ r = r' := by
  simp [vector_at_coordinate, EndpointGraph.unslabbedRow]

def activeItems (G : EndpointGraph V E) (s : ℕ) (α : Fin (q2 G s)) : Finset (Item V s) :=
  Finset.univ.filter (fun i => vector G s i α = true)

theorem activeItems_at_coordinate (G : EndpointGraph V E) (s : ℕ)
    (z : RealCoordinate E s) :
    activeItems G s (coordinate G s z) =
      (G.activeRows s (Sum.inl z.2)).image (fun a => (z.1, a)) := by
  ext i
  simp only [activeItems, Finset.mem_filter, Finset.mem_univ, true_and,
    vector_at_coordinate, Finset.mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨i.2, ?_, ?_⟩
    · simpa [EndpointGraph.activeRows] using h2
    · exact Prod.ext h1.symm rfl
  · rintro ⟨a, ha, hi⟩
    cases hi
    exact ⟨rfl, by simpa [EndpointGraph.activeRows] using ha⟩

theorem activeItems_card_real (G : EndpointGraph V E) {s : ℕ} (hs : 3 ≤ s)
    (z : RealCoordinate E s) :
    (activeItems G s (coordinate G s z)).card = s - 1 := by
  rw [activeItems_at_coordinate, Finset.card_image_of_injective _
    (fun a b h => congrArg Prod.snd h)]
  exact G.card_activeRows_edge hs z.2

theorem activeItems_card_le (G : EndpointGraph V E) {s : ℕ} (hs : 3 ≤ s)
    (α : Fin (q2 G s)) : (activeItems G s α).card ≤ s := by
  by_cases h : ∃ z, coordinate G s z = α
  · obtain ⟨z, rfl⟩ := h
    rw [activeItems_card_real G hs z]
    omega
  · have hp : ∀ z, coordinate G s z ≠ α := by simpa using h
    have hz : activeItems G s α = ∅ := by
      ext i
      simp [activeItems, vector_padding G s i α hp]
    simp [hz]

/-- The input vectors indexed in the original copy-major order. -/
def vectors (G : EndpointGraph V E) (s : ℕ) :
    Fin (vertexCount V s + auxiliaryCount s) → Fin (q2 G s) → Bool :=
  fun i α => vector G s ((itemIndex G s).symm i) α

@[simp] theorem vectors_itemIndex (G : EndpointGraph V E) (s : ℕ)
    (i : Item V s) (α : Fin (q2 G s)) :
    vectors G s (itemIndex G s i) α = vector G s i α := by simp [vectors]

theorem indexed_activeItems (G : EndpointGraph V E) (s : ℕ) (α : Fin (q2 G s)) :
    Construction.activeItems (vectors G s) α = (activeItems G s α).image (itemIndex G s) := by
  ext i
  simp only [Construction.activeItems, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_image]
  constructor
  · intro hi
    exact ⟨(itemIndex G s).symm i, by simpa [activeItems, vectors] using hi,
      (itemIndex G s).apply_symm_apply i⟩
  · rintro ⟨x, hx, rfl⟩
    simpa [activeItems] using hx

theorem supportCap (G : EndpointGraph V E) {s : ℕ} (hs : 3 ≤ s)
    (α : Fin (q2 G s)) : (Construction.activeItems (vectors G s) α).card ≤ s := by
  rw [indexed_activeItems, Finset.card_image_of_injective _ (itemIndex G s).injective]
  exact activeItems_card_le G hs α

/-- The YES branch uses only the edge restriction of the audited local legal
packing. Incidence columns are not reintroduced into the current construction. -/
theorem legal_of_sourceYES (G : EndpointGraph V E) {s : ℕ} (hs : 4 ≤ s)
    (hnoiso : ∀ v : V, 1 ≤ G.degree v) (hyes : G.SourceYES) :
    ∃ φ : Item V s → Fin s,
      Legal (vector G s) Finset.univ φ ∧ ∀ J, Legal (vector G s) J φ := by
  classical
  obtain ⟨φ₀, hφ₀⟩ := (G.source_completeness hs hnoiso).2 hyes
  have hlegal : Legal (vector G s) Finset.univ (fun i => φ₀ i.2) := by
    intro b α
    by_cases h : ∃ z, coordinate G s z = α
    · obtain ⟨⟨r, e⟩, rfl⟩ := h
      have heq : activeSet (vector G s) Finset.univ (fun i => φ₀ i.2) b
          (coordinate G s (r, e)) =
          ({r} : Finset (Fin (4 * s))) ×ˢ
            activeSet (G.unslabbedRow s) Finset.univ φ₀ b (Sum.inl e) := by
        ext i
        rcases i with ⟨r', a⟩
        simp only [mem_activeSet, Finset.mem_univ, true_and,
          vector_at_coordinate, Finset.mem_product, Finset.mem_singleton]
        tauto
      rw [heq, Finset.card_product, Finset.card_singleton, one_mul]
      exact hφ₀ b (Sum.inl e)
    · have hp : ∀ z, coordinate G s z ≠ α := by simpa using h
      have heq : activeSet (vector G s) Finset.univ (fun i => φ₀ i.2) b α = ∅ := by
        ext i
        simp [mem_activeSet, vector_padding G s i α hp]
      simp [heq]
  exact ⟨fun i => φ₀ i.2, hlegal, fun J => hlegal.mono (Finset.subset_univ J)⟩

/-- The legal bin assignment is transported to exactly the vector indices used by `B`. -/
theorem indexed_legal_of_sourceYES (G : EndpointGraph V E) {s : ℕ} (hs : 4 ≤ s)
    (hnoiso : ∀ v : V, 1 ≤ G.degree v) (hyes : G.SourceYES) :
    ∃ φ : Fin (vertexCount V s + auxiliaryCount s) → Fin s,
      Legal (vectors G s) Finset.univ φ ∧ ∀ J, Legal (vectors G s) J φ := by
  classical
  obtain ⟨φ, hφ, _⟩ := legal_of_sourceYES G hs hnoiso hyes
  let ψ : Fin (vertexCount V s + auxiliaryCount s) → Fin s :=
    fun i => φ ((itemIndex G s).symm i)
  have hlegal : Legal (vectors G s) Finset.univ ψ := by
    intro b α
    have heq : activeSet (vectors G s) Finset.univ ψ b α =
        (activeSet (vector G s) Finset.univ φ b α).image (itemIndex G s) := by
      ext i
      simp only [mem_activeSet, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · rintro ⟨hb, hv⟩
        exact ⟨(itemIndex G s).symm i, ⟨hb, hv⟩, (itemIndex G s).apply_symm_apply i⟩
      · rintro ⟨j, ⟨hb, hv⟩, rfl⟩
        simpa [ψ, vectors] using And.intro hb hv
    rw [heq, Finset.card_image_of_injective _ (itemIndex G s).injective]
    exact hφ b α
  exact ⟨ψ, hlegal, fun J => hlegal.mono (Finset.subset_univ J)⟩

/-- Two retained active items plus a retained item from a different copy
produce exactly the overload-plus-inactive witness required by the paper. -/
theorem witness_of_two_and_foreign (G : EndpointGraph V E) (s : ℕ)
    (J : Finset (Item V s)) (φ : Item V s → Fin s) (z : RealCoordinate E s)
    (i j k : Item V s) (hij : i ≠ j) (hi : i ∈ J) (hj : j ∈ J) (hk : k ∈ J)
    (hbin : φ i = φ j) (hkbin : φ k = φ i)
    (hvi : vector G s i (coordinate G s z) = true)
    (hvj : vector G s j (coordinate G s z) = true) (hforeign : k.1 ≠ z.1) :
    coordinate G s z ∈ Wit (vector G s) J φ := by
  classical
  rw [mem_Wit]
  refine ⟨φ i, ?_, k, ?_, ?_⟩
  · have hsub : ({i, j} : Finset (Item V s)) ⊆
        activeSet (vector G s) J φ (φ i) (coordinate G s z) := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact (mem_activeSet ..).2 ⟨⟨hi, rfl⟩, hvi⟩
      · obtain rfl := Finset.mem_singleton.mp hx
        exact (mem_activeSet ..).2 ⟨⟨hj, hbin.symm⟩, hvj⟩
    have hcard := Finset.card_le_card hsub
    simpa [hij] using hcard
  · exact (mem_binOf ..).2 ⟨hk, hkbin⟩
  · exact vector_cross_copy G s k.1 z.1 hforeign k.2 z.2

theorem witness_of_edge_collision (G : EndpointGraph V E) (s : ℕ)
    (J : Finset (Item V s)) (φ : Item V s → Fin s) (r : Fin (4 * s)) (e : E)
    (k : Item V s)
    (hleft : (r, Sum.inl (G.bd₀ e)) ∈ J) (hright : (r, Sum.inl (G.bd₁ e)) ∈ J)
    (hk : k ∈ J) (hbin : φ (r, Sum.inl (G.bd₀ e)) = φ (r, Sum.inl (G.bd₁ e)))
    (hkbin : φ k = φ (r, Sum.inl (G.bd₀ e))) (hforeign : k.1 ≠ r) :
    coordinate G s (r, e) ∈ Wit (vector G s) J φ := by
  apply witness_of_two_and_foreign G s J φ (r, e)
    (r, Sum.inl (G.bd₀ e)) (r, Sum.inl (G.bd₁ e)) k
    (by simpa using G.loopless e) hleft hright hk hbin hkbin
  · simp
  · simp
  · exact hforeign

/-- The overloaded coordinates of one copy are edge occurrences only. -/
def localEdgeOver (G : EndpointGraph V E) (s : ℕ) (J : Finset (Item V s))
    (φ : Item V s → Fin s) (r : Fin (4 * s)) : Finset E :=
  Over (EdgeSourceGap.edgeRow G s) (localRetained s J r) (localAssign s φ r)

theorem card_activeSet_edge_local_le (G : EndpointGraph V E) (s : ℕ)
    (J : Finset (Item V s)) (φ : Item V s → Fin s) (r : Fin (4 * s))
    (b : Fin s) (e : E) :
    (activeSet (EdgeSourceGap.edgeRow G s) (localRetained s J r)
      (localAssign s φ r) b e).card ≤
      (activeSet (vector G s) J φ b (coordinate G s (r, e))).card := by
  refine Finset.card_le_card_of_injOn (fun a => ((r, a) : Item V s)) ?_ ?_
  · intro a ha
    simp only [Finset.mem_coe, mem_activeSet, mem_localRetained] at ha ⊢
    obtain ⟨⟨hJ, hb⟩, hv⟩ := ha
    exact ⟨⟨hJ, hb⟩, (vector_at_coordinate G s (r, a) (r, e)).2 ⟨rfl, hv⟩⟩
  · intro a _ a' _ h
    exact congrArg Prod.snd h

/-- The older private-bin set is used only as a conservative superset: an
edge-overloaded bin confined to one copy belongs to it. Its row-only count is
valid for this purpose; no old global vector or incidence witness is used. -/
theorem witness_of_nonprivate_edge (G : EndpointGraph V E) (s : ℕ)
    (J : Finset (Item V s)) (φ : Item V s → Fin s) (r : Fin (4 * s))
    (hr : ¬ (privateBins G s J φ r).Nonempty) {e : E}
    (he : e ∈ localEdgeOver G s J φ r) :
    coordinate G s (r, e) ∈ Wit (vector G s) J φ := by
  rw [localEdgeOver, mem_Over] at he
  obtain ⟨b, hb⟩ := he
  rw [mem_Wit]
  refine ⟨b, hb.trans (card_activeSet_edge_local_le G s J φ r b e), ?_⟩
  have hnb : b ∉ privateBins G s J φ r := fun hc => hr ⟨b, hc⟩
  rw [mem_privateBins] at hnb
  have hnsub : ¬ (binOf J φ b ⊆ rowSlab V s r) :=
    fun hc => hnb ⟨hc, ⟨Sum.inl e, hb⟩⟩
  obtain ⟨i, hi, hi'⟩ := Finset.not_subset.mp hnsub
  refine ⟨i, hi, ?_⟩
  rw [mem_rowSlab] at hi'
  exact vector_cross_copy G s i.1 r hi' i.2 e

/-- The current edge-only deletion-stable source theorem. The two deletion
budgets are precisely `RetentionOK`: fewer than `(s/2) δᵥ |V|` vertex items
and fewer than `s/2` auxiliary items. The conclusion counts actual padded
coordinates of `vector`, not coordinates of the older incidence construction. -/
theorem witness_of_sourceNO (G : EndpointGraph V E) {s : ℕ} (hs : 4 ≤ s)
    {Δ : ℕ} (hΔ : 0 < Δ) {γ : ℚ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hdeg : ∀ v : V, G.degree v ≤ Δ) (hno : G.SourceNO γ)
    (J : Finset (Item V s)) (hJ : RetentionOK G s γ Δ J)
    (φ : Item V s → Fin s) :
    (γ / 24) * (q2 G s : ℚ) ≤ ((Wit (vector G s) J φ).card : ℚ) := by
  classical
  have hm : (0 : ℚ) < Fintype.card E := by exact_mod_cast G.card_edge_pos
  have hgood := three_mul_lt_card_goodSlabs G hs hΔ hγ0 J hJ
  let T := (goodSlabs G s γ Δ J).filter fun r => ¬ (privateBins G s J φ r).Nonempty
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := goodSlabs G s γ Δ J) (fun r => (privateBins G s J φ r).Nonempty)
  have hPriv := card_privateSlabs_le G s γ Δ J φ
  have hNonPriv : (2 * s : ℚ) < (T.card : ℚ) := by
    have h1 : (((goodSlabs G s γ Δ J).filter
        fun r => (privateBins G s J φ r).Nonempty).card : ℚ) ≤ s := by
      exact_mod_cast hPriv
    have h2 : (((goodSlabs G s γ Δ J).filter
        fun r => (privateBins G s J φ r).Nonempty).card : ℚ) + (T.card : ℚ) =
        ((goodSlabs G s γ Δ J).card : ℚ) := by exact_mod_cast hsplit
    linarith
  have hOloc : ∀ r ∈ goodSlabs G s γ Δ J,
      γ * (Fintype.card E : ℚ) / 2 ≤ ((localEdgeOver G s J φ r).card : ℚ) := by
    intro r hr
    rw [mem_goodSlabs] at hr
    have heq : (Finset.univ.filter fun v : V =>
        (Sum.inl v : Row V s) ∉ localRetained s J r) = deletedVertices s J r := by
      ext v
      simp [deletedVertices, mem_localRetained]
    exact EdgeSourceGap.source_one_copy G hs hΔ hγ0 hγ1 hno hdeg
      (localRetained s J r) (fun b => by rw [mem_localRetained]; exact hr.1 b)
      (by rw [heq]; exact hr.2) (localAssign s φ r)
  have hdisj : ∀ r ∈ T, ∀ r' ∈ T, r ≠ r' →
      Disjoint ((localEdgeOver G s J φ r).image fun e => coordinate G s (r, e))
        ((localEdgeOver G s J φ r').image fun e => coordinate G s (r', e)) := by
    intro r _ r' _ hne
    rw [Finset.disjoint_left]
    intro j hj hj'
    obtain ⟨e, _, he⟩ := Finset.mem_image.mp hj
    obtain ⟨e', _, he'⟩ := Finset.mem_image.mp hj'
    exact hne (congrArg Prod.fst (coordinate_injective G s (he.trans he'.symm)))
  have hWsub : (T.biUnion fun r =>
      (localEdgeOver G s J φ r).image fun e => coordinate G s (r, e)) ⊆
        Wit (vector G s) J φ := by
    intro j hj
    obtain ⟨r, hr, hjr⟩ := Finset.mem_biUnion.mp hj
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hjr
    exact witness_of_nonprivate_edge G s J φ r (Finset.mem_filter.mp hr).2 he
  have hWcard : (T.biUnion fun r =>
      (localEdgeOver G s J φ r).image fun e => coordinate G s (r, e)).card =
        ∑ r ∈ T, (localEdgeOver G s J φ r).card := by
    rw [Finset.card_biUnion hdisj]
    refine Finset.sum_congr rfl fun r _ => ?_
    exact Finset.card_image_of_injective _ (fun e e' h =>
      congrArg Prod.snd (coordinate_injective G s h))
  have hsum : (T.card : ℚ) * (γ * (Fintype.card E : ℚ) / 2) ≤
      ∑ r ∈ T, ((localEdgeOver G s J φ r).card : ℚ) := by
    have h := Finset.sum_le_sum (s := T)
      (f := fun _ : Fin (4 * s) => γ * (Fintype.card E : ℚ) / 2)
      (g := fun r => ((localEdgeOver G s J φ r).card : ℚ))
      (fun r hr => hOloc r (Finset.mem_filter.mp hr).1)
    simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using h
  have hcast : ((T.biUnion fun r =>
      (localEdgeOver G s J φ r).image fun e => coordinate G s (r, e)).card : ℚ) =
        ∑ r ∈ T, ((localEdgeOver G s J φ r).card : ℚ) := by
    rw [hWcard]
    push_cast
    ring
  have hWle : ((T.biUnion fun r =>
      (localEdgeOver G s J φ r).image fun e => coordinate G s (r, e)).card : ℚ) ≤
        ((Wit (vector G s) J φ).card : ℚ) := by
    exact_mod_cast Finset.card_le_card hWsub
  have hpos : (0 : ℚ) < γ * (Fintype.card E : ℚ) / 2 := by positivity
  have hstrict := mul_lt_mul_of_pos_right hNonPriv hpos
  have hq2 : (q2 G s : ℚ) < 24 * (s : ℚ) * (Fintype.card E : ℚ) := by
    exact_mod_cast q2_lt G hs
  have hfinal := mul_lt_mul_of_pos_left hq2 (show (0 : ℚ) < γ / 24 by positivity)
  have hring : γ / 24 * (24 * (s : ℚ) * (Fintype.card E : ℚ)) =
      (2 * s : ℚ) * (γ * (Fintype.card E : ℚ) / 2) := by ring
  linarith

/-- Retained finite indices, read back as the original copied graph items. -/
def retainedItems (G : EndpointGraph V E) (s : ℕ)
    (J : Finset (Fin (vertexCount V s + auxiliaryCount s))) : Finset (Item V s) :=
  J.image (itemIndex G s).symm

@[simp] theorem mem_retainedItems (G : EndpointGraph V E) (s : ℕ)
    (J : Finset (Fin (vertexCount V s + auxiliaryCount s))) (i : Item V s) :
    i ∈ retainedItems G s J ↔ itemIndex G s i ∈ J := by
  constructor
  · intro h
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
    simpa using hj
  · intro h
    exact Finset.mem_image.mpr ⟨itemIndex G s i, h, (itemIndex G s).symm_apply_apply i⟩

/-- Active sets are transported without loss to the actual `Fin` indices of `B`. -/
theorem indexed_activeSet (G : EndpointGraph V E) (s : ℕ)
    (J : Finset (Fin (vertexCount V s + auxiliaryCount s)))
    (φ : Fin (vertexCount V s + auxiliaryCount s) → Fin s)
    (b : Fin s) (α : Fin (q2 G s)) :
    activeSet (vectors G s) J φ b α =
      (activeSet (vector G s) (retainedItems G s J)
        (fun i => φ (itemIndex G s i)) b α).image (itemIndex G s) := by
  ext i
  simp only [mem_activeSet, mem_retainedItems, Finset.mem_image]
  constructor
  · rintro ⟨⟨hi, hb⟩, hv⟩
    exact ⟨(itemIndex G s).symm i,
      by simpa [vectors] using And.intro (And.intro hi hb) hv,
      (itemIndex G s).apply_symm_apply i⟩
  · rintro ⟨j, ⟨⟨hj, hb⟩, hv⟩, rfl⟩
    exact ⟨⟨hj, hb⟩, by simpa using hv⟩

theorem indexed_witnesses (G : EndpointGraph V E) (s : ℕ)
    (J : Finset (Fin (vertexCount V s + auxiliaryCount s)))
    (φ : Fin (vertexCount V s + auxiliaryCount s) → Fin s) :
    Wit (vectors G s) J φ = Wit (vector G s) (retainedItems G s J)
      (fun i => φ (itemIndex G s i)) := by
  ext α
  simp only [mem_Wit, indexed_activeSet,
    Finset.card_image_of_injective _ (itemIndex G s).injective]
  constructor
  · rintro ⟨b, hb, i, hi, hv⟩
    refine ⟨b, hb, (itemIndex G s).symm i, ?_, hv⟩
    simpa [mem_binOf] using hi
  · rintro ⟨b, hb, i, hi, hv⟩
    refine ⟨b, hb, itemIndex G s i, ?_, ?_⟩
    · simpa [mem_binOf] using hi
    · simpa using hv

/-- Count the deleted vertex items in the grouped row labels of `B`. -/
theorem deleted_vertex_card (G : EndpointGraph V E) (s : ℕ)
    (J : Finset (Fin (vertexCount V s + auxiliaryCount s))) :
    (Finset.univ.filter fun i : Fin (vertexCount V s) =>
      Construction.vertexIndex (itemOrder G s) i ∉ J).card =
    (Finset.univ.filter fun x : Fin (4 * s) × V =>
      (x.1, Sum.inl x.2) ∉ retainedItems G s J).card := by
  apply Finset.card_bij (fun i _ => vertexLabels G s i)
  · intro i hi
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, mem_retainedItems,
      itemOrder_vertex] using hi
  · intro i _ j _ h
    exact (vertexLabels G s).injective h
  · intro x hx
    refine ⟨(vertexLabels G s).symm x, ?_, (vertexLabels G s).apply_symm_apply x⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, mem_retainedItems,
      itemOrder_vertex, Equiv.apply_symm_apply] using hx

theorem deleted_auxiliary_card (G : EndpointGraph V E) (s : ℕ)
    (J : Finset (Fin (vertexCount V s + auxiliaryCount s))) :
    (Finset.univ.filter fun i : Fin (auxiliaryCount s) =>
      Construction.auxiliaryIndex (itemOrder G s) i ∉ J).card =
    (Finset.univ.filter fun x : Fin (4 * s) × Fin (s - 3) =>
      (x.1, Sum.inr x.2) ∉ retainedItems G s J).card := by
  apply Finset.card_bij (fun i _ => auxiliaryLabels s i)
  · intro i hi
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, mem_retainedItems,
      itemOrder_auxiliary] using hi
  · intro i _ j _ h
    exact (auxiliaryLabels s).injective h
  · intro x hx
    refine ⟨(auxiliaryLabels s).symm x, ?_, (auxiliaryLabels s).apply_symm_apply x⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, mem_retainedItems,
      itemOrder_auxiliary, Equiv.apply_symm_apply] using hx

/-- The source conclusion on the exact vector indices used by `rawMatrix`,
with deletion budgets stated directly on its vertex and auxiliary labels. -/
theorem indexed_witness_of_sourceNO (G : EndpointGraph V E) {s : ℕ} (hs : 4 ≤ s)
    {Δ : ℕ} (hΔ : 0 < Δ) {γ : ℚ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hdeg : ∀ v : V, G.degree v ≤ Δ) (hno : G.SourceNO γ)
    (J : Finset (Fin (vertexCount V s + auxiliaryCount s)))
    (hJv : ((Finset.univ.filter fun i : Fin (vertexCount V s) =>
      Construction.vertexIndex (itemOrder G s) i ∉ J).card : ℚ) <
        (s : ℚ) / 2 * (G.deltaV γ Δ * (Fintype.card V : ℚ)))
    (hJb : ((Finset.univ.filter fun i : Fin (auxiliaryCount s) =>
      Construction.auxiliaryIndex (itemOrder G s) i ∉ J).card : ℚ) < (s : ℚ) / 2)
    (φ : Fin (vertexCount V s + auxiliaryCount s) → Fin s) :
    (γ / 24) * (q2 G s : ℚ) ≤ ((Wit (vectors G s) J φ).card : ℚ) := by
  rw [indexed_witnesses]
  apply witness_of_sourceNO G hs hΔ hγ0 hγ1 hdeg hno
  constructor
  · simpa only [deleted_vertex_card] using hJv
  · simpa only [deleted_auxiliary_card] using hJb

/-- The number of nonzero entries in the edge-only vector table. -/
def activeIncidences (G : EndpointGraph V E) (s : ℕ) :
    Finset (Item V s × Fin (q2 G s)) :=
  Finset.univ.filter fun z => vector G s z.1 z.2

theorem card_activeIncidences (G : EndpointGraph V E) {s : ℕ} (hs : 3 ≤ s) :
    (activeIncidences G s).card = 4 * s * Fintype.card E * (s - 1) := by
  classical
  have hsum : (activeIncidences G s).card =
      ∑ α : Fin (q2 G s), (activeItems G s α).card := by
    rw [activeIncidences, Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
    exact Finset.sum_congr rfl fun α _ => by rw [activeItems, Finset.card_filter]
  rw [hsum]
  have hreal : ∑ α : Fin (q2 G s), (activeItems G s α).card =
      ∑ α ∈ Finset.univ.image (coordinate G s), (activeItems G s α).card := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro α _ hα
    have hp : ∀ z, coordinate G s z ≠ α := fun z hz =>
      hα (Finset.mem_image.mpr ⟨z, Finset.mem_univ _, hz⟩)
    have heq : activeItems G s α = ∅ := by
      ext i
      simp [activeItems, vector_padding G s i α hp]
    simp [heq]
  rw [hreal, Finset.sum_image]
  · simp only [activeItems_card_real G hs]
    simp [RealCoordinate, mul_assoc]
  · intro x _ y _ h
    exact coordinate_injective G s h

omit [DecidableEq E] in
theorem card_realCoordinate (s : ℕ) :
    Fintype.card (RealCoordinate E s) = 4 * s * Fintype.card E := by
  simp [RealCoordinate]

omit [DecidableEq V] in
theorem card_item (s : ℕ) :
    Fintype.card (Item V s) = 4 * s * (Fintype.card V + (s - 3)) := by
  simp [Item]

/-- The current width is the least power of two above `12s|E|`, with the
paper's strict upper bound. This does not import any old parameter schedule. -/
theorem width_spec (G : EndpointGraph V E) {s : ℕ} (hs : 4 ≤ s) :
    (∃ r : ℕ, q2 G s = 2 ^ r) ∧
    12 * s * Fintype.card E ≤ q2 G s ∧
    q2 G s < 24 * s * Fintype.card E ∧
    (∀ r : ℕ, 12 * s * Fintype.card E ≤ 2 ^ r → q2 G s ≤ 2 ^ r) :=
  ⟨q2_isPowTwo G s, card_le_q2 G s, q2_lt G hs, fun _ h => q2_le_of_le G s h⟩

/-- The finite part of `thm:paper-guarded-source`, for the actual edge-only
producer. The YES and NO promises occur as separate implications. Sparse
encoding size and machine running time are deliberately not claimed here. -/
theorem graph_source (G : EndpointGraph V E) {s : ℕ} (hs : 4 ≤ s)
    {Δ : ℕ} (hΔ : 0 < Δ) {γ : ℚ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hnoiso : ∀ v : V, 1 ≤ G.degree v) (hdeg : ∀ v : V, G.degree v ≤ Δ) :
    (G.SourceYES → ∃ φ : Item V s → Fin s,
      Legal (vector G s) Finset.univ φ ∧ ∀ J, Legal (vector G s) J φ) ∧
    (G.SourceNO γ → ∀ J : Finset (Item V s), RetentionOK G s γ Δ J →
      ∀ φ : Item V s → Fin s,
      (γ / 24) * (q2 G s : ℚ) ≤ ((Wit (vector G s) J φ).card : ℚ)) ∧
    (∀ α, (Construction.activeItems (vectors G s) α).card ≤ s) ∧
    Fintype.card (Item V s) = 4 * s * (Fintype.card V + (s - 3)) ∧
    Fintype.card (RealCoordinate E s) = 4 * s * Fintype.card E ∧
    (activeIncidences G s).card = 4 * s * Fintype.card E * (s - 1) :=
  ⟨legal_of_sourceYES G hs hnoiso,
    fun hno J hJ φ => witness_of_sourceNO G hs hΔ hγ0 hγ1 hdeg hno J hJ φ,
    supportCap G (by omega), card_item s, card_realCoordinate s,
    card_activeIncidences G (by omega)⟩

section Matrices

variable {X Y : Type w} [Fintype X] [Fintype Y]

def rawMatrix (G : EndpointGraph V E) (R : X → Y → Bool)
    (a s L : ℕ) (hs : 4 ≤ s) (family : Construction.SecondFamily a (q2 G s) L X) :=
  Construction.rawMatrix R a s (q2 G s) L (vertexCount V s) (auxiliaryCount s)
    (by omega) family (itemOrder G s) (vectors G s) (supportCap G (by omega))

def protectedMatrix (G : EndpointGraph V E) (R : X → Y → Bool)
    (a s L : ℕ) (hs : 4 ≤ s) (family : Construction.SecondFamily a (q2 G s) L X) :=
  Construction.protectedMatrix R a s (q2 G s) L (vertexCount V s) (auxiliaryCount s)
    (by omega) family (itemOrder G s) (vectors G s) (supportCap G (by omega))

theorem card_rawRows (_G : EndpointGraph V E) (s L : ℕ) :
    Fintype.card (Construction.RawRows s L (vertexCount V s) (auxiliaryCount s) X) =
      s * L + 4 * s * (Fintype.card V + (s - 3)) * Fintype.card X := by
  rw [Construction.card_rawRows]
  simp only [vertexCount, auxiliaryCount]
  ring

theorem card_rawColumns (G : EndpointGraph V E) (a s : ℕ) :
    Fintype.card (Construction.RawColumns a s (q2 G s) Y) =
      Fintype.card Y ^ (s + 1) *
        (q2 G s * Fintype.card Y ^ Construction.firstLength a s) ^ s :=
  Construction.card_rawColumns a s (q2 G s)

theorem card_protectedRows (_G : EndpointGraph V E) (s L : ℕ) :
    Fintype.card (Construction.ProtectedRows s L (vertexCount V s) (auxiliaryCount s) X) =
      2 ^ 22 * (s * L + 4 * s * (Fintype.card V + (s - 3)) * Fintype.card X) *
        (s * L) * (4 * s * Fintype.card V * Fintype.card X) *
        (4 * s * (s - 3) * Fintype.card X) := by
  rw [Construction.card_protectedRows]
  simp only [vertexCount, auxiliaryCount]
  ring

theorem card_protectedColumns (G : EndpointGraph V E) (a s : ℕ) :
    Fintype.card (Construction.ProtectedColumns a s (q2 G s) Y) =
      184 * (Fintype.card Y ^ (s + 1) *
        (q2 G s * Fintype.card Y ^ Construction.firstLength a s) ^ s) *
        (q2 G s * Fintype.card Y ^ Construction.firstLength a s) *
        (q2 G s * Fintype.card Y ^ Construction.firstLength a s) ^ s :=
  Construction.card_protectedColumns a s (q2 G s)

theorem D_protectedMatrix [Nonempty X] [Nonempty Y]
    (G : EndpointGraph V E) (R : X → Y → Bool)
    (a s L : ℕ) (hs : 4 ≤ s) (hL : 0 < L)
    (family : Construction.SecondFamily a (q2 G s) L X) :
    D (protectedMatrix G R a s L hs family) = D (rawMatrix G R a s L hs family) := by
  apply Construction.D_protectedMatrix
  · exact q2_pos G s
  · exact hL
  · unfold vertexCount
    exact Nat.mul_pos (by omega) G.card_vertex_pos
  · unfold auxiliaryCount
    exact Nat.mul_pos (by omega) (by omega)

end Matrices

end EthInapproximability.CurrentPaper.GraphVectors
