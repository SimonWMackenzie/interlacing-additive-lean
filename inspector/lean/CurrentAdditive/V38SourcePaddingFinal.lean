import CurrentAdditive.GraphCopyPadding
import Paper2.CanonicalEdgeTape

/-!
Selected v38 `appendices/sources.tex:69-76`: the source graph H is copied to
make at least N edge occurrences. This is separate from the removed late
cutoff copy in v37 `sections/sampling.tex:202-220`.
-/

namespace Paper2.CurrentAdditive.V38SourcePaddingFinal

open EthInapproximability.CurrentPaper
open Paper2.CurrentAdditive.GraphCopyPadding

theorem copy_edge_bounds (N m : ℕ) (hm : 0 < m) :
    N ≤ copies N m * m ∧ copies N m * m ≤ N + m := by
  by_cases hN : 2 ≤ N
  · obtain ⟨_, hlo, hu⟩ := copies_bounds N m hN hm
    exact ⟨hlo, le_of_lt (by omega)⟩
  · have hsmall : N = 0 ∨ N = 1 := by omega
    rcases hsmall with rfl | rfl
    · have hq : (m - 1) / m = 0 := Nat.div_eq_zero_iff.mpr (by omega)
      simp [copies, hq]
    · simp [copies, Nat.div_self hm]
      omega

/-- On the source graph, each labelled occurrence is retained in every copy. -/
theorem encoded_edge_bounds (g : EncodedGraph.Graph) (N : ℕ)
    (hm : 0 < g.edges.length) :
    N ≤ (encodedCopies g (copies N g.edges.length)).edges.length ∧
    (encodedCopies g (copies N g.edges.length)).edges.length ≤ N + g.edges.length := by
  rw [encodedCopies_edges_length]
  exact copy_edge_bounds N g.edges.length hm

theorem encoded_vertex_bound (g : EncodedGraph.Graph) (N : ℕ) :
    (encodedCopies g (copies N g.edges.length)).vertices =
      copies N g.edges.length * g.vertices := rfl

def ProperNat (g : EncodedGraph.Graph) : Prop :=
  ∃ colour : ℕ → Fin 3, ∀ p ∈ g.edges, colour p.1 ≠ colour p.2

theorem encoded_proper_iff (g : EncodedGraph.Graph) (hg : g.Valid)
    (c : ℕ) (hc : 0 < c) :
    ProperNat (encodedCopies g c) ↔ ProperNat g := by
  constructor
  · rintro ⟨colour, hcolour⟩
    refine ⟨colour, ?_⟩
    intro p hp
    have hcp : (0 * g.vertices + p.1, 0 * g.vertices + p.2) ∈
        (encodedCopies g c).edges :=
      (encodedCopies_edge_mem g c _).2 ⟨0, hc, p, hp, rfl⟩
    simpa using hcolour _ hcp
  · rintro ⟨colour, hcolour⟩
    refine ⟨fun v => colour (v % g.vertices), ?_⟩
    intro p hp
    obtain ⟨j, hj, q, hq, rfl⟩ := (encodedCopies_edge_mem g c p).1 hp
    obtain ⟨hu, hv, _⟩ := hg q hq
    simpa [Nat.add_mod, Nat.mul_mod_right, Nat.mod_eq_of_lt hu,
      Nat.mod_eq_of_lt hv] using hcolour q hq

def NoIsolatesNat (g : EncodedGraph.Graph) : Prop :=
  ∀ v < g.vertices, ∃ p ∈ g.edges, v = p.1 ∨ v = p.2

theorem encoded_no_isolates (g : EncodedGraph.Graph) (c : ℕ)
    (hn : 0 < g.vertices) (h : NoIsolatesNat g) :
    NoIsolatesNat (encodedCopies g c) := by
  intro v hv
  let j := v / g.vertices
  let r := v % g.vertices
  have hj : j < c := (Nat.div_lt_iff_lt_mul hn).2 (by simpa [encodedCopies, Nat.mul_comm] using hv)
  have hr : r < g.vertices := Nat.mod_lt _ hn
  obtain ⟨p, hp, hvp⟩ := h r hr
  have hmem : (j * g.vertices + p.1, j * g.vertices + p.2) ∈
      (encodedCopies g c).edges :=
    (encodedCopies_edge_mem g c _).2 ⟨j, hj, p, hp, rfl⟩
  refine ⟨(j * g.vertices + p.1, j * g.vertices + p.2), hmem, ?_⟩
  have hident : v = j * g.vertices + r := by
    simpa only [j, r, Nat.mul_comm, Nat.add_comm] using
      (Nat.mod_add_div v g.vertices).symm
  rcases hvp with hp1 | hp2
  · left; omega
  · right; omega

theorem copied_degree {V E : Type*} [Fintype E] (c Δ : ℕ)
    (edge : E → Bool → V)
    (h : ∀ v, SourceItems.degree edge v ≤ Δ) :
    ∀ v, SourceItems.degree (copyEdge c edge) v ≤ Δ :=
  degree_bound c edge Δ h

theorem copied_gap {V E : Type*} [Fintype E] (c : ℕ)
    (edge : E → Bool → V) (γ : ℚ)
    (h : ∀ colour : V → Fin 3,
      γ * (Fintype.card E : ℚ) ≤ (monochromatic edge colour).card) :
    ∀ colour : Vertices c V → Fin 3,
      γ * (Fintype.card (Edges c E) : ℚ) ≤
        ((Finset.univ.filter (fun e : Edges c E =>
          colour (copyEdge c edge e false) = colour (copyEdge c edge e true))).card : ℚ) :=
  monochromatic_gap c edge γ h

theorem degree_sum_eq {V E : Type*} [Fintype V] [Fintype E]
    (edge : E → Bool → V) :
    (∑ v : V, SourceItems.degree edge v) = 2 * Fintype.card E := by
  classical
  simp only [SourceItems.degree, Finset.card_eq_sum_ones,
    Finset.sum_filter, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp only [Finset.sum_comm (s := (Finset.univ : Finset V))]
  simp [Nat.mul_comm]

theorem source_edge_vertex_bounds {V E : Type*} [Fintype V] [Fintype E]
    (edge : E → Bool → V) (Δ : ℕ)
    (hno : ∀ v : V, ∃ e b, edge e b = v)
    (hdeg : ∀ v : V, SourceItems.degree edge v ≤ Δ) :
    Fintype.card V ≤ 2 * Fintype.card E ∧
    2 * Fintype.card E ≤ Δ * Fintype.card V := by
  classical
  have hpos (v : V) : 1 ≤ SourceItems.degree edge v := by
    obtain ⟨e, b, he⟩ := hno v
    unfold SourceItems.degree
    apply Finset.card_pos.mpr
    exact ⟨(e, b), by simp [he]⟩
  have hsum := degree_sum_eq edge
  constructor
  · calc
      Fintype.card V = ∑ _v : V, (1 : ℕ) := by simp
      _ ≤ ∑ v : V, SourceItems.degree edge v :=
        Finset.sum_le_sum (fun v _ => hpos v)
      _ = 2 * Fintype.card E := hsum
  · calc
      2 * Fintype.card E = ∑ v : V, SourceItems.degree edge v := hsum.symm
      _ ≤ ∑ _v : V, Δ := Finset.sum_le_sum (fun v _ => hdeg v)
      _ = Δ * Fintype.card V := by simp [Nat.mul_comm]

theorem copied_edge_vertex_bounds {V E : Type*} [Fintype V] [Fintype E]
    (c Δ : ℕ) (edge : E → Bool → V)
    (hno : ∀ v : V, ∃ e b, edge e b = v)
    (hdeg : ∀ v : V, SourceItems.degree edge v ≤ Δ) :
    Fintype.card (Vertices c V) ≤ 2 * Fintype.card (Edges c E) ∧
    2 * Fintype.card (Edges c E) ≤ Δ * Fintype.card (Vertices c V) := by
  obtain ⟨hlo, hhi⟩ := source_edge_vertex_bounds edge Δ hno hdeg
  rw [copy_card_vertices, copy_card_edges]
  constructor
  · nlinarith [Nat.mul_le_mul_left c hlo]
  · nlinarith [Nat.mul_le_mul_left c hhi]

theorem encoded_edge_vertex_bounds (g : EncodedGraph.Graph) (hg : g.Valid)
    (c Δ : ℕ)
    (hno : ∀ v : Fin g.vertices, ∃ e b,
      CanonicalEdgeTape.graphEdge g hg e b = v)
    (hdeg : ∀ v : Fin g.vertices,
      SourceItems.degree (CanonicalEdgeTape.graphEdge g hg) v ≤ Δ) :
    (encodedCopies g c).vertices ≤ 2 * (encodedCopies g c).edges.length ∧
    2 * (encodedCopies g c).edges.length ≤ Δ * (encodedCopies g c).vertices := by
  obtain ⟨hlo, hhi⟩ :=
    source_edge_vertex_bounds (CanonicalEdgeTape.graphEdge g hg) Δ hno hdeg
  simp only [Fintype.card_fin] at hlo hhi
  rw [encodedCopies_vertices, encodedCopies_edges_length]
  constructor
  · nlinarith [Nat.mul_le_mul_left c hlo]
  · nlinarith [Nat.mul_le_mul_left c hhi]

private theorem shifted_eq_iff (n k j u r : ℕ)
    (hn : 0 < n) (hu : u < n) (hr : r < n) :
    k * n + u = j * n + r ↔ k = j ∧ u = r := by
  constructor
  · intro heq
    have hkj : k = j := by
      rcases lt_trichotomy k j with hlt | heq' | hgt
      · have hm := Nat.mul_le_mul_right n (by omega : k + 1 ≤ j)
        nlinarith
      · exact heq'
      · have hm := Nat.mul_le_mul_right n (by omega : j + 1 ≤ k)
        nlinarith
    subst k
    exact ⟨rfl, by omega⟩
  · rintro ⟨rfl, rfl⟩
    rfl

def incidenceNat (p : ℕ × ℕ) (v : ℕ) : ℕ :=
  (if p.1 = v then 1 else 0) + (if p.2 = v then 1 else 0)

def degreeNat (g : EncodedGraph.Graph) (v : ℕ) : ℕ :=
  (g.edges.map fun p => incidenceNat p v).sum

private theorem sum_flatMap_nat {A : Type*} (xs : List A) (f : A → List ℕ) :
    (xs.flatMap f).sum = (xs.map fun x => (f x).sum).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [List.flatMap, Function.comp_def] using (congrArg (fun z => (f x).sum + z) ih)

private theorem sum_range_ite (c : ℕ) (j : Fin c) (d : ℕ) :
    ((List.range c).map fun k => if k = j.val then d else 0).sum = d := by
  induction c with
  | zero => exact Fin.elim0 j
  | succ c ih =>
    rw [List.sum_range_succ]
    by_cases hj : j.val = c
    · have hzero :
          ((List.range c).map fun k => if k = j.val then d else 0).sum = 0 := by
        have hm : (List.range c).map (fun k => if k = j.val then d else 0) =
            (List.range c).map (fun _ => (0 : ℕ)) := by
          apply List.map_congr_left
          intro k hk
          simp [ne_of_lt (by have := List.mem_range.mp hk; omega : k < j.val)]
        rw [hm]
        simp
      rw [hj] at hzero ⊢
      simpa [hzero]
    · have hjc : j.val < c := by omega
      have heq := ih ⟨j.val, hjc⟩
      have hcj : c ≠ j.val := Ne.symm hj
      simpa [hcj] using heq

theorem encoded_degree_copy (g : EncodedGraph.Graph) (hg : g.Valid)
    (c : ℕ) (j : Fin c) (r : Fin g.vertices) :
    degreeNat (encodedCopies g c) (j.val * g.vertices + r.val) =
      degreeNat g r.val := by
  let target := j.val * g.vertices + r.val
  have hshift (k : ℕ) (p : ℕ × ℕ) (hp : p ∈ g.edges) :
      incidenceNat (k * g.vertices + p.1, k * g.vertices + p.2) target =
      if k = j.val then incidenceNat p r.val else 0 := by
    obtain ⟨hu, hv, _⟩ := hg p hp
    simp [incidenceNat, target, shifted_eq_iff g.vertices k j.val p.1 r.val
      (by omega) hu r.isLt,
      shifted_eq_iff g.vertices k j.val p.2 r.val (by omega) hv r.isLt]
    split_ifs <;> simp_all
  have hinner (k : ℕ) :
      (g.edges.map fun p =>
        incidenceNat (k * g.vertices + p.1, k * g.vertices + p.2) target).sum =
        if k = j.val then degreeNat g r.val else 0 := by
    calc
      _ = (g.edges.map fun p =>
          if k = j.val then incidenceNat p r.val else 0).sum := by
        congr 1
        apply List.map_congr_left
        intro p hp
        exact hshift k p hp
      _ = if k = j.val then degreeNat g r.val else 0 := by
        split_ifs <;> simp [degreeNat]
  simp only [degreeNat, encodedCopies, List.map_flatMap, sum_flatMap_nat]
  simp only [List.map_map, Function.comp_def]
  calc
    _ = ((List.range c).map fun k =>
        if k = j.val then degreeNat g r.val else 0).sum := by
          congr 1
          apply List.map_congr_left
          intro k hk
          exact hinner k
    _ = degreeNat g r.val := sum_range_ite c j _

theorem encoded_degree_bound (g : EncodedGraph.Graph) (hg : g.Valid)
    (c Δ : ℕ) (hn : 0 < g.vertices)
    (hdeg : ∀ v < g.vertices, degreeNat g v ≤ Δ) :
    ∀ v < (encodedCopies g c).vertices,
      degreeNat (encodedCopies g c) v ≤ Δ := by
  intro v hv
  let j : Fin c := ⟨v / g.vertices,
    (Nat.div_lt_iff_lt_mul hn).2 (by simpa [encodedCopies, Nat.mul_comm] using hv)⟩
  let r : Fin g.vertices := ⟨v % g.vertices, Nat.mod_lt _ hn⟩
  have hident : v = j.val * g.vertices + r.val := by
    simpa only [j, r, Nat.mul_comm, Nat.add_comm] using
      (Nat.mod_add_div v g.vertices).symm
  rw [hident, encoded_degree_copy g hg c j r]
  exact hdeg r.val r.isLt

theorem degreeNat_eq_source (g : EncodedGraph.Graph) (hg : g.Valid)
    (v : Fin g.vertices) :
    degreeNat g v.val =
      SourceItems.degree (CanonicalEdgeTape.graphEdge g hg) v := by
  classical
  have hlist : g.edges = List.ofFn g.edges.get := (List.ofFn_get g.edges).symm
  unfold degreeNat SourceItems.degree
  conv_lhs => rw [hlist]
  rw [List.map_ofFn, List.sum_ofFn]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro e he
  have hb : (Finset.univ : Finset Bool) = {false, true} := by decide
  simp [hb, incidenceNat, CanonicalEdgeTape.graphEdge, EncodedGraph.endpoints,
    Finset.filter_insert, Finset.filter_singleton, List.get_eq_getElem, Fin.ext_iff]
  split_ifs <;> simp_all

private theorem filter_length_eq_indicator_sum {A : Type*}
    (xs : List A) (p : A → Bool) :
    (xs.filter p).length = (xs.map fun x => if p x then 1 else 0).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hp : p x <;> simp [List.filter, hp, ih, Nat.add_comm]

theorem monoCountNat_eq_source (g : EncodedGraph.Graph) (hg : g.Valid)
    (colour : ℕ → Fin 3) :
    monoCountNat g colour =
      (Finset.univ.filter (fun e : Fin g.edges.length =>
        colour (CanonicalEdgeTape.graphEdge g hg e false).val =
          colour (CanonicalEdgeTape.graphEdge g hg e true).val)).card := by
  classical
  unfold monoCountNat
  rw [filter_length_eq_indicator_sum]
  have hlist : g.edges = List.ofFn g.edges.get := (List.ofFn_get g.edges).symm
  conv_lhs => rw [hlist]
  rw [List.map_ofFn, List.sum_ofFn]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e he
  simp [CanonicalEdgeTape.graphEdge_false, CanonicalEdgeTape.graphEdge_true]

theorem gapFin_to_gapNat (g : EncodedGraph.Graph) (hg : g.Valid)
    (γ : ℚ)
    (hgap : ∀ colour : Fin g.vertices → Fin 3,
      γ * (g.edges.length : ℚ) ≤
        ((Finset.univ.filter (fun e : Fin g.edges.length =>
          colour (CanonicalEdgeTape.graphEdge g hg e false) =
            colour (CanonicalEdgeTape.graphEdge g hg e true))).card : ℚ)) :
    ∀ colour : ℕ → Fin 3,
      γ * (g.edges.length : ℚ) ≤ monoCountNat g colour := by
  intro colour
  rw [monoCountNat_eq_source g hg colour]
  exact hgap (fun v => colour v.val)

theorem noIsolatesNat_to_source (g : EncodedGraph.Graph) (hg : g.Valid)
    (hno : NoIsolatesNat g) :
    ∀ v : Fin g.vertices, ∃ e b,
      CanonicalEdgeTape.graphEdge g hg e b = v := by
  intro v
  obtain ⟨p, hp, hside⟩ := hno v.val v.isLt
  obtain ⟨e, he⟩ := List.get_of_mem hp
  rcases hside with hleft | hright
  · refine ⟨e, false, Fin.ext ?_⟩
    have hp1 : (g.edges.get e).1 = v.val := by rw [he]; exact hleft.symm
    exact (CanonicalEdgeTape.graphEdge_false g hg e).trans hp1
  · refine ⟨e, true, Fin.ext ?_⟩
    have hp2 : (g.edges.get e).2 = v.val := by rw [he]; exact hright.symm
    exact (CanonicalEdgeTape.graphEdge_true g hg e).trans hp2

theorem encoded_source_promise (g : EncodedGraph.Graph) (hg : g.Valid)
    (N Δ : ℕ) (γ : ℚ) (hn : 0 < g.vertices)
    (hm : 0 < g.edges.length)
    (hno : NoIsolatesNat g)
    (hdeg : ∀ v < g.vertices, degreeNat g v ≤ Δ)
    (hgap : ∀ colour : ℕ → Fin 3,
      γ * (g.edges.length : ℚ) ≤ monoCountNat g colour) :
    let G := encodedCopies g (copies N g.edges.length)
    G.Valid ∧ N ≤ G.edges.length ∧ G.edges.length ≤ N + g.edges.length ∧
    G.vertices ≤ 2 * G.edges.length ∧
    2 * G.edges.length ≤ Δ * G.vertices ∧
    NoIsolatesNat G ∧
    (∀ v < G.vertices, degreeNat G v ≤ Δ) ∧
    (ProperNat G ↔ ProperNat g) ∧
    (∀ colour : ℕ → Fin 3,
      γ * (G.edges.length : ℚ) ≤ monoCountNat G colour) := by
  dsimp
  have hdegreeSource : ∀ v : Fin g.vertices,
      SourceItems.degree (CanonicalEdgeTape.graphEdge g hg) v ≤ Δ := by
    intro v
    rw [← degreeNat_eq_source g hg v]
    exact hdeg v.val v.isLt
  have hnumeric := encoded_edge_vertex_bounds g hg (copies N g.edges.length) Δ
    (noIsolatesNat_to_source g hg hno) hdegreeSource
  have hcount := encoded_edge_bounds g N hm
  exact ⟨encodedCopies_valid g hg _, hcount.1, hcount.2, hnumeric.1,
    hnumeric.2, encoded_no_isolates g _ hn hno,
    encoded_degree_bound g hg _ Δ hn hdeg,
    encoded_proper_iff g hg _ (copies_pos N _),
    encodedCopies_gap g _ γ hgap⟩

theorem encoded_ratio (g : EncodedGraph.Graph) (c : ℕ)
    (hc : 0 < c) (hn : 0 < g.vertices) :
    ((encodedCopies g c).edges.length : ℚ) /
        (encodedCopies g c).vertices =
      (g.edges.length : ℚ) / g.vertices := by
  rw [encodedCopies_edges_length, encodedCopies_vertices]
  push_cast
  field_simp

theorem encoded_delta_v (g : EncodedGraph.Graph) (c Δ : ℕ) (γ : ℚ)
    (hc : 0 < c) (hn : 0 < g.vertices) (hΔ : 0 < Δ) :
    γ * ((encodedCopies g c).edges.length : ℚ) /
        (2 * (Δ : ℚ) * (encodedCopies g c).vertices) =
      γ * (g.edges.length : ℚ) / (2 * (Δ : ℚ) * g.vertices) := by
  rw [encodedCopies_edges_length, encodedCopies_vertices]
  push_cast
  field_simp

/-- A byte-size consequence of the actual `EncodedGraph.encode` constructor.
This is not a fixed-machine running-time or tape bound. -/
theorem encoded_output_length (g : EncodedGraph.Graph) (hg : g.Valid)
    (c : ℕ) :
    (EncodedGraph.encode (encodedCopies g c)).length ≤
      c * g.vertices + 2 +
        (c * g.edges.length) * (4 * (c * g.vertices) + 4) := by
  simpa only [encodedCopies_vertices, encodedCopies_edges_length] using
    EncodedGraph.encode_length_upper (encodedCopies g c) (encodedCopies_valid g hg c)

#print axioms copy_edge_bounds
#print axioms encoded_edge_bounds
#print axioms encoded_vertex_bound
#print axioms encoded_proper_iff
#print axioms encoded_no_isolates
#print axioms copied_degree
#print axioms copied_gap
#print axioms degree_sum_eq
#print axioms source_edge_vertex_bounds
#print axioms copied_edge_vertex_bounds
#print axioms encoded_edge_vertex_bounds
#print axioms encoded_degree_copy
#print axioms encoded_degree_bound
#print axioms degreeNat_eq_source
#print axioms monoCountNat_eq_source
#print axioms gapFin_to_gapNat
#print axioms noIsolatesNat_to_source
#print axioms encoded_source_promise
#print axioms encoded_ratio
#print axioms encoded_delta_v
#print axioms encoded_output_length

end Paper2.CurrentAdditive.V38SourcePaddingFinal
