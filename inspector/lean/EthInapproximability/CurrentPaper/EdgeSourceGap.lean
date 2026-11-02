import EthInapproximability.ParameterizedNP.GuardedSourceGraph

/-!
# The one-copy gap for the current edge-only source

Source: v8 `A-stage4-details.tex`, proof of `thm:paper-guarded-source`,
the one-copy paragraph at lines 99--112. Coordinates are edge occurrences
only, not the old edge-plus-incidence carrier. The graph promises, finite
packing vocabulary, free-bin count and incidence-count identity are generic
reused definitions/lemmas. The obsolete `source_one_copy` theorem is not used.

The conclusion is a concrete overload count from the graph's colouring-far
promise and the permitted vertex deletions. No overload or communication
lower bound is supplied as a hypothesis. Multi-copy witness extraction and
the production of the promised graph are separate obligations.
-/

namespace EthInapproximability.CurrentPaper.EdgeSourceGap

open EthInapproximability.ParameterizedNP.GuardedSourceGraph

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The literal edge-only local evaluator: both endpoints and every auxiliary
item are active at an edge occurrence. -/
def edgeRow (G : EndpointGraph V E) (s : ℕ) : Row V s → E → Bool :=
  fun i e => G.unslabbedRow s i (Sum.inl e)

@[simp] theorem edgeRow_vertex (G : EndpointGraph V E) (s : ℕ) (u : V) (e : E) :
    edgeRow G s (Sum.inl u) e = decide (u = G.bd₀ e ∨ u = G.bd₁ e) := rfl

@[simp] theorem edgeRow_auxiliary (G : EndpointGraph V E) (s : ℕ)
    (k : Fin (s - 3)) (e : E) : edgeRow G s (Sum.inr k) e = true := rfl

/-- Edge occurrences meeting a deleted vertex cost at most the degree bound
times the number of deleted vertices. Parallel occurrences remain distinct. -/
theorem touched_edges_card_le (G : EndpointGraph V E) {Δ : ℕ}
    (hdeg : ∀ u : V, G.degree u ≤ Δ) (Del : Finset V) :
    (Finset.univ.filter fun e : E => ∃ b : Fin 2, G.bd e b ∈ Del).card
      ≤ Δ * Del.card := by
  classical
  have hsubset : (Finset.univ.filter fun e : E => ∃ b : Fin 2, G.bd e b ∈ Del)
      ⊆ (Finset.univ.filter fun p : Inc E => G.vert p ∈ Del).image Prod.fst := by
    intro e he
    obtain ⟨b, hb⟩ := (Finset.mem_filter.mp he).2
    exact Finset.mem_image.mpr ⟨(e, b), by simpa using hb, rfl⟩
  calc
    _ ≤ ((Finset.univ.filter fun p : Inc E => G.vert p ∈ Del).image Prod.fst).card :=
      Finset.card_le_card hsubset
    _ ≤ (Finset.univ.filter fun p : Inc E => G.vert p ∈ Del).card := Finset.card_image_le
    _ = ∑ u ∈ Del, G.degree u := G.card_inc_mem Del
    _ ≤ ∑ _u ∈ Del, Δ := Finset.sum_le_sum fun u _ => hdeg u
    _ = Δ * Del.card := by simp [Nat.mul_comm]

/-- With all auxiliary items retained, the permitted deletion of vertices
leaves at least `γ |E| / 2` overloaded EDGE coordinates in every assignment.
This is the current paper's edge-only one-copy argument. -/
theorem source_one_copy (G : EndpointGraph V E) {s : ℕ} (hs : 4 ≤ s)
    {Δ : ℕ} (hΔ : 0 < Δ) {γ : ℚ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hno : G.SourceNO γ) (hdeg : ∀ u : V, G.degree u ≤ Δ)
    (J : Finset (Row V s))
    (hblk : ∀ k : Fin (s - 3), (Sum.inr k : Row V s) ∈ J)
    (hdel : ((Finset.univ.filter fun u : V => (Sum.inl u : Row V s) ∉ J).card : ℚ)
      ≤ G.deltaV γ Δ * (Fintype.card V : ℚ))
    (φ : Row V s → Fin s) :
    γ * (Fintype.card E : ℚ) / 2 ≤ ((Over (edgeRow G s) J φ).card : ℚ) := by
  classical
  have hΔq : (0 : ℚ) < Δ := by exact_mod_cast hΔ
  have hmq : (0 : ℚ) < Fintype.card E := by exact_mod_cast G.card_edge_pos
  let Del : Finset V := Finset.univ.filter fun u : V => (Sum.inl u : Row V s) ∉ J
  have hdelbound : (Δ : ℚ) * (Del.card : ℚ) ≤ γ * (Fintype.card E : ℚ) / 2 := by
    rw [G.deltaV_mul_card γ hΔ] at hdel
    have h := mul_le_mul_of_nonneg_left hdel (le_of_lt hΔq)
    calc
      (Δ : ℚ) * (Del.card : ℚ) ≤ Δ * (γ * (Fintype.card E : ℚ) / (2 * Δ)) := h
      _ = γ * (Fintype.card E : ℚ) / 2 := by field_simp
  by_cases hcase : ∃ k k' : Fin (s - 3), k ≠ k' ∧ φ (Sum.inr k) = φ (Sum.inr k')
  · obtain ⟨k, k', hne, heq⟩ := hcase
    have hall : Over (edgeRow G s) J φ = (Finset.univ : Finset E) := by
      ext e
      simp only [Finset.mem_univ, iff_true]
      exact mem_Over_of_two (edgeRow G s) J φ e
        (i := Sum.inr k) (j := Sum.inr k')
        (by simpa using hne) (hblk k) (hblk k') heq (by simp) (by simp)
    rw [hall, Finset.card_univ]
    nlinarith
  · have hblkinj : Function.Injective fun k : Fin (s - 3) => φ (Sum.inr k) := by
      intro k k' h
      by_contra hne
      exact hcase ⟨k, k', hne, h⟩
    have hC : (freeBins (V := V) φ).card = 3 := freeBins_card (by omega) hblkinj
    let iso := (freeBins (V := V) φ).orderIsoOfFin hC
    let χ : V → Fin 3 := fun u =>
      if h : φ (Sum.inl u) ∈ freeBins (V := V) φ then iso.symm ⟨_, h⟩ else 0
    let Bad : Finset E := Finset.univ.filter fun e => ∃ b : Fin 2, G.bd e b ∈ Del
    let Good : Finset E := (G.monoFinset χ) \ Bad
    have hbad : Bad.card ≤ Δ * Del.card := touched_edges_card_le G hdeg Del
    have hgood : Good ⊆ Over (edgeRow G s) J φ := by
      intro e he
      obtain ⟨hmono, hnotbad⟩ := Finset.mem_sdiff.mp he
      have hsurv : ∀ b : Fin 2, (Sum.inl (G.bd e b) : Row V s) ∈ J := by
        intro b
        by_contra hb
        apply hnotbad
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, b,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩⟩
      by_cases hf0 : φ (Sum.inl (G.bd e 0)) ∈ freeBins (V := V) φ
      · by_cases hf1 : φ (Sum.inl (G.bd e 1)) ∈ freeBins (V := V) φ
        · have hc := (EndpointGraph.mem_monoFinset G χ e).mp hmono
          have hχ0 : χ (G.bd e 0) = iso.symm ⟨φ (Sum.inl (G.bd e 0)), hf0⟩ := by
            simp only [χ, dif_pos hf0]
          have hχ1 : χ (G.bd e 1) = iso.symm ⟨φ (Sum.inl (G.bd e 1)), hf1⟩ := by
            simp only [χ, dif_pos hf1]
          have hsub : (⟨φ (Sum.inl (G.bd e 0)), hf0⟩ : {x // x ∈ freeBins (V := V) φ})
              = ⟨φ (Sum.inl (G.bd e 1)), hf1⟩ :=
            iso.symm.injective (by rw [← hχ0, ← hχ1]; exact hc)
          have hbins : φ (Sum.inl (G.bd₀ e)) = φ (Sum.inl (G.bd₁ e)) := by
            simpa using congrArg Subtype.val hsub
          exact mem_Over_of_two (edgeRow G s) J φ e
            (i := Sum.inl (G.bd₀ e)) (j := Sum.inl (G.bd₁ e))
            (by simpa using G.loopless e) (by simpa using hsurv 0)
            (by simpa using hsurv 1) hbins (by simp) (by simp)
        · obtain ⟨k, hk⟩ := exists_blocker_of_notMem_freeBins hf1
          exact mem_Over_of_two (edgeRow G s) J φ e
            (i := Sum.inl (G.bd₁ e)) (j := Sum.inr k)
            (by simp) (by simpa using hsurv 1) (hblk k) (by simpa using hk.symm)
            (by simp) (by simp)
      · obtain ⟨k, hk⟩ := exists_blocker_of_notMem_freeBins hf0
        exact mem_Over_of_two (edgeRow G s) J φ e
          (i := Sum.inl (G.bd₀ e)) (j := Sum.inr k)
          (by simp) (by simpa using hsurv 0) (hblk k) (by simpa using hk.symm)
          (by simp) (by simp)
    have hcover : G.monoFinset χ ⊆ Good ∪ Bad := by
      intro e he
      by_cases hb : e ∈ Bad
      · exact Finset.mem_union_right _ hb
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨he, hb⟩)
    have hcount : (G.monoFinset χ).card ≤ (Over (edgeRow G s) J φ).card + Δ * Del.card :=
      calc
        _ ≤ (Good ∪ Bad).card := Finset.card_le_card hcover
        _ ≤ Good.card + Bad.card := Finset.card_union_le _ _
        _ ≤ (Over (edgeRow G s) J φ).card + Δ * Del.card :=
          Nat.add_le_add (Finset.card_le_card hgood) hbad
    have hcountq : ((G.monoFinset χ).card : ℚ) ≤
        ((Over (edgeRow G s) J φ).card : ℚ) + Δ * (Del.card : ℚ) := by
      exact_mod_cast hcount
    have hnoχ := hno χ
    linarith

/-- A nonvacuous instance on the complete graph on four vertices: every
four-bin assignment overloads at least one of the six EDGE coordinates.
Thus the full hypothesis bundle of `source_one_copy` is satisfiable. -/
theorem complete_four_regression (φ : Row (Fin 4) 4 → Fin 4) :
    1 ≤ (Over (edgeRow K4 4) (Finset.univ : Finset (Row (Fin 4) 4)) φ).card := by
  have hdel : ((Finset.univ.filter fun u : Fin 4 =>
        (Sum.inl u : Row (Fin 4) 4) ∉ (Finset.univ : Finset (Row (Fin 4) 4))).card : ℚ)
      ≤ K4.deltaV (1 / 6) 3 * (Fintype.card (Fin 4) : ℚ) := by
    norm_num [EndpointGraph.deltaV]
  have h := source_one_copy K4 (s := 4) (by norm_num) (Δ := 3) (by norm_num)
    (γ := 1 / 6) (by norm_num) (by norm_num) k4_sourceNO
    (fun u => le_of_eq (k4_degree u)) Finset.univ (fun _ => Finset.mem_univ _) hdel φ
  have hpos : (0 : ℚ) <
      ((Over (edgeRow K4 4) (Finset.univ : Finset (Row (Fin 4) 4)) φ).card : ℚ) := by
    norm_num only [Fintype.card_fin] at h
    linarith
  exact Nat.succ_le_of_lt (by exact_mod_cast hpos)

end EthInapproximability.CurrentPaper.EdgeSourceGap
