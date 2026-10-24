import Paper2.CanonicalEdgeTape
import Paper2.FiniteFallbackOutput
import Paper2.SourceItems
import EthInapproximability.CurrentPaper.EncodedETHSource
import Paper2.A4BOTOutput

/-!
# Unit 4 (Paper A), segment A4-S2: graph-type bridges

Owner lane `owner:a-unit4-shell` (private, 25 September 2026).

Pure finite identities between Paper B's typed view of a valid encoded graph
(`EncodedETHSource.rawGraph g hg`) and Paper A's Fin-indexed endpoint map
(`CanonicalEdgeTape.graphEdge g hg`) consumed by `TotalFiniteConstructor.select`,
`EncodedSelectedOutput.every_yes_output_language` and
`EncodedSelectedOutput.positive_gap_noLanguageProbability`.

**None of these statements closes a ledger row.** They are finite bridges only;
they do not state or charge any machine, and do not decide X03/X04/D-A7.
-/

namespace Paper2.Unit4Shell.GraphBridges

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.SourceNormalization
open EthInapproximability.CurrentPaper.SourceCNFSemantics

section Graph

variable (g : EncodedGraph.Graph) (hg : g.Valid)

/-- Endpoint identity: Paper A's Boolean endpoint orientation is Paper B's
`Fin 2` orientation (`false ↦ 0`, `true ↦ 1`). Does not close a ledger row. -/
theorem graphEdge_eq_bd (e : Fin g.edges.length) (b : Bool) :
    CanonicalEdgeTape.graphEdge g hg e b =
      (EncodedETHSource.rawGraph g hg).bd e (if b then 1 else 0) := by
  rw [EncodedETHSource.rawGraph_bd]
  rfl

/-- Degree bridge (labelled incidences with multiplicity on both sides).
Does not close a ledger row. -/
theorem degree_eq (v : Fin g.vertices) :
    (EncodedETHSource.rawGraph g hg).degree v =
      SourceItems.degree (CanonicalEdgeTape.graphEdge g hg) v := by
  classical
  unfold RawGraph.degree SourceItems.degree
  refine Finset.card_bij' (fun p _ => (p.1, decide (p.2 = 1)))
    (fun q _ => (q.1, if q.2 then 1 else 0)) ?_ ?_ ?_ ?_
  · rintro ⟨e, b⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    rw [graphEdge_eq_bd]
    fin_cases b <;> simpa using hp
  · rintro ⟨e, b⟩ hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    rw [graphEdge_eq_bd] at hq
    exact hq
  · rintro ⟨e, b⟩ _
    fin_cases b <;> rfl
  · rintro ⟨e, b⟩ _
    cases b <;> rfl

/-- Colourability bridge. Does not close a ledger row. -/
theorem colourable_iff :
    (EncodedETHSource.rawGraph g hg).Colourable ↔
      FiniteFallbackOutput.ThreeColourable (CanonicalEdgeTape.graphEdge g hg) := by
  constructor
  · rintro ⟨χ, hχ⟩
    exact ⟨χ, fun z => hχ z⟩
  · rintro ⟨χ, hχ⟩
    exact ⟨χ, fun z => hχ z⟩

/-- Monochromatic-edge count bridge. Does not close a ledger row. -/
theorem mono_card (χ : Fin g.vertices → Fin 3) :
    ((EncodedETHSource.rawGraph g hg).monoFinset χ).card =
      (Finset.univ.filter (fun e => χ (CanonicalEdgeTape.graphEdge g hg e false) =
        χ (CanonicalEdgeTape.graphEdge g hg e true))).card := by
  rfl

/-- Gap bridge from Paper B's rational `Gap γ` to the real-valued gap premise of
`EncodedSelectedOutput.positive_gap_noLanguageProbability`.
Does not close a ledger row. -/
theorem gap_real {γ : ℚ} (h : (EncodedETHSource.rawGraph g hg).Gap γ)
    (colour : Fin g.vertices → Fin 3) :
    (γ : ℝ) * g.edges.length ≤
      ((Finset.univ.filter (fun e => colour (CanonicalEdgeTape.graphEdge g hg e false) =
        colour (CanonicalEdgeTape.graphEdge g hg e true))).card : ℝ) := by
  have hc := h colour
  rw [mono_card] at hc
  simp only [Fintype.card_fin] at hc
  exact_mod_cast hc

/-- Looplessness from validity of the encoded graph. Does not close a ledger row. -/
theorem loopless (e : Fin g.edges.length) :
    CanonicalEdgeTape.graphEdge g hg e false ≠ CanonicalEdgeTape.graphEdge g hg e true := by
  intro h
  exact (EncodedETHSource.rawGraph g hg).loopless e h

/-- Incidence from positive degree. Does not close a ledger row. -/
theorem incident_of_degree_pos (v : Fin g.vertices)
    (h : 1 ≤ (EncodedETHSource.rawGraph g hg).degree v) :
    ∃ e b, CanonicalEdgeTape.graphEdge g hg e b = v := by
  rw [degree_eq] at h
  unfold SourceItems.degree at h
  obtain ⟨⟨e, b⟩, hp⟩ := Finset.card_pos.mp h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
  exact ⟨e, b, hp⟩

/-- A valid graph with an edge has a vertex. Does not close a ledger row. -/
theorem vertices_pos_of_edges_pos (g : EncodedGraph.Graph) (hg : g.Valid)
    (he : 0 < g.edges.length) : 0 < g.vertices := by
  have h := (hg _ (List.get_mem g.edges ⟨0, he⟩)).1
  omega

end Graph

section BOT

variable {k : ℕ} (B : EncodedETHSource.BOTReduction k)

/-- The normalized BOT output always has an edge (the adjoined `K₂` copies).
Does not close a ledger row. -/
theorem output_edges_pos (f : EncodedCNF.Formula) (hf : f.Valid) (n : ℕ) :
    0 < (B.output f hf n).edges.length :=
  BOTOutput.output_edges_pos B f hf n

/-- The normalized BOT output always has a vertex. Does not close a ledger row. -/
theorem output_vertices_pos (f : EncodedCNF.Formula) (hf : f.Valid) (n : ℕ) :
    0 < (B.output f hf n).vertices :=
  vertices_pos_of_edges_pos _ (B.output_valid f hf n) (output_edges_pos B f hf n)

/-- The H-A3 structural premises (incidence, degree bound, looplessness) for
the actual normalized BOT output graph, with Paper A's endpoint map.
Does not close a ledger row. -/
theorem output_structural (f : EncodedCNF.Formula) (hf : f.Valid)
    (hk : BoundedOccurrence f k) (n : ℕ) :
    (∀ v, ∃ e b, CanonicalEdgeTape.graphEdge (B.output f hf n) (B.output_valid f hf n) e b = v) ∧
    (∀ v, SourceItems.degree
      (CanonicalEdgeTape.graphEdge (B.output f hf n) (B.output_valid f hf n)) v ≤ B.degreeBound) ∧
    (∀ e, CanonicalEdgeTape.graphEdge (B.output f hf n) (B.output_valid f hf n) e false ≠
      CanonicalEdgeTape.graphEdge (B.output f hf n) (B.output_valid f hf n) e true) := by
  refine ⟨fun v => ?_, fun v => ?_, fun e => loopless _ _ e⟩
  · exact incident_of_degree_pos _ _ v (B.output_degree f hf hk n v).1
  · rw [← degree_eq]
    exact (B.output_degree f hf hk n v).2

/-- YES transfer for the actual normalized BOT output graph.
Does not close a ledger row. -/
theorem output_yes (f : EncodedCNF.Formula) (hf : f.Valid)
    (hk : BoundedOccurrence f k) (n : ℕ) (hyes : EncodedCNF.Satisfiable f) :
    FiniteFallbackOutput.ThreeColourable
      (CanonicalEdgeTape.graphEdge (B.output f hf n) (B.output_valid f hf n)) :=
  (colourable_iff (B.output f hf n) (B.output_valid f hf n)).mp
    (BOTOutput.output_colourable B f hf hk n hyes)

/-- NO transfer (gap, real form) for the actual normalized BOT output graph.
Does not close a ledger row. -/
theorem output_no (f : EncodedCNF.Formula) (hf : f.Valid)
    (hk : BoundedOccurrence f k)
    {V : ℕ} (hV : 0 < V) (hused : f.variables ≤ V * f.clauses.length)
    (hm : 0 < f.clauses.length)
    (n : ℕ) {ρ : ℚ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hgap : FormulaGap f ρ)
    (colour : Fin (B.output f hf n).vertices → Fin 3) :
    ((B.gapFraction V ρ / 2 : ℚ) : ℝ) * (B.output f hf n).edges.length ≤
      ((Finset.univ.filter (fun e =>
        colour (CanonicalEdgeTape.graphEdge (B.output f hf n) (B.output_valid f hf n) e false) =
        colour (CanonicalEdgeTape.graphEdge (B.output f hf n) (B.output_valid f hf n) e true))).card
        : ℝ) :=
  gap_real (B.output f hf n) (B.output_valid f hf n)
    (BOTOutput.output_gap B f hf hk hV hused hm n hρ hρ1 hgap) colour

end BOT

end Paper2.Unit4Shell.GraphBridges
