import EthInapproximability.CurrentPaper.EncodedETHSource

/-!
# Unit 4 (Paper A), segment A4-S2 support: BOT output facts in Paper B's typing

Owner lane `owner:a-unit4-shell` (private, 25 September 2026).

This module imports only `EncodedETHSource`, so the instance environment is the
one in which `BOTReduction.normalized` was elaborated (importing Paper2 modules
adds `Fintype` instances that are not definitionally reducible to the ones
baked into `normalized`'s type). Pure finite corollaries of admitted Paper B
lemmas. **None of these statements closes a ledger row.**
-/

namespace Paper2.Unit4Shell.BOTOutput

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.SourceNormalization
open EthInapproximability.CurrentPaper.SourceCNFSemantics
open EthInapproximability.CurrentPaper.EncodedETHSource

open EthInapproximability.ParameterizedNP.GuardedSourceGraph

/-! Generic serialized-graph facts. The instance arguments are ordinary implicit
binders, so they are fixed by unification with the graph's own type rather than
re-synthesized in this module's environment. -/

theorem serialize_edges_pos {V E : Type*} {iV : Fintype V} {dV : DecidableEq V}
    {iE : Fintype E} {dE : DecidableEq E} (G : EndpointGraph V E) :
    0 < (serializeGraph G).edges.length := by
  obtain ⟨e⟩ := G.edgeNonempty
  exact Fin.pos ((serializedEdgeEquiv G).symm e)

theorem serialize_colourable {V E : Type*} {iV : Fintype V} {dV : DecidableEq V}
    {iE : Fintype E} {dE : DecidableEq E} (G : EndpointGraph V E) (h : G.SourceYES) :
    (rawGraph (serializeGraph G) (serializeGraph_valid G)).Colourable :=
  (serialized_colourable_iff G).mpr h

theorem serialize_gap {V E : Type*} {iV : Fintype V} {dV : DecidableEq V}
    {iE : Fintype E} {dE : DecidableEq E} (G : EndpointGraph V E) {γ : ℚ}
    (h : G.SourceNO γ) :
    (rawGraph (serializeGraph G) (serializeGraph_valid G)).Gap γ :=
  serialized_gap G h

variable {k : ℕ} (B : BOTReduction k)

/-- The normalized BOT output always has an edge (it contains the adjoined `K₂`
copies), for every `n` including `n = 0`. Does not close a ledger row. -/
theorem output_edges_pos (f : EncodedCNF.Formula) (hf : f.Valid) (n : ℕ) :
    0 < (B.output f hf n).edges.length :=
  serialize_edges_pos (B.normalized f hf n)

/-- YES transfer to the serialized output graph. Does not close a ledger row. -/
theorem output_colourable (f : EncodedCNF.Formula) (hf : f.Valid)
    (hk : BoundedOccurrence f k) (n : ℕ) (hyes : EncodedCNF.Satisfiable f) :
    (rawGraph (B.output f hf n) (B.output_valid f hf n)).Colourable :=
  serialize_colourable (B.normalized f hf n) (B.normalized_yes f hf hk n hyes)

/-- NO transfer to the serialized output graph. Does not close a ledger row. -/
theorem output_gap (f : EncodedCNF.Formula) (hf : f.Valid)
    (hk : BoundedOccurrence f k)
    {V : ℕ} (hV : 0 < V) (hused : f.variables ≤ V * f.clauses.length)
    (hm : 0 < f.clauses.length)
    (n : ℕ) {ρ : ℚ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hgap : FormulaGap f ρ) :
    (rawGraph (B.output f hf n) (B.output_valid f hf n)).Gap (B.gapFraction V ρ / 2) :=
  serialize_gap (B.normalized f hf n) (B.normalized_no f hf hk hV hused hm n hρ hρ1 hgap)

end Paper2.Unit4Shell.BOTOutput
