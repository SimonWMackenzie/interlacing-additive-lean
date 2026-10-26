import EthInapproximability.CurrentPaper.EntryClockPolyPieces

/-!
# Segment 2 (graph-dependent piece): `EntryPrepVec.boundV` is uniformly polynomial

Lane owner:b-entry-clock-2 (Paper B, unit 2, CP-EFFECTIVE). Pure arithmetic about the
admitted clocks; no machine.

`boundV G n c` (owner-7's vectors phase clock, production since WAVE12_B22) depends on the
graph through the admitted `VectorsFromGraphQ.fullBound`, the workspace allowance
`EntryPrepVec.lenB` and the literal encoded graph bytes. Over the type `GI` of
(graph, bins) pairs:

* `lenB_le`: every workspace allowance is at most `BzG + BQG` (explicit polynomial atoms);
* `boundV_le`: `boundV G n c ≤ bvG ⟨V, E, G, sv G n c⟩`;
* `bvG_poly`: `bvG` is `PolyIn` the size `UG = s + |enc G| + q2 + |endpointStream|`
  (ONE pair of absolute constants), reusing the admitted `QPublicGrowth.arithmetic_cost_le`;
* `stream_le`: `|endpointStream| ≤ |enc G| * (2 |enc G| + 2)`.
-/

namespace EthInapproximability.CurrentPaper.EntryClockPoly

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open EthInapproximability.ParameterizedNP.GuardedSourceSlab

/-- A graph with a bin count. -/
structure GI where
  V : Type
  E : Type
  [iV : Fintype V]
  [dV : DecidableEq V]
  [iE : Fintype E]
  [dE : DecidableEq E]
  G : EndpointGraph V E
  s : ℕ

attribute [instance] GI.iV GI.dV GI.iE GI.dE

/-- The literal encoded graph length `|enc G|`. -/
def ellG {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EndpointGraph V E) : ℕ :=
  (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length

/-- The endpoint stream length. -/
def strG {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EndpointGraph V E) : ℕ :=
  (SourceGraphPayloadMachine.endpointStream (EncodedETHSource.serializeGraph G).edges).length

def UG (g : GI) : ℕ := g.s + ellG g.G + q2 g.G g.s + strG g.G

theorem card_le_ell {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EndpointGraph V E) : Fintype.card V + 2 * Fintype.card E + 2 ≤ ellG G := by
  have h := EncodedGraph.encode_length_lower (EncodedETHSource.serializeGraph G)
  simp only [EncodedETHSource.serializeGraph_vertices, EncodedETHSource.serializeGraph_edges] at h
  exact h

theorem stream_aux (N : ℕ) : ∀ (es : List (ℕ × ℕ)), (∀ p ∈ es, p.1 < N ∧ p.2 < N) →
    (SourceGraphPayloadMachine.endpointStream es).length ≤ es.length * (2 * N + 2) := by
  intro es
  induction es with
  | nil => intro _; simp [SourceGraphPayloadMachine.endpointStream]
  | cons p ps ih =>
    intro h
    have hp := h p (by simp)
    have hi := ih (fun q hq => h q (by simp [hq]))
    have e : (SourceGraphPayloadMachine.endpointStream (p :: ps)).length =
        p.1 + p.2 + 2 + (SourceGraphPayloadMachine.endpointStream ps).length := by
      simp [SourceGraphPayloadMachine.endpointStream, EncodedGraph.unary]
      omega
    rw [e, List.length_cons]
    have e2 : (ps.length + 1) * (2 * N + 2) = ps.length * (2 * N + 2) + (2 * N + 2) := by ring
    rw [e2]
    omega

theorem stream_le {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EndpointGraph V E) : strG G ≤ ellG G * (2 * ellG G + 2) := by
  have h := stream_aux (Fintype.card V) (EncodedETHSource.serializeGraph G).edges
    (fun p hp => ⟨(EncodedETHSource.serializeGraph_valid G p hp).1,
      (EncodedETHSource.serializeGraph_valid G p hp).2.1⟩)
  rw [EncodedETHSource.serializeGraph_edges] at h
  have hc := card_le_ell G
  unfold strG
  refine h.trans (Nat.mul_le_mul (by omega) (by omega))

/-! ## The workspace allowance -/

section vec

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Items of the vectors table. -/
abbrev rowsNG (V : Type) [Fintype V] (s : ℕ) : ℕ :=
  GraphVectors.vertexCount V s + GraphVectors.auxiliaryCount s

def BzG (G : EndpointGraph V E) (s : ℕ) : ℕ :=
  (ellG G + 1) + s + q2 G s + strG G + (Fintype.card V + (s - 3)) + Fintype.card V +
    Fintype.card E + 4 * s * Fintype.card E + rowsNG V s + rowsNG V s * q2 G s

noncomputable def BQG (G : EndpointGraph V E) (s : ℕ) : ℕ :=
  s + Fintype.card V + Fintype.card E + strG G + EntryPrepVec.growQ s (Fintype.card E)

theorem vcell_len (G : EndpointGraph V E) (s : ℕ) (k : Fin 25) :
    (VectorsTable.graphBank G s k).length ≤
      strG G + (Fintype.card V + (s - 3)) + Fintype.card V + Fintype.card E +
        4 * s * Fintype.card E := by
  unfold VectorsTable.graphBank EntryVectorsCell.cellBank strG
  split_ifs <;> (try simp only [List.length_replicate, List.length_nil]) <;> omega

theorem exitZ_len (G : EndpointGraph V E) (s : ℕ) (z : VectorsProducer.Z) :
    (VectorsProducer.exitBank G s [] z).length ≤ BzG G s := by
  unfold BzG
  rcases z with i | ((k | j) | e)
  · fin_cases i <;>
      simp [VectorsProducer.exitBank, VectorsProducer.inputs, VectorsProducer.code, ellG] <;> omega
  · have := vcell_len G s k
    show (VectorsTable.graphBank G s k).length ≤ _
    omega
  · fin_cases j <;>
      simp [VectorsProducer.exitBank, VectorsProducer.readyData, MatrixTableWriter.Data.contents,
        MatrixTableWriter.Data.cell, MatrixTableWriter.ready]
  · cases e <;>
      simp [VectorsProducer.exitBank, VectorsProducer.readyData, MatrixTableWriter.Data.contents,
        MatrixTableWriter.Data.foreign, MatrixTableWriter.ready, VectorsProducer.rowsN, rowsNG,
        MatrixMaterialization.rowMajor_length] <;> omega

theorem qd_len (G : EndpointGraph V E) (j : VectorsFromGraphQ.QS) :
    (VectorsFromGraphQ.Qd G j).length ≤ Fintype.card V + Fintype.card E + strG G := by
  unfold VectorsFromGraphQ.Qd strG
  rcases j with ((a | k) | b) | d
  · simp
  · fin_cases k <;> simp <;> omega
  · simp
  · simp

theorem qa_len (G : EndpointGraph V E) (s : ℕ) (j : VectorsFromGraphQ.QS) :
    (VectorsFromGraphQ.Qa G s j).length ≤ s + Fintype.card V + Fintype.card E + strG G := by
  unfold VectorsFromGraphQ.Qa
  by_cases h : j = QProduct.s
  · subst h; simp <;> omega
  · rw [Function.update_of_ne h]
    have := qd_len G j
    omega

theorem lenB_le (G : EndpointGraph V E) (n c : ℕ) (z : VectorsFromGraphQ.Z2) :
    EntryPrepVec.lenB G n c z ≤ BzG G (EntryPrepVec.sv G n c) + BQG G (EntryPrepVec.sv G n c) := by
  rcases z with z | j
  · have := exitZ_len G (EntryPrepVec.sv G n c) z
    show (VectorsProducer.exitBank G (EntryPrepVec.sv G n c) [] z).length ≤ _
    omega
  · have := qa_len G (EntryPrepVec.sv G n c) j
    show (VectorsFromGraphQ.Qa G (EntryPrepVec.sv G n c) j).length +
      EntryPrepVec.growQ (EntryPrepVec.sv G n c) (Fintype.card E) ≤ _
    unfold BQG
    omega

end vec

/-- The majorant of `boundV` on a (graph, bins) pair. -/
noncomputable def bvG (g : GI) : ℕ :=
  ((2 * ellG g.G + 2) + ((2 * g.s + 2) + 0) + 1) +
    (1 + (VectorsFromGraphQ.fullBound g.G g.s +
      ((((2 * q2 g.G g.s + 2) + ((2 * (rowsNG g.V g.s * q2 g.G g.s) + 2) + 0) + 1) +
        (EntryPrepVec.nZ * (BzG g.G g.s + BQG g.G g.s) + EntryPrepVec.nZ + 2) + 1) + 1) + 1) + 1) + 1

theorem boundV_le {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EndpointGraph V E) (n c : ℕ) :
    EntryPrepVec.boundV G n c ≤ bvG ⟨V, E, G, EntryPrepVec.sv G n c⟩ := by
  have hsum := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin EntryPrepVec.nZ))
    (fun i => EntryPrepVec.lenB G n c ((Fintype.equivFin EntryPrepVec.Z2).symm i))
    (BzG G (EntryPrepVec.sv G n c) + BQG G (EntryPrepVec.sv G n c))
    (fun i _ => lenB_le G n c _)
  simp only [Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  unfold EntryPrepVec.boundV bvG
  simp only [MatrixMaterialization.rowMajor_length, rowsNG]
  dsimp only [ellG]
  omega

/-! ## `bvG` is uniformly polynomial in `UG` -/

theorem at_gs : PolyIn UG (fun g => g.s) := PolyIn.of_le fun g => by unfold UG; omega
theorem at_ell : PolyIn UG (fun g => ellG g.G) := PolyIn.of_le fun g => by unfold UG; omega
theorem at_q2 : PolyIn UG (fun g => q2 g.G g.s) := PolyIn.of_le fun g => by unfold UG; omega
theorem at_str : PolyIn UG (fun g => strG g.G) := PolyIn.of_le fun g => by unfold UG; omega
theorem at_V : PolyIn UG (fun g => Fintype.card g.V) := PolyIn.of_le fun g => by
  have := card_le_ell g.G; unfold UG; omega
theorem at_E : PolyIn UG (fun g => Fintype.card g.E) := PolyIn.of_le fun g => by
  have := card_le_ell g.G; unfold UG; omega
theorem at_code : PolyIn UG (fun g => (VectorsProducer.code g.G).length) :=
  PolyIn.mono (fun g => by simp [VectorsProducer.code, ellG]) (PolyIn.add at_ell (PolyIn.const 1))
theorem at_enc : PolyIn UG (fun g => (EncodedGraph.encode (EncodedETHSource.serializeGraph g.G)).length) :=
  at_ell
theorem at_edges : PolyIn UG (fun g => (EncodedETHSource.serializeGraph g.G).edges.length) :=
  PolyIn.mono (fun g => by rw [EncodedETHSource.serializeGraph_edges]) at_E
theorem at_stream : PolyIn UG (fun g =>
    (SourceGraphPayloadMachine.endpointStream (EncodedETHSource.serializeGraph g.G).edges).length) :=
  at_str

macro "gpoly_step" : tactic => `(tactic| first
  | with_reducible apply PolyIn.add
  | with_reducible apply PolyIn.mul
  | with_reducible apply PolyIn.pow
  | with_reducible refine PolyIn.sub _ ?_
  | with_reducible refine PolyIn.div _ ?_
  | with_reducible refine PolyIn.mono (fun _ => QPublicGrowth.arithmetic_cost_le _ _) ?_
  | with_reducible exact PolyIn.const _
  | with_reducible exact at_gs
  | with_reducible exact at_ell
  | with_reducible exact at_enc
  | with_reducible exact at_q2
  | with_reducible exact at_str
  | with_reducible exact at_stream
  | with_reducible exact at_V
  | with_reducible exact at_E
  | with_reducible exact at_code
  | with_reducible exact at_edges
  | dsimp only)

theorem bvG_poly : PolyIn UG bvG := by
  unfold bvG BzG BQG rowsNG EntryPrepVec.growQ VectorsFromGraphQ.fullBound
    VectorsProducer.producerBound MatrixTableWriter.writerBound VectorsTable.tableT
    VectorsTable.vectorsT VectorsProducer.rowsN GraphVectors.vertexCount GraphVectors.auxiliaryCount
  simp only [MatrixAddressMachine.exactTime]
  repeat' gpoly_step

#print axioms stream_le
#print axioms exitZ_len
#print axioms lenB_le
#print axioms boundV_le
#print axioms bvG_poly

end EthInapproximability.CurrentPaper.EntryClockPoly
