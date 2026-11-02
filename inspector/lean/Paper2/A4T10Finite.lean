import Paper2.A4GraphBridges
import EthInapproximability.CurrentPaper.EncodedETHSourceComposition
import Paper2.EncodedSelectedOutput

/-!
# Unit 4 (Paper A), segment A4-S3 (finite part): the T10 source and the fixed-k T01 core

Owner lane `owner:a-unit4-shell` (private, 25 September 2026).
Source: lock v12 `04-source.tex` `src:gap-colouring` (T10) and `01-introduction.tex`
`intro:theorem` (T01), with `06-reduction.tex` `thm:uniform-reduction` (T23).

The cited records enter only as the two parameters `D : EncodedETHSource.DinurReduction` (X03)
and `B : EncodedETHSource.BOTReduction (booleanOccurrence D)` (X04): whether Paper A may take
Paper B's records as its X03/X04 contract is the author's decision D-A7, NOT taken here.
There is no sparsifier in Paper A: the semantic T10 graph of a valid formula `Φ` is the
BOT-normalized output on `EncodedETHSourceComposition.booleanFormula D Φ` (Paper B's generic-
alphabet Boolean CSP-to-3CNF encoding, never `a = 2`), padded to `Φ`'s variable count.

The T01 core below composes T10 with the banked finite reduction guarantees
`EncodedSelectedOutput.every_yes_output_language` and `positive_gap_noLanguageProbability`
(the same `select`/`outputBits` object that H-A3's machine must produce).

**None of these statements closes a ledger row** (T10, T01, X03, X04 stay open); nothing here
is a machine or a runtime bound.
-/

namespace Paper2.Unit4Shell.T10Finite

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2.Unit4Shell.GraphBridges

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

/-- The semantic T10 graph of a valid 3-CNF `Φ` (DRAFT name). -/
noncomputable def t10Graph (Φ : ValidFormula) : EncodedGraph.Graph :=
  B.output (booleanFormula D Φ).val (booleanFormula D Φ).property Φ.val.variables

theorem t10Graph_valid (Φ : ValidFormula) : (t10Graph D B Φ).Valid :=
  B.output_valid _ _ _

theorem t10_vertices_pos (Φ : ValidFormula) : 0 < (t10Graph D B Φ).vertices :=
  output_vertices_pos B _ _ _

/-- **T10 (finite content), HYP on the cited records `D`, `B`.** For every valid 3-CNF `Φ` the
graph `t10Graph D B Φ` has an edge, at least `Φ.variables` edges, no isolated vertex, maximum
degree at most `B.degreeBound`, is three-colourable when `Φ` is satisfiable, and otherwise every
colouring has at least a `sourceGap D B` fraction of monochromatic edges (real form, as consumed
by `positive_gap_noLanguageProbability`). Does not close a ledger row. -/
theorem t10_source (Φ : ValidFormula) :
    0 < (t10Graph D B Φ).edges.length ∧
    Φ.val.variables ≤ (t10Graph D B Φ).edges.length ∧
    (∀ v, ∃ e b, CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ) e b = v) ∧
    (∀ v, SourceItems.degree
      (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) v ≤ B.degreeBound) ∧
    (∀ e, CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ) e false ≠
      CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ) e true) ∧
    (EncodedCNF.Satisfiable Φ.val → FiniteFallbackOutput.ThreeColourable
      (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))) ∧
    (¬ EncodedCNF.Satisfiable Φ.val → ∀ colour : Fin (t10Graph D B Φ).vertices → Fin 3,
      ((sourceGap D B : ℚ) : ℝ) * (t10Graph D B Φ).edges.length ≤
        ((Finset.univ.filter (fun e =>
          colour (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ) e false) =
          colour (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ) e true))).card
          : ℝ)) := by
  have hk := boolean_occurrence D Φ
  obtain ⟨hinc, hdeg, hloop⟩ :=
    output_structural B (booleanFormula D Φ).val (booleanFormula D Φ).property hk Φ.val.variables
  refine ⟨output_edges_pos B _ _ _,
    (B.output_edge_bounds _ _ _).1, hinc, hdeg, hloop, ?_, ?_⟩
  · intro hyes
    exact output_yes B _ _ hk _ (boolean_yes D Φ hyes)
  · intro hno colour
    obtain ⟨hgap, hm⟩ := boolean_no D Φ hno
    exact output_no B _ _ hk (boolean_ratio_pos D) (boolean_variable_ratio D Φ) hm _
      (boolean_gap_pos D) (boolean_gap_le_one D) hgap colour

/-- **Fixed-k T01 core (finite), HYP on `D`, `B`.** Composing T10 with the banked finite
reduction guarantees: for every valid `Φ` and `k ≥ 1`, on every tape of the selected output the
encoded instance is in `EncodedCommunication.Language` (i.e. `D(M) ≤ B`) when `Φ` is
satisfiable, and otherwise the probability of `D(M) ≥ B + k` (not in the language) is at least
`1 - 2^-11 ≥ 981/1000`. This is the same `select`/`outputBits` object H-A3's machine must print.
Does not close a ledger row (T01 also needs the machine, H-A3, and polynomial resources). -/
theorem t01_finite_core (Φ : ValidFormula) (k : ℕ) (hk : 1 ≤ k) :
    (EncodedCNF.Satisfiable Φ.val →
      ∀ t : (TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
          (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
          B.degreeBound (sourceGap D B) k).Tape,
        EncodedSelectedOutput.outputBits (t10_vertices_pos D B Φ)
          (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
          B.degreeBound (sourceGap D B) k t ∈ EncodedCommunication.Language) ∧
    (¬ EncodedCNF.Satisfiable Φ.val →
      (981 / 1000 : ℝ) ≤ EncodedSelectedOutput.noLanguageProbability (t10_vertices_pos D B Φ)
          (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
          B.degreeBound (sourceGap D B) k) := by
  obtain ⟨hm, _, _, hdeg, hloop, hyes, hno⟩ := t10_source D B Φ
  have hΔ : 0 < B.degreeBound := B.degreeBound_pos
  have hγ : 0 < sourceGap D B := source_gap_pos D B
  constructor
  · intro hsat t
    exact EncodedSelectedOutput.every_yes_output_language _ _ _ _ _ hloop hdeg hγ hΔ hm
      (hyes hsat) t
  · intro hunsat
    have h := EncodedSelectedOutput.positive_gap_noLanguageProbability
      (t10_vertices_pos D B Φ)
      (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
      B.degreeBound (sourceGap D B) k hk hloop hdeg hγ hΔ hm (hno hunsat)
    have hnum : (981 / 1000 : ℝ) ≤ 1 - (1 / 2 : ℝ) ^ 11 := by norm_num
    linarith

end Paper2.Unit4Shell.T10Finite
