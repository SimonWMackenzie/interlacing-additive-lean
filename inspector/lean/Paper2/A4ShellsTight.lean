import Paper2.A4FrontClosed
import Paper2.A4T10Size
import Paper2.A4ShellsT24

/-!
# Unit 4 (Paper A), segment A4-S10 tightened (owner lane `owner:a-unit4-shell-3`)

Private, 26 September 2026. Production universe. `T01_of_glue` and `T24_source_shell` are
taken from owner-2's UNCHECKPOINTED draft `A4ShellsTight.lean` (source SHA-256 in
`SHA256SUMS.txt`), whose bodies are copied here and compiled in THIS lane (the draft object is
not imported). New here: `T01_tight`, where every glue contract is discharged
(`FrontClosed.H_T10Front_holds`) and `H_T10Size` is discharged (`T10Size.H_T10Size_holds`).

**An HYP shell is never an endpoint closure. None of these statements closes a ledger row**
(T01, T02, T24 stay open).

* `T01_tight`: the ONLY hypothesis is `H_A3` (the unit-3 endpoint); the cited records `D`
  (X03), `B` (X04) are parameters (D-A7 is the author's).
* `T01_of_glue` (kept for comparison): hypotheses `H_A3` and the three glue contracts.
* `T24_source_shell`: the T45 relations are derived for the actual T10 graph of every sparse
  valid `Φ`; the sparsity density `cs` is a parameter (D-A2/D-A6); the reduction law, costs,
  budget and estimator remain arbitrary (see `R3T24Actual` for the actual law).
-/

namespace Paper2.Unit4Shell.ShellsTight

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2 Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

/-- **T01 shell (fixed `k`), tightened.** Named hypotheses: `H_A3` (unit 3), the generic glue
contracts `H_PairMap`, `H_Packetizer`, `H_BankOut k`; the records `D`, `B` are parameters.
`H_T10Size` and `H_T10Front` are no longer hypotheses. Does not close a ledger row (T01). -/
theorem T01_of_glue (hA3 : Shells.H_A3 B.degreeBound (sourceGap D B)) (k : ℕ) (hk : 1 ≤ k)
    (hPM : T10Front.H_PairMap) (hP : T10Front.H_Packetizer) (hB : T10Front.H_BankOut k) :
    (∃ (M : BitMachine.Machine) (C E : ℕ), ∀ (Φ : ValidFormula) (t : (TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ) (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) B.degreeBound (sourceGap D B) k).Tape),
      M.OutputsWithin
        (EncodedComplexity.pair (EncodedCNF.encode Φ.val) ((TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ) (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) B.degreeBound (sourceGap D B) k).tapeBits t))
        (EncodedSelectedOutput.outputBits (t10_vertices_pos D B Φ)
          (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
          B.degreeBound (sourceGap D B) k t)
        (C * ((EncodedComplexity.pair (EncodedCNF.encode Φ.val)
          ((TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ) (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) B.degreeBound (sourceGap D B) k).tapeBits t)).length + 1) ^ E)) ∧
    (∀ Φ : ValidFormula, EncodedCNF.Satisfiable Φ.val → ∀ t : (TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ) (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) B.degreeBound (sourceGap D B) k).Tape,
      EncodedSelectedOutput.outputBits (t10_vertices_pos D B Φ)
        (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
        B.degreeBound (sourceGap D B) k t ∈ EncodedCommunication.Language) ∧
    (∀ Φ : ValidFormula, ¬ EncodedCNF.Satisfiable Φ.val →
      (981 / 1000 : ℝ) ≤ TotalFiniteConstructorScratch.successProbability (t10_vertices_pos D B Φ)
        (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
        B.degreeBound (sourceGap D B) k) :=
  Shells.T01_of_interfaces D B hA3 k hk (T10Front.front_of_glue D B hPM hP k hB)
    (T10Size.H_T10Size_holds D B)

/-- **T01 shell (fixed `k`), fully tightened.** The ONLY hypothesis is the unit-3 endpoint
`H_A3` (absolute exponent form); the records `D` (X03) and `B` (X04) are parameters (D-A7).
The T10 front (`H_T10Front`) and the T10 size (`H_T10Size`) are discharged. One fixed machine
per `k` prints, on the literal word `pair (encode Φ) tape`, exactly `outputBits` within a
polynomial of the input length, for every valid `Φ` and every tape of the selected law; YES:
the output is in the language on every tape; NO: `D(M) = budget + k` with probability at
least `981/1000` under the selected tape law. Does not close a ledger row (T01: the tape law
is the constructor's `select` law, not yet identified with uniform exact-length tapes (D-A1);
malformed inputs are not routed; `H_A3` is unit 3's). -/
theorem T01_tight (hA3 : Shells.H_A3 B.degreeBound (sourceGap D B)) (k : ℕ) (hk : 1 ≤ k) :
    (∃ (M : BitMachine.Machine) (C E : ℕ), ∀ (Φ : ValidFormula) (t : (TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ) (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) B.degreeBound (sourceGap D B) k).Tape),
      M.OutputsWithin
        (EncodedComplexity.pair (EncodedCNF.encode Φ.val) ((TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ) (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) B.degreeBound (sourceGap D B) k).tapeBits t))
        (EncodedSelectedOutput.outputBits (t10_vertices_pos D B Φ)
          (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
          B.degreeBound (sourceGap D B) k t)
        (C * ((EncodedComplexity.pair (EncodedCNF.encode Φ.val)
          ((TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ) (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) B.degreeBound (sourceGap D B) k).tapeBits t)).length + 1) ^ E)) ∧
    (∀ Φ : ValidFormula, EncodedCNF.Satisfiable Φ.val → ∀ t : (TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ) (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) B.degreeBound (sourceGap D B) k).Tape,
      EncodedSelectedOutput.outputBits (t10_vertices_pos D B Φ)
        (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
        B.degreeBound (sourceGap D B) k t ∈ EncodedCommunication.Language) ∧
    (∀ Φ : ValidFormula, ¬ EncodedCNF.Satisfiable Φ.val →
      (981 / 1000 : ℝ) ≤ TotalFiniteConstructorScratch.successProbability (t10_vertices_pos D B Φ)
        (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
        B.degreeBound (sourceGap D B) k) :=
  Shells.T01_of_interfaces D B hA3 k hk (FrontClosed.H_T10Front_holds D B k)
    (T10Size.H_T10Size_holds D B)

/-- **T24 midpoint shell on the actual T10 source, tightened.** Beyond an explicit cutoff
`N₀`, for every valid `Φ` with at most `cs·N` clauses (`N = Φ.variables`), the T10 graph of
`Φ` (degree bound `B.degreeBound`, gap `sourceGap D B`) satisfies the T24 error conclusion at
gap `kOf N`, for the rectangular (`square = false`) or square (`square = true`) printed count.
The T45 relations are DERIVED, not assumed. The laws, costs, budget and estimator remain
arbitrary (not identified with the actual reduction). Does not close a ledger row (T24). -/
theorem T24_source_shell (cs : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12) (square : Bool) :
    ∃ N₀ : ℕ, ∀ Φ : ValidFormula, Φ.val.clauses.length ≤ cs * Φ.val.variables →
      N₀ ≤ Φ.val.variables →
      let T : ℕ := if square then
          printedTsq (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length B.degreeBound
            (sourceGap D B) (kOf Φ.val.variables)
        else printedT (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length B.degreeBound
            (sourceGap D B) (kOf Φ.val.variables)
      let a : ℝ := c * (Real.logb 2 T / Real.logb 2 (Real.logb 2 T))
      ∀ {α β : Type} [Fintype α] [Fintype β] (ρ : FiniteLaw β) (μ : FiniteLaw α)
        (cost : β → ℕ) (Bud : ℕ) (est : β → α → ℝ),
        (∀ b, 2 / 3 ≤ μ.prob (fun t => |est b t - cost b| ≤ a)) →
        ((∀ b, cost b ≤ Bud) →
          (ρ.prod (μ.iid Amplification.reps)).prob
            (fun x => ¬ Shells.accepts est Bud (kOf Φ.val.variables) x) ≤ 1 / 100) ∧
        (ρ.prob (fun b => ¬ cost b = Bud + kOf Φ.val.variables) ≤ (1 / 2) ^ 11 →
          (ρ.prod (μ.iid Amplification.reps)).prob
            (fun x => Shells.accepts est Bud (kOf Φ.val.variables) x) ≤
              (1 / 2) ^ 11 + 1 / 100 ∧
          (1 / 2 : ℝ) ^ 11 + 1 / 100 < 1 / 3) := by
  obtain ⟨N₀', hN₀'⟩ := ShellsT24.T24_midpoint_shell B.degreeBound (sourceGap D B)
    (source_gap_pos D B) (by have := B.degreeBound_pos; omega) (D.sizeExponent + 2)
    c hc0 hc square
  refine ⟨max N₀' (2 ^ (2 ^ (D.sizeExponent + 1) * T10Size.t45C D B cs)), ?_⟩
  intro Φ hsparse hN T a α β _ _ ρ μ cost Bud est hμ
  haveI : NeZero (t10Graph D B Φ).vertices := ⟨(t10_vertices_pos D B Φ).ne'⟩
  obtain ⟨_, _, hinc, hdeg, _, _, _⟩ := t10_source D B Φ
  obtain ⟨hNm, hmn, _⟩ := T10Size.t45_relations D B Φ
  have hsize := T10Size.t45_shell_form D B cs Φ hsparse (le_trans (le_max_right _ _) hN)
  exact hN₀' Φ.val.variables (le_trans (le_max_left _ _) hN) _ _
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) hinc hdeg hNm hmn hsize
    ρ μ cost Bud est hμ

#print axioms T01_of_glue
#print axioms T01_tight
#print axioms T24_source_shell

end Paper2.Unit4Shell.ShellsTight
