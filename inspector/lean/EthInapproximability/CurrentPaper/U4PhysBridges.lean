import EthInapproximability.CurrentPaper.Bridges
import EthInapproximability.CurrentPaper.PhysicalLevelRun

/-!
# Unit-4 bridges for the generalized-numbering run (lane owner:b-unit4-shell-2)

Source: frozen v8 `06-eth.tex:89-116` and `06-eth.tex:204-243` (proof of `thm:main`).
The H-B2 interface `PhysicalLevelRun.HB2Physical` (lane owner:b-weighted-level-3, root decision
of 25 September 21:05) produces the table of the PHYSICAL run `physRun`, not of `Iteration.run`:
the two matrices differ by the proof-side renumbering. The frozen `Unit4Bridges.branchOf` is
stated for `Iteration.run`, so the item packet an H-B2 machine can produce is NOT literally
`packet M (branchOf g).table ...`. This module restates the branch objects on `physRun` and
re-derives their semantics from the checked `PhysicalLevelRun.physical_finite_gap_and_size`
(hypotheses verbatim those of `IterationComplete.finite_gap_and_size`) and the frozen
`Unit4Bridges.padding_fit` (rows/columns transported by the first conjunct). Pure lemmas: no
machine, no runtime claim.
-/

namespace EthInapproximability.CurrentPaper.Unit4PhysBridges

open EncodedETHSource EncodedETHSourceComposition EffectiveIteration Unit4Bridges
open EthInapproximability.ParameterizedNP.GuardedSourceGraph

-- The same local instance as `EncodedETHSource.lean:34-35` and `Bridges.lean:27`.
local instance (n : ℕ) (p : Fin n → Prop) [DecidablePred p] : Decidable (∃ i, p i) :=
  Fintype.decidableExistsFintype

section Branches

variable {η : ℚ} (S : Sparsification η) (D : DinurReduction)
  (B : BOTReduction (booleanOccurrence D)) (c A d : ℕ)

/-- The `k = L n`-th state of the physical (generalized-numbering) run of the typed branch
graph, `L = ETHTailGrowth.repetitions c A d`. -/
noncomputable def physState (n : ℕ) (g : ValidFormula) : Iteration.State :=
  PhysicalLevelRun.physRun (branchGraph D B n g) c (sourceDepth n)
    (Iteration.seedState (sourceDepth n)) (ETHTailGrowth.repetitions c A d n)

/-- The padded table branch of the physical run: `FinalPadding.table` of the `k`-th physical
matrix at `p = FinalPadding.exponent L n`, threshold the `k`-th physical budget. -/
noncomputable def physBranchOf (n : ℕ) (g : ValidFormula) : EncodedETHTail.Branch :=
  EncodedETHTail.paddedBranch (physState D B c A d n g).matrix.entry
    (FinalPadding.exponent (ETHTailGrowth.repetitions c A d) n)
    (physState D B c A d n g).budget
    (physState D B c A d n g).matrix.rows_pos (physState D B c A d n g).matrix.columns_pos

noncomputable def physBranches (f : ValidFormula) : List EncodedETHTail.Branch :=
  (S.branches f).map (physBranchOf D B c A d f.val.variables)

/-- One branch of the physical run: the same four facts as `Unit4Bridges.branch_facts`. -/
theorem phys_branch_facts (f : ValidFormula) (hn : 1 ≤ f.val.variables)
    (hk : 1 ≤ ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
      (sourceSizeExponent S D B) f.val.variables)
    (hsource : 2 ^ 44 * (B.degreeBound : ℚ) / sourceGap D B ≤ c)
    (g : ValidFormula) (hg : g ∈ S.branches f) :
    (EncodedCNF.Satisfiable g.val →
      (physBranchOf D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
        f.val.variables g).cost ≤
      (physBranchOf D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
        f.val.variables g).threshold) ∧
    (¬ EncodedCNF.Satisfiable g.val →
      (physBranchOf D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
        f.val.variables g).cost =
      (physBranchOf D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
        f.val.variables g).threshold +
        ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
          (sourceSizeExponent S D B) f.val.variables) ∧
    (physBranchOf D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
        f.val.variables g).table.length =
      FinalPadding.tableSize (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
        (sourceSizeExponent S D B)) f.val.variables ∧
    2 * ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
        (sourceSizeExponent S D B) f.val.variables *
      ((physBranchOf D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
        f.val.variables g).threshold +
        ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
          (sourceSizeExponent S D B) f.val.variables) < f.val.variables := by
  obtain ⟨hcommon, hlower0, hupper0⟩ := branch_source_facts S D B f hn g hg
  rw [output_eq_serialize, serializeGraph_edges] at hlower0 hupper0
  have hlower := hlower0
  have hupper := hupper0
  have hcut := CutoffBitMachine.actualClock_selected_cutoff c (2 ^ sourceSizeExponent S D B)
    (sourceSizeExponent S D B) f.val.variables _ hk le_rfl
  have hΔ : 0 < B.degreeBound := B.degreeBound_pos
  have pg := PhysicalLevelRun.physical_finite_gap_and_size (branchGraph D B f.val.variables g) c
    (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B) f.val.variables _
    (by omega) hcut hΔ (source_gap_pos D B) (source_gap_le_one D B) hcommon hsource
    hlower hupper
  dsimp only at pg
  have hfit := padding_fit (branchGraph D B f.val.variables g) c
    (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B) f.val.variables _
    (by omega) hcut hcommon.1 hlower hupper
  have hdim := pg.1 (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
    (sourceSizeExponent S D B) f.val.variables)
  have hrows : (physState D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
      f.val.variables g).matrix.rows ≤
      2 ^ FinalPadding.exponent (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
        (sourceSizeExponent S D B)) f.val.variables := by
    have h := hdim.2.1
    unfold physState
    rw [h]
    exact hfit.1
  have hcols : (physState D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
      f.val.variables g).matrix.columns ≤
      2 ^ FinalPadding.exponent (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
        (sourceSizeExponent S D B)) f.val.variables := by
    have h := hdim.2.2
    unfold physState
    rw [h]
    exact hfit.2.1
  have hcost := EncodedETHTail.paddedBranch_cost
    (physState D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
      f.val.variables g).matrix.entry
    (FinalPadding.exponent (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
      (sourceSizeExponent S D B)) f.val.variables)
    (physState D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
      f.val.variables g).budget
    (physState D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
      f.val.variables g).matrix.rows_pos
    (physState D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
      f.val.variables g).matrix.columns_pos hrows hcols
  refine ⟨?_, ?_, (physBranchOf D B c _ _ _ g).length_eq, pg.2.2.2.2 _ le_rfl⟩
  · intro hsat
    have hY := B.normalized_yes (booleanFormula D g).val (booleanFormula D g).property
      (boolean_occurrence D g) f.val.variables (boolean_yes D g hsat)
    change (EncodedETHTail.paddedBranch _ _ _ _ _).cost ≤ _
    rw [hcost]
    exact pg.2.1 hY _ le_rfl
  · intro hns
    have hN := B.normalized_no (booleanFormula D g).val (booleanFormula D g).property
      (boolean_occurrence D g) (boolean_ratio_pos D) (boolean_variable_ratio D g)
      (boolean_no D g hns).2 f.val.variables (boolean_gap_pos D) (boolean_gap_le_one D)
      (boolean_no D g hns).1
    change (EncodedETHTail.paddedBranch _ _ _ _ _).cost = _
    rw [hcost]
    exact (pg.2.2.1 hN _ le_rfl).1

/-- Whole list of the physical run: exactly the premises `herror`, `hgap`, `hyes`, `hno` of the
admitted `SignedMidpointApproxActualMapper.sat_outputs_linear`, as in
`Unit4Bridges.branches_semantics`. -/
theorem phys_branches_semantics (f : ValidFormula) (hn : 1 ≤ f.val.variables)
    (hk : 1 ≤ ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
      (sourceSizeExponent S D B) f.val.variables)
    (hsource : 2 ^ 44 * (B.degreeBound : ℚ) / sourceGap D B ≤ c)
    (answer : List Bool → ℤ)
    (herr : ∀ b : EncodedETHTail.Branch, |answer b.table - (b.cost : ℤ)| ≤
      (FinalPadding.allowance (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
        (sourceSizeExponent S D B)) b.table.length : ℤ)) :
    (∀ b ∈ physBranches S D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B) f,
      |answer b.table - (b.cost : ℤ)| ≤
        (FinalPadding.allowance (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
          (sourceSizeExponent S D B))
          (FinalPadding.tableSize (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
            (sourceSizeExponent S D B)) f.val.variables) : ℤ)) ∧
    2 * FinalPadding.allowance (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
          (sourceSizeExponent S D B))
        (FinalPadding.tableSize (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
          (sourceSizeExponent S D B)) f.val.variables) <
      ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
        (sourceSizeExponent S D B) f.val.variables ∧
    (EncodedCNF.encode f.val ∈ EncodedCNF.Language →
      ∃ b ∈ physBranches S D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B) f,
        b.cost ≤ b.threshold) ∧
    (EncodedCNF.encode f.val ∉ EncodedCNF.Language →
      ∀ b ∈ physBranches S D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B) f,
        b.cost = b.threshold + ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
          (sourceSizeExponent S D B) f.val.variables) := by
  have hmem := EncodedCNF.encode_mem_iff f.val f.property
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hb
    have hlen := (phys_branch_facts S D B c f hn hk hsource g hg).2.2.1
    have h := herr (physBranchOf D B c (2 ^ sourceSizeExponent S D B)
      (sourceSizeExponent S D B) f.val.variables g)
    rw [hlen] at h
    exact h
  · exact ClockedPadding.gap_fit
      (CutoffBitMachine.actualClock c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B))
      f.val.variables hk
  · intro hin
    obtain ⟨g, hg, hsat⟩ := S.some_yes f (hmem.mp hin)
    exact ⟨_, List.mem_map.mpr ⟨g, hg, rfl⟩,
      (phys_branch_facts S D B c f hn hk hsource g hg).1 hsat⟩
  · intro hout b hb
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hb
    exact (phys_branch_facts S D B c f hn hk hsource g hg).2.1
      (S.every_no f (fun h => hout (hmem.mpr h)) g hg)

end Branches

end EthInapproximability.CurrentPaper.Unit4PhysBridges
