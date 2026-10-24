import EthInapproximability.CurrentPaper.EncodedETHSourceComposition
import EthInapproximability.CurrentPaper.IterationComplete
import EthInapproximability.CurrentPaper.FinalPadding
import EthInapproximability.CurrentPaper.ETHTailGrowth
import EthInapproximability.CurrentPaper.CutoffBitMachine
import EthInapproximability.CurrentPaper.EncodedETHTail
import EthInapproximability.CurrentPaper.ClockedPadding

/-!
# Unit-4 bridges (B4-S6a padding fit, B4-S6b size bridge, B4-S6c/d branch semantics)

Source: frozen v8 `06-eth.tex:23-51` (`thm:paper-sparse-gap-source`, the size bound
`n (log (n+2))^{c_eps}`), `06-eth.tex:89-116` (`k(n) = L(n)`, `p(n) = floor(n/(2 max{1,k(n)}))`,
`T(n) = 2^{2p(n)}`), `06-eth.tex:204-243` (proof of `thm:main`: the branch list and the midpoint
test). Pure lemmas: no machine and no runtime claim. Every fact is derived from the admitted
declarations named in the unit-4 map, by exact name.
-/

namespace EthInapproximability.CurrentPaper.Unit4Bridges

open EncodedETHSource EncodedETHSourceComposition EffectiveIteration
open EthInapproximability.ParameterizedNP.GuardedSourceGraph

-- Match the generic support enumeration used by `SourceNormalization` and
-- `EncodedETHSource` (the same local instance as in `EncodedETHSource.lean`).
-- This local instance changes no imported or exported instance registration.
local instance (n : ℕ) (p : Fin n → Prop) [DecidablePred p] : Decidable (∃ i, p i) :=
  Fintype.decidableExistsFintype

/-! ## B4-S6b: the displayed logarithmic size bound -/

theorem size_le_depth (n : ℕ) (hn : 1 ≤ n) : n.size + 1 ≤ 2 * sourceDepth n := by
  have h1 : n.size ≤ sourceDepth n := by
    unfold sourceDepth
    rw [Nat.size_le]
    exact lt_of_lt_of_le (by omega) (Nat.le_pow_clog (by decide : 1 < 2) (n + 2))
  have h2 : 1 ≤ sourceDepth n := by
    unfold sourceDepth
    exact Nat.clog_pos (by decide) (by omega)
  omega

/-- `n (n.size + 1)^e ≤ 2^e n (sourceDepth n)^e`: the conversion from the Lean size bound of
`EncodedETHSourceComposition.source_total_size` to the `A * n * sourceDepth n ^ d` form consumed
by `IterationComplete.finite_gap_and_size`, with `A = 2^e`, `d = e`. -/
theorem size_bridge (n e : ℕ) (hn : 1 ≤ n) :
    n * (n.size + 1) ^ e ≤ 2 ^ e * n * sourceDepth n ^ e := by
  have h := Nat.pow_le_pow_left (size_le_depth n hn) e
  rw [mul_pow] at h
  calc n * (n.size + 1) ^ e ≤ n * (2 ^ e * sourceDepth n ^ e) := Nat.mul_le_mul_left n h
    _ = 2 ^ e * n * sourceDepth n ^ e := by ring

/-! ## B4-S6a: padding fit -/

section Padding

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- After `k ≥ 1` rounds beyond the source cutoff, both dimensions of the iterated matrix fit
in `2^p` with `p = n / (2 max 1 k)`, and `p ≥ 1`. -/
theorem padding_fit (G : EndpointGraph V E) (c A d n k : ℕ)
    (hk : 0 < k) (hcut : sourceCutoff c A d k ≤ n)
    (hv : Fintype.card V ≤ 2 * Fintype.card E)
    (hlower : n ≤ Fintype.card E)
    (hupper : Fintype.card E ≤ A * n * sourceDepth n ^ d) :
    (Iteration.run G c (sourceDepth n) (Iteration.seedState (sourceDepth n)) k).matrix.rows ≤
        2 ^ (n / (2 * max 1 k)) ∧
      (Iteration.run G c (sourceDepth n) (Iteration.seedState (sourceDepth n)) k).matrix.columns ≤
        2 ^ (n / (2 * max 1 k)) ∧
      1 ≤ n / (2 * max 1 k) := by
  have h := (run_indexing_table_size_beyond_cutoff G c A d n k hk hcut hv hlower hupper k
    le_rfl).1
  set p := runParameters G c (sourceDepth n) (Iteration.seedState (sourceDepth n)) k with hp
  have hmk : max 1 k = k := max_eq_right hk
  rw [hmk]
  have hS : max 1 (Parameters.namingLength p) ≤ n / (2 * k) := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    have := h
    nlinarith [Nat.le_max_left 1 (Parameters.namingLength p)]
  have hrows : p.rows =
      (Iteration.run G c (sourceDepth n) (Iteration.seedState (sourceDepth n)) k).matrix.rows :=
    rfl
  have hcols : p.columns =
      (Iteration.run G c (sourceDepth n) (Iteration.seedState (sourceDepth n)) k).matrix.columns :=
    rfl
  refine ⟨?_, ?_, (le_max_left _ _).trans hS⟩
  · rw [← hrows]
    exact (Nat.le_pow_clog (by decide : 1 < 2) _).trans
      (Nat.pow_le_pow_right (by decide) ((le_max_left _ _).trans
        ((le_max_right _ _).trans hS)))
  · rw [← hcols]
    exact (Nat.le_pow_clog (by decide : 1 < 2) _).trans
      (Nat.pow_le_pow_right (by decide) ((le_max_right _ _).trans
        ((le_max_right _ _).trans hS)))

end Padding

/-! ## B4-S6c/d: the actual branch list and its semantics -/

section Branches

variable {η : ℚ} (S : Sparsification η) (D : DinurReduction)
  (B : BOTReduction (booleanOccurrence D)) (c A d : ℕ)

/-- The typed normalized graph of a sparse branch, at the ORIGINAL variable count `n`. -/
noncomputable def branchGraph (n : ℕ) (g : ValidFormula) :=
  B.normalized (booleanFormula D g).val (booleanFormula D g).property n

theorem output_eq_serialize (n : ℕ) (g : ValidFormula) :
    B.output (booleanFormula D g).val (booleanFormula D g).property n =
      serializeGraph (branchGraph D B n g) := rfl

/-- The iterated state after `k = L n` rounds, `L = ETHTailGrowth.repetitions c A d`. -/
noncomputable def branchState (n : ℕ) (g : ValidFormula) : Iteration.State :=
  Iteration.run (branchGraph D B n g) c (sourceDepth n) (Iteration.seedState (sourceDepth n))
    (ETHTailGrowth.repetitions c A d n)

/-- The padded table branch of the proof of `thm:main`: table `FinalPadding.table` of the
`k`-th matrix at `p = FinalPadding.exponent L n`, threshold the `k`-th budget. -/
noncomputable def branchOf (n : ℕ) (g : ValidFormula) : EncodedETHTail.Branch :=
  EncodedETHTail.paddedBranch (branchState D B c A d n g).matrix.entry
    (FinalPadding.exponent (ETHTailGrowth.repetitions c A d) n)
    (branchState D B c A d n g).budget
    (branchState D B c A d n g).matrix.rows_pos (branchState D B c A d n g).matrix.columns_pos

noncomputable def branches (f : ValidFormula) : List EncodedETHTail.Branch :=
  (S.branches f).map (branchOf D B c A d f.val.variables)

/-- B4-S6c: the typed graph of a branch satisfies the source hypotheses of
`finite_gap_and_size` at `γ = sourceGap D B`, `A = 2^e`, `d = e`; the edge count is stated on
the serialized graph `B.output ... = serializeGraph (branchGraph ...)`. -/
theorem branch_source_facts (f : ValidFormula) (hn : 1 ≤ f.val.variables)
    (g : ValidFormula) (hg : g ∈ S.branches f) :
    (branchGraph D B f.val.variables g).SourceCommon (sourceGap D B) B.degreeBound ∧
    f.val.variables ≤ (B.output (booleanFormula D g).val (booleanFormula D g).property
      f.val.variables).edges.length ∧
    (B.output (booleanFormula D g).val (booleanFormula D g).property
      f.val.variables).edges.length ≤
      2 ^ sourceSizeExponent S D B * f.val.variables *
        sourceDepth f.val.variables ^ sourceSizeExponent S D B := by
  refine ⟨B.normalized_common _ _ (boolean_occurrence D g) _ _,
    (B.output_edge_bounds _ _ _).1, ?_⟩
  have hmem : (⟨B.output (booleanFormula D g).val (booleanFormula D g).property
      f.val.variables, B.output_valid _ _ _⟩ : BOTReduction.ValidGraph) ∈
      sourceGraphs S D B f :=
    List.mem_map.mpr ⟨booleanFormula D g, List.mem_map.mpr ⟨g, hg, rfl⟩, rfl⟩
  have h := source_total_size S D B f hn _ hmem
  exact (le_trans (Nat.le_add_left _ _) h).trans
    (size_bridge f.val.variables (sourceSizeExponent S D B) hn)

/-- B4-S6d, one branch. With `A = 2^e`, `d = e` (`e = sourceSizeExponent S D B`), `k = L n ≥ 1`
and the source constant `c` above `2^44 Δ / γ`: the branch cost is at most its threshold when
the sparse branch is satisfiable, exactly threshold plus `k` otherwise; the table has length
`tableSize L n`; and `2 k (threshold + k) < n`. -/
theorem branch_facts (f : ValidFormula) (hn : 1 ≤ f.val.variables)
    (hk : 1 ≤ ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
      (sourceSizeExponent S D B) f.val.variables)
    (hsource : 2 ^ 44 * (B.degreeBound : ℚ) / sourceGap D B ≤ c)
    (g : ValidFormula) (hg : g ∈ S.branches f) :
    (EncodedCNF.Satisfiable g.val →
      (branchOf D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
        f.val.variables g).cost ≤
      (branchOf D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
        f.val.variables g).threshold) ∧
    (¬ EncodedCNF.Satisfiable g.val →
      (branchOf D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
        f.val.variables g).cost =
      (branchOf D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
        f.val.variables g).threshold +
        ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
          (sourceSizeExponent S D B) f.val.variables) ∧
    (branchOf D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
        f.val.variables g).table.length =
      FinalPadding.tableSize (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
        (sourceSizeExponent S D B)) f.val.variables ∧
    2 * ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
        (sourceSizeExponent S D B) f.val.variables *
      ((branchOf D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
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
  have fg := IterationComplete.finite_gap_and_size (branchGraph D B f.val.variables g) c
    (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B) f.val.variables _
    (by omega) hcut hΔ (source_gap_pos D B) (source_gap_le_one D B) hcommon hsource
    hlower hupper
  have hfit := padding_fit (branchGraph D B f.val.variables g) c
    (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B) f.val.variables _
    (by omega) hcut hcommon.1 hlower hupper
  have hcost := EncodedETHTail.paddedBranch_cost
    (branchState D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
      f.val.variables g).matrix.entry
    (FinalPadding.exponent (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
      (sourceSizeExponent S D B)) f.val.variables)
    (branchState D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
      f.val.variables g).budget
    (branchState D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
      f.val.variables g).matrix.rows_pos
    (branchState D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
      f.val.variables g).matrix.columns_pos hfit.1 hfit.2.1
  refine ⟨?_, ?_, (branchOf D B c _ _ _ g).length_eq, fg.2.2.2 _ le_rfl⟩
  · intro hsat
    have hY := B.normalized_yes (booleanFormula D g).val (booleanFormula D g).property
      (boolean_occurrence D g) f.val.variables (boolean_yes D g hsat)
    change (EncodedETHTail.paddedBranch _ _ _ _ _).cost ≤ _
    rw [hcost]
    exact fg.1 hY _ le_rfl
  · intro hns
    have hN := B.normalized_no (booleanFormula D g).val (booleanFormula D g).property
      (boolean_occurrence D g) (boolean_ratio_pos D) (boolean_variable_ratio D g)
      (boolean_no D g hns).2 f.val.variables (boolean_gap_pos D) (boolean_gap_le_one D)
      (boolean_no D g hns).1
    change (EncodedETHTail.paddedBranch _ _ _ _ _).cost = _
    rw [hcost]
    exact (fg.2.1 hN _ le_rfl).1

/-- B4-S6d, whole list: exactly the premises `herror`, `hgap`, `hyes`, `hno` of the admitted
`SignedMidpointApproxActualMapper.sat_outputs_linear` / `EncodedETHTail.listAccept_correct` for
`input = encode f`, `branches = branches S D B c (2^e) e f`, `k = L n` and
`A = FinalPadding.allowance L (FinalPadding.tableSize L n)`, from any estimator error bound
`|answer b.table - b.cost| ≤ allowance L b.table.length` (the second conjunct of
`SignedMidpointApproxWitness.approximation_supplies_callback` at `allowance L`). -/
theorem branches_semantics (f : ValidFormula) (hn : 1 ≤ f.val.variables)
    (hk : 1 ≤ ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
      (sourceSizeExponent S D B) f.val.variables)
    (hsource : 2 ^ 44 * (B.degreeBound : ℚ) / sourceGap D B ≤ c)
    (answer : List Bool → ℤ)
    (herr : ∀ b : EncodedETHTail.Branch, |answer b.table - (b.cost : ℤ)| ≤
      (FinalPadding.allowance (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
        (sourceSizeExponent S D B)) b.table.length : ℤ)) :
    (∀ b ∈ branches S D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B) f,
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
      ∃ b ∈ branches S D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B) f,
        b.cost ≤ b.threshold) ∧
    (EncodedCNF.encode f.val ∉ EncodedCNF.Language →
      ∀ b ∈ branches S D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B) f,
        b.cost = b.threshold + ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
          (sourceSizeExponent S D B) f.val.variables) := by
  have hmem := EncodedCNF.encode_mem_iff f.val f.property
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hb
    have hlen := (branch_facts S D B c f hn hk hsource g hg).2.2.1
    have h := herr (branchOf D B c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
      f.val.variables g)
    rw [hlen] at h
    exact h
  · exact ClockedPadding.gap_fit
      (CutoffBitMachine.actualClock c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B))
      f.val.variables hk
  · intro hin
    obtain ⟨g, hg, hsat⟩ := S.some_yes f (hmem.mp hin)
    exact ⟨_, List.mem_map.mpr ⟨g, hg, rfl⟩, (branch_facts S D B c f hn hk hsource g hg).1 hsat⟩
  · intro hout b hb
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hb
    exact (branch_facts S D B c f hn hk hsource g hg).2.1
      (S.every_no f (fun h => hout (hmem.mpr h)) g hg)

end Branches

end EthInapproximability.CurrentPaper.Unit4Bridges
