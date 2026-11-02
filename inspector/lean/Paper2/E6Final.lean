import Paper2.E6Err
import Paper2.E6DecClock
-- root successor copy (30 September 2026, for the R22 batch): the docstring citation of a non-existent `decAlg_sparse` replaced by the theorem's name `growDec_sparse` (readback:a-eth-6 defect D5), and the T24_whole_budget_final docstring restating the R20 gloss withdrawn by R22 point 4 (readback:a-carrier-2 defect DC2) corrected; no other change.

/-!
# Paper A (lock v12), lane `owner:a-eth-6`, segment 3: T24 and T03 at class level in the R20 carrier

Lock v12 `sections/06-reduction.tex:107-117` (`thm:quantitative`): "Assuming randomized sparse ETH, for every
fixed $0\le c<1/12$ there is no bounded-error randomized algorithm, polynomial in the number $T$ of matrix
entries, that estimates $\D(M)$ with additive error at most $c\,\frac{\log T}{\log\log T}$ on every
sufficiently large explicit Boolean matrix."

`growDec_sparse`: from ANY selected-tape estimator `E` with `EstimatesGrowingSel E c` (R19 carrier), for EVERY
density `cs`, the composite decider `decAlg D B (selectedClassifier E) (cs + 2) N₁ …` (ONE fixed machine,
R20 carrier: computed tape length with `lenPoly`) is an R20 sparse decider at density `cs`:
* error: on every well-formed `cs`-sparse input `encode Φ`, the decider realises the route-B identity at the
  ROUTED formula `Φ'` (`decAlg_joinAt`), `Φ'` is `(cs+2)`-sparse with at least `N₁` variables and is
  equisatisfiable with `Φ` (a-eth-owner-4 `routed4_sat_iff`), and the error transfer at `Φ'`
  (`decider_error_joinAt`) gives the bounded error; there is NO separate small-`N` premise;
* clock: `decTime_budget` (D-A6).
Hence `¬ RandomizedSparseETH_R20` (`not_R20_iff`), with NO `hAsm` premise.

No ledger row is closed. Nothing here is admitted.
-/

noncomputable section

namespace Paper2.AEth6

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2 Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics
open Paper2.AEth Paper2.AEth2 Paper2.AEth4 Paper2.AEth5

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

/-- The internal cutoff of the composite decider for estimator `E`, density `cs`, gap constant `c`. -/
def cutN (E : SelectedTape.Algorithm) (cs : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12) : ℕ :=
  max 1 (max (N0 D B (Paper2.HeaderStrip.selectedClassifier E) (cs + 2))
    (max (Classical.choose (decider_error_joinAt D B (cs + 2) c hc0 hc))
      (Classical.choose (decTime_budget D B (Paper2.HeaderStrip.selectedClassifier E) (cs + 2)))))

theorem cutN_pos (E : SelectedTape.Algorithm) (cs : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12) :
    1 ≤ cutN D B E cs c hc0 hc := le_max_left _ _

theorem cutN_N0 (E : SelectedTape.Algorithm) (cs : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12) :
    N0 D B (Paper2.HeaderStrip.selectedClassifier E) (cs + 2) ≤ cutN D B E cs c hc0 hc :=
  le_trans (le_max_left _ _) (le_max_right _ _)

theorem cutN_K (E : SelectedTape.Algorithm) (cs : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12) :
    2 ≤ (cs + 2) * cutN D B E cs c hc0 hc := by
  have := cutN_pos D B E cs c hc0 hc
  nlinarith

/-- **THE composite growing-gap decider** (R20 carrier) for estimator `E` and density `cs`. -/
def growDec (E : SelectedTape.Algorithm) (cs : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12) :
    ETape.Algorithm :=
  decAlg D B (Paper2.HeaderStrip.selectedClassifier E) (cs + 2) (cutN D B E cs c hc0 hc)
    (cutN_pos D B E cs c hc0 hc) (cutN_N0 D B E cs c hc0 hc) (cutN_K D B E cs c hc0 hc)

set_option maxHeartbeats 1000000 in
/-- **Segment 3: the composite decider is an R20 sparse decider at density `cs`.** -/
theorem growDec_sparse (E : SelectedTape.Algorithm) (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12)
    (hE : EstimatesGrowingSel E c) (cs : ℕ) :
    SparseDeciderR20 cs (growDec D B E cs c hc0 hc) := by
  have hN₁ := cutN_pos D B E cs c hc0 hc
  have hN := cutN_N0 D B E cs c hc0 hc
  have hK := cutN_K D B E cs c hc0 hc
  have herr := Classical.choose_spec (decider_error_joinAt D B (cs + 2) c hc0 hc)
  have hclk := Classical.choose_spec
    (decTime_budget D B (Paper2.HeaderStrip.selectedClassifier E) (cs + 2))
  have hNerr : Classical.choose (decider_error_joinAt D B (cs + 2) c hc0 hc) ≤ cutN D B E cs c hc0 hc :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hNclk : Classical.choose (decTime_budget D B (Paper2.HeaderStrip.selectedClassifier E) (cs + 2)) ≤
      cutN D B E cs c hc0 hc :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  refine ⟨fun input hwf hsp => ?_, fun ε hε => ?_⟩
  · obtain ⟨Φ, rfl⟩ := hwf
    rw [ADecider.cnfClauseCount_encode, ADecider.variableCount_encode] at hsp
    have hspK : Φ.val.clauses.length ≤ (cs + 2) * Φ.val.variables :=
      le_trans hsp (Nat.mul_le_mul_right _ (by omega))
    set Φ' := routedV (cs + 2) (cutN D B E cs c hc0 hc) hN₁ (EncodedCNF.encode Φ.val) with hΦ'
    have hJ := decAlg_joinAt D B E (cs + 2) (cutN D B E cs c hc0 hc) hN₁ hN hK (EncodedCNF.encode Φ.val)
    have hsp' : Φ'.val.clauses.length ≤ (cs + 2) * Φ'.val.variables :=
      routed4_sparse (cs + 2) (cutN D B E cs c hc0 hc) hK _
    have hv' : cutN D B E cs c hc0 hc ≤ Φ'.val.variables := routed4_variables _ _ _
    have h := herr Φ' hsp' (le_trans hNerr hv') E (growDec D B E cs c hc0 hc)
      (EncodedCNF.encode Φ.val) hE hJ
    have hlang : EncodedCNF.encode Φ'.val ∈ EncodedCNF.Language ↔
        EncodedCNF.encode Φ.val ∈ EncodedCNF.Language := by
      rw [EncodedCNF.encode_mem_iff Φ'.val Φ'.property]
      exact routed4_sat_iff (cs + 2) hN₁ Φ.val Φ.property hspK
    exact ⟨fun hin => h.1 (hlang.2 hin), fun hout => h.2 (fun h' => hout (hlang.1 h'))⟩
  · obtain ⟨C', d, N₂, hb⟩ := hclk (cutN D B E cs c hc0 hc) hN₁ hNclk hK ε hε
    refine ⟨C', d, N₂, fun input hwf hsp hN2 => ?_⟩
    obtain ⟨Φ, rfl⟩ := hwf
    rw [ADecider.cnfClauseCount_encode, ADecider.variableCount_encode] at hsp
    rw [ADecider.variableCount_encode] at hN2 ⊢
    have hspK : Φ.val.clauses.length ≤ (cs + 2) * Φ.val.variables :=
      le_trans hsp (Nat.mul_le_mul_right _ (by omega))
    exact hb Φ hspK hN2

include D B in
/-- **T24 at class level, R20 carrier, final** (`0 ≤ c < 1/12`; lock v12 `thm:quantitative`). Under
randomized sparse ETH (R20 carrier, D-A6) there is NO selected-tape estimator (R19 carrier: polynomial
in `T`, bounded error, on EVERY decodable word) with additive error `c log T / log log T`.
Remaining premises: the records `D : DinurReduction`, `B : BOTReduction (booleanOccurrence D)` (D-A7);
D-A2 is the language `EncodedCNF.Language`; D-A6 is the shape of `RandomizedSparseETH_R20`. -/
theorem T24_class_final (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12)
    (hETH : RandomizedSparseETH_R20) :
    ¬ ∃ E : SelectedTape.Algorithm, EstimatesGrowingSel E c := by
  rintro ⟨E, hE⟩
  exact (not_R20_iff.2 (fun cs => ⟨growDec D B E cs c hc0 hc, growDec_sparse D B E c hc0 hc hE cs⟩)) hETH

include D B in
/-- **T03** (lock v12 `intro:quantitative`, `0 < c < 1/12`): same premises. -/
theorem T03_class_final (c : ℝ) (hc0 : 0 < c) (hc : c < 1 / 12)
    (hETH : RandomizedSparseETH_R20) :
    ¬ ∃ E : SelectedTape.Algorithm, EstimatesGrowingSel E c :=
  T24_class_final D B c hc0.le hc hETH

include D B in
/-- T24 in contrapositive form: an estimator refutes randomized sparse ETH in the R20 carrier, the
a-eth-owner-1 carrier, the prefix carrier and the DRAFT shape. -/
theorem T24_refutes (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12)
    (hE : ∃ E : SelectedTape.Algorithm, EstimatesGrowingSel E c) :
    ¬ RandomizedSparseETH_R20 ∧ ¬ Paper2.AEth.RandomizedSparseETH_effective ∧
      ¬ Paper2.AModel.RandomizedSparseETH ∧
      ¬ Paper2.Unit4Shell.Definitions.RandomizedSparseETH EncodedCNF.Language
        Paper2.AModel.WellFormedCNF EncodedETHTail.variableCount Paper2.AModel.cnfClauseCount
        (1 / 3) true := by
  have h : ¬ RandomizedSparseETH_R20 := fun hETH => T24_class_final D B c hc0 hc hETH hE
  exact ⟨h, not_old_of_not_R20 h, not_prefix_of_not_R20 h, not_draft_of_not_R20 h⟩

include D B in
/-- The conclusion of a-eth-owner-2 `T24_class_effective_final` WITHOUT its `hAsm` premise (the composite
decider replaces the assembly statement); an alias of `T24_refutes`. -/
theorem T24_class_effective_final_discharged (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12)
    (hE : ∃ E : SelectedTape.Algorithm, EstimatesGrowingSel E c) :
    ¬ RandomizedSparseETH_R20 ∧ ¬ Paper2.AEth.RandomizedSparseETH_effective ∧
      ¬ Paper2.AModel.RandomizedSparseETH ∧
      ¬ Paper2.Unit4Shell.Definitions.RandomizedSparseETH EncodedCNF.Language
        Paper2.AModel.WellFormedCNF EncodedETHTail.variableCount Paper2.AModel.cnfClauseCount
        (1 / 3) true :=
  T24_refutes D B c hc0 hc hE

/-- **The decider's clock plus the length budget `lenCap`, within the D-A6 budget** (R20; the gloss
"including its length computation" was withdrawn by root decision R22, point 4). -/
theorem T24_whole_budget_final (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12)
    (E : SelectedTape.Algorithm) (hE : EstimatesGrowingSel E c) (cs : ℕ) :
    SparseDeciderR20 cs (growDec D B E cs c hc0 hc) ∧
      ∀ ε : ℝ, 0 < ε → ∃ C d N₀ : ℕ, ∀ input, Paper2.AModel.WellFormedCNF input →
        Paper2.AModel.cnfClauseCount input ≤ cs * EncodedETHTail.variableCount input →
        N₀ ≤ EncodedETHTail.variableCount input →
        (growDec D B E cs c hc0 hc).lenCap input + (growDec D B E cs c hc0 hc).time input ≤
          C * ⌈(2 : ℝ) ^ (ε * EncodedETHTail.variableCount input)⌉₊ * (input.length + 1) ^ d := by
  have hS := growDec_sparse D B E c hc0 hc hE cs
  exact ⟨hS, whole_budget cs _ hS⟩

end Paper2.AEth6

end

#print axioms Paper2.AEth6.cutN_K
#print axioms Paper2.AEth6.growDec
#print axioms Paper2.AEth6.growDec_sparse
#print axioms Paper2.AEth6.T24_class_final
#print axioms Paper2.AEth6.T03_class_final
#print axioms Paper2.AEth6.T24_refutes
#print axioms Paper2.AEth6.T24_class_effective_final_discharged
#print axioms Paper2.AEth6.T24_whole_budget_final
