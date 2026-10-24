import Paper2.E2PerTape
import Paper2.ETapeETH
import Paper2.A4Amplification
-- root successor copy (30 September 2026, for the R22 batch): the T24_whole_budget docstring restating the R20 gloss withdrawn by R22 point 4 (readback:a-carrier-2 defect DC2) corrected; no other change.

/-! a-eth-owner-2 copy of frozen `a-eth-owner-1/AEthJoin.lean` (SHA-256 6e68121a8d13b81050b97010d5fbbb6dc863359257310e0cc0a6d9ac106059a4). Changes: namespace `Paper2.AEth` -> `Paper2.AEth2` (with `open Paper2.AEth`); carrier `SubexpTape.Algorithm` -> the R20 carrier `ETape.Algorithm`; `SparseDecider` / `RandomizedSparseETH_effective` / `not_effective_iff` -> `SparseDeciderR20` / `RandomizedSparseETH_R20` / `not_R20_iff`; the duplicated `prob_not` / `prob_false` (audit A1) DELETED and replaced by the banked `Paper2.Unit4Shell.Amplification.prob_not` and `Paper2.FiniteLaw.prob_false`; appended: the final class theorems. -/

/-!
# Paper A (lock v12), lane `owner:a-eth-1`, segments 4-5, route B: error transfer and T24/T03 at
class level for a "reduction, then header, then A27 classifier" effective decider

Lock v12 `sections/06-reduction.tex:107-153` (`thm:quantitative`, proof: "The midpoint test from
\cref{intro:corollary} decides the formula with bounded error. Both the construction and any
fixed polynomial-time estimator take $n^{O(k+1)}=2^{O(N/\log N)}=2^{o(N)}$, contrary to
randomized sparse ETH.").

Route B replaces the 147-block majority identity of route A (`RealisesMidpointEff`, lane
a-decider-owner-2) by the physical shape the A27 components provide: the decider's tape pushes
forward to (reduction tape law) × (one uniform classifier tape of length `s`), and the decider
prints exactly what the admitted A27 `HeaderStrip.selectedClassifier E` prints on the headered
printed word `natField (2·budget + k) ++ mwOf b` with that tape (`JoinRealises`). The error
bound is DERIVED: per-tape classifier bounds (`classifier_per_tape`: growing gap, per-word
accuracy), the admitted T01 law (`AEndpoint.t01_yes`, `t01_no`: `Pr[D ≥ budget + k] ≥ 981/1000`)
and the admitted two-stage accounting `FiniteLaw.two_stage_failure_le`. No probability identity
is assumed; `JoinRealises` is a deterministic output identity plus the tape pushforward.

`T24_class_effective_join`, `T03_class_effective_join`: `¬ RandomizedSparseETH_R20` with the
remaining premise `hAsm` = the route-B segment-3 assembly (`DeciderAssemblyJoin`). **`hAsm` is a
whole-decider machine premise, NOT an implementation.**

No ledger row is closed.
-/

noncomputable section

namespace Paper2.AEth2

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2 Paper2.FiniteLaw Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics
open Paper2.Unit4Shell.Definitions (uniformTape)
open Paper2.AEth

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

set_option hygiene false in
local notation "EXP" Φ:max k:max => TotalFiniteConstructorScratch.experiment (t10_vertices_pos D B Φ)
  (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) B.degreeBound (sourceGap D B) k

/-- Transport of a pointwise statement along `experiment.output = select` (as in lane
a-decider-owner-3's `forall_of_output_eq`). -/
theorem forall_of_output_eq' {O S : TotalFiniteConstructorScratch.SelectedOutput} (h : O = S)
    (P : (X : TotalFiniteConstructorScratch.SelectedOutput) → X.Tape → Prop)
    (hS : ∀ t, P S t) : ∀ t, P O t := by
  subst h
  exact hS

/-- **Route-B output identity** (a deterministic machine statement with the tape pushforward):
one classifier tape length `s` for all reduction tapes, a split `π` of the decider tape whose
pushforward is (reduction law) × (uniform length-`s` tape), and the decider prints what the A27
classifier prints on the headered printed word with the second component. -/
def JoinRealises (Φ : ValidFormula) (k : ℕ) (E : SelectedTape.Algorithm)
    (A : ETape.Algorithm) : Prop :=
  letI : Fintype (EXP Φ k).output.Tape := (EXP Φ k).tapeFintype
  ∃ (s : ℕ) (π : (Fin (A.tapeLen (EncodedCNF.encode Φ.val).length) → Bool) →
      (EXP Φ k).output.Tape × (Fin s → Bool)),
    (∀ b, (Paper2.HeaderStrip.selectedClassifier E).tapeLength (headerWord D B Φ k b) = s) ∧
    (∀ P : (EXP Φ k).output.Tape × (Fin s → Bool) → Prop,
      (uniformTape (A.tapeLen (EncodedCNF.encode Φ.val).length)).prob (fun t => P (π t)) =
        ((EXP Φ k).tapeLaw.prod (uniformTape s)).prob P) ∧
    ∀ t, A.output (EncodedCNF.encode Φ.val) (List.ofFn t) =
      (Paper2.HeaderStrip.selectedClassifier E).output (headerWord D B Φ k (π t).1)
        (List.ofFn (π t).2)

set_option maxHeartbeats 2000000 in
/-- **Route B, segment 4.** Error `≤ 1/3` (in fact `≥ 99/100` / `≤ 29/1000`) for every effective
decider realising the route-B identity at `k = kOf N`, sparse valid `Φ`, `N ≥ N₀`. -/
theorem decider_error_join (cs : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12) :
    ∃ N₀ : ℕ, ∀ Φ : ValidFormula, Φ.val.clauses.length ≤ cs * Φ.val.variables →
      N₀ ≤ Φ.val.variables → ∀ (E : SelectedTape.Algorithm) (A : ETape.Algorithm),
      EstimatesGrowingSel E c → JoinRealises D B Φ (kOf Φ.val.variables) E A →
      (EncodedCNF.encode Φ.val ∈ EncodedCNF.Language →
        1 - 1 / 3 ≤ A.prob (EncodedCNF.encode Φ.val) (· = [true])) ∧
      (EncodedCNF.encode Φ.val ∉ EncodedCNF.Language →
        A.prob (EncodedCNF.encode Φ.val) (· = [true]) ≤ 1 / 3) := by
  obtain ⟨N₀, hN₀⟩ := classifier_per_tape D B cs c hc0 hc
  refine ⟨max N₀ 36, fun Φ hsp hN E A hE hJ => ?_⟩
  have hN0 : N₀ ≤ Φ.val.variables := le_trans (le_max_left _ _) hN
  have h36 : 36 ≤ Φ.val.variables := le_trans (le_max_right _ _) hN
  have hk1 : 1 ≤ kOf Φ.val.variables := Paper2.Unit4Shell.AsymptoticsExplicit.kOf_pos _ h36
  letI : Fintype (EXP Φ (kOf Φ.val.variables)).output.Tape :=
    (EXP Φ (kOf Φ.val.variables)).tapeFintype
  obtain ⟨s, π, hs, hpush, hout⟩ := hJ
  have hper := hN₀ Φ hsp hN0 E hE
  -- the decider law is the two-stage law
  have key : ∀ Ev : List Bool → Prop,
      A.prob (EncodedCNF.encode Φ.val) Ev =
        ((EXP Φ (kOf Φ.val.variables)).tapeLaw.prod (uniformTape s)).prob
          (fun x => Ev ((Paper2.HeaderStrip.selectedClassifier E).output (headerWord D B Φ (kOf Φ.val.variables) x.1) (List.ofFn x.2))) := by
    intro Ev
    unfold ETape.Algorithm.prob
    have e : (fun t : Fin (A.tapeLen (EncodedCNF.encode Φ.val).length) → Bool =>
        Ev (A.output (EncodedCNF.encode Φ.val) (List.ofFn t))) =
        (fun t => (fun x : (EXP Φ (kOf Φ.val.variables)).output.Tape × (Fin s → Bool) =>
          Ev ((Paper2.HeaderStrip.selectedClassifier E).output (headerWord D B Φ (kOf Φ.val.variables) x.1) (List.ofFn x.2))) (π t)) := by
      funext t; rw [hout t]
    rw [e]
    exact hpush (fun x => Ev ((Paper2.HeaderStrip.selectedClassifier E).output (headerWord D B Φ (kOf Φ.val.variables) x.1) (List.ofFn x.2)))
  -- the second stage is the classifier law
  have perb : ∀ b (Ev : List Bool → Prop),
      (uniformTape s).prob (fun y => Ev ((Paper2.HeaderStrip.selectedClassifier E).output (headerWord D B Φ (kOf Φ.val.variables) b) (List.ofFn y))) =
        (Paper2.HeaderStrip.selectedClassifier E).prob (headerWord D B Φ (kOf Φ.val.variables) b) Ev := by
    intro b Ev
    unfold SelectedTape.Algorithm.prob
    exact (Paper2.AModel.uniformTape_prob_ofFn_congr (hs b) (fun w => Ev ((Paper2.HeaderStrip.selectedClassifier E).output (headerWord D B Φ (kOf Φ.val.variables) b) w))).symm
  refine ⟨fun hin => ?_, fun hout' => ?_⟩
  · -- YES: every tape is within budget
    have hyes : ∀ b : (EXP Φ (kOf Φ.val.variables)).output.Tape,
        Workspace.Types.CommComplexity.D ((EXP Φ (kOf Φ.val.variables)).output.table b).matrix ≤
          (EXP Φ (kOf Φ.val.variables)).output.budget :=
      forall_of_output_eq' (TotalFiniteConstructorScratch.experiment_output_eq_select _ _ _ _ _)
        (fun X t => Workspace.Types.CommComplexity.D (X.table t).matrix ≤ X.budget)
        (fun t => AEndpoint.t01_yes D B EncodedCNF.Language AEndpoint.DA2_recommended Φ
          (kOf Φ.val.variables) t hin)
    have hfirst : (EXP Φ (kOf Φ.val.variables)).tapeLaw.prob (fun _ => ¬ True) ≤ 0 := by
      simp only [not_true_eq_false]
      rw [Paper2.FiniteLaw.prob_false]
    have hsecond : ∀ a : (EXP Φ (kOf Φ.val.variables)).output.Tape, True →
        (uniformTape s).prob (fun y => ¬ ((Paper2.HeaderStrip.selectedClassifier E).output (headerWord D B Φ (kOf Φ.val.variables) a) (List.ofFn y) = [true])) ≤ 1 / 100 := by
      intro a _
      have hn := Paper2.Unit4Shell.Amplification.prob_not (uniformTape s) (fun y => (Paper2.HeaderStrip.selectedClassifier E).output (headerWord D B Φ (kOf Φ.val.variables) a) (List.ofFn y) = [true])
      have hp := perb a (· = [true])
      have := (hper a).1 (hyes a)
      linarith
    have hrej := FiniteLaw.two_stage_failure_le (EXP Φ (kOf Φ.val.variables)).tapeLaw
      (uniformTape s) (fun _ => True)
      (fun a y => ¬ ((Paper2.HeaderStrip.selectedClassifier E).output (headerWord D B Φ (kOf Φ.val.variables) a) (List.ofFn y) = [true])) 0 (1 / 100) hfirst hsecond
      (by norm_num)
    have hcomp := Paper2.Unit4Shell.Amplification.prob_not ((EXP Φ (kOf Φ.val.variables)).tapeLaw.prod (uniformTape s))
      (fun x => (Paper2.HeaderStrip.selectedClassifier E).output (headerWord D B Φ (kOf Φ.val.variables) x.1) (List.ofFn x.2) = [true])
    have hacc := key (· = [true])
    rw [hacc]
    have hrej2 : ((EXP Φ (kOf Φ.val.variables)).tapeLaw.prod (uniformTape s)).prob
        (fun x => ¬ ((Paper2.HeaderStrip.selectedClassifier E).output (headerWord D B Φ (kOf Φ.val.variables) x.1) (List.ofFn x.2) = [true])) ≤ 0 + 1 / 100 := hrej
    linarith
  · -- NO: the good event has mass ≥ 981/1000
    have hno := AEndpoint.t01_no D B EncodedCNF.Language AEndpoint.DA2_recommended Φ
      (kOf Φ.val.variables) hk1 hout'
    have hfirst : (EXP Φ (kOf Φ.val.variables)).tapeLaw.prob
        (fun a => ¬ ((EXP Φ (kOf Φ.val.variables)).output.budget + kOf Φ.val.variables ≤
          Workspace.Types.CommComplexity.D
            ((EXP Φ (kOf Φ.val.variables)).output.table a).matrix)) ≤ 19 / 1000 := by
      have hn := Paper2.Unit4Shell.Amplification.prob_not (EXP Φ (kOf Φ.val.variables)).tapeLaw
        (fun a => (EXP Φ (kOf Φ.val.variables)).output.budget + kOf Φ.val.variables ≤
          Workspace.Types.CommComplexity.D ((EXP Φ (kOf Φ.val.variables)).output.table a).matrix)
      linarith
    have hsecond : ∀ a : (EXP Φ (kOf Φ.val.variables)).output.Tape,
        (EXP Φ (kOf Φ.val.variables)).output.budget + kOf Φ.val.variables ≤
          Workspace.Types.CommComplexity.D
            ((EXP Φ (kOf Φ.val.variables)).output.table a).matrix →
        (uniformTape s).prob (fun y => (Paper2.HeaderStrip.selectedClassifier E).output (headerWord D B Φ (kOf Φ.val.variables) a) (List.ofFn y) = [true]) ≤ 1 / 100 := by
      intro a ha
      have hp := perb a (· = [true])
      have := (hper a).2 ha
      linarith
    have hacc := FiniteLaw.two_stage_failure_le (EXP Φ (kOf Φ.val.variables)).tapeLaw
      (uniformTape s)
      (fun a => (EXP Φ (kOf Φ.val.variables)).output.budget + kOf Φ.val.variables ≤
          Workspace.Types.CommComplexity.D ((EXP Φ (kOf Φ.val.variables)).output.table a).matrix)
      (fun a y => (Paper2.HeaderStrip.selectedClassifier E).output (headerWord D B Φ (kOf Φ.val.variables) a) (List.ofFn y) = [true]) (19 / 1000) (1 / 100) hfirst hsecond
      (by norm_num)
    rw [key (· = [true])]
    have hacc2 : ((EXP Φ (kOf Φ.val.variables)).tapeLaw.prod (uniformTape s)).prob
        (fun x => (Paper2.HeaderStrip.selectedClassifier E).output (headerWord D B Φ (kOf Φ.val.variables) x.1) (List.ofFn x.2) = [true]) ≤ 19 / 1000 + 1 / 100 := hacc
    linarith

/-- **Route-B segment-3 assembly statement** (the remaining premise): D-A6 clock, correct below
the cutoff, route-B identity at `kOf N` from the cutoff on. -/
def DeciderAssemblyJoin (E : SelectedTape.Algorithm) (cs N₁ : ℕ) (A : ETape.Algorithm) :
    Prop :=
  (∀ ε : ℝ, 0 < ε → ∃ C d N₀ : ℕ, ∀ input, AModel.WellFormedCNF input →
      AModel.cnfClauseCount input ≤ cs * EncodedETHTail.variableCount input →
      N₀ ≤ EncodedETHTail.variableCount input →
      A.time input ≤ C * ⌈(2 : ℝ) ^ (ε * EncodedETHTail.variableCount input)⌉₊ *
        (input.length + 1) ^ d) ∧
  (∀ Φ : ValidFormula, Φ.val.clauses.length ≤ cs * Φ.val.variables → Φ.val.variables < N₁ →
      (EncodedCNF.encode Φ.val ∈ EncodedCNF.Language →
        1 - 1 / 3 ≤ A.prob (EncodedCNF.encode Φ.val) (· = [true])) ∧
      (EncodedCNF.encode Φ.val ∉ EncodedCNF.Language →
        A.prob (EncodedCNF.encode Φ.val) (· = [true]) ≤ 1 / 3)) ∧
  (∀ Φ : ValidFormula, Φ.val.clauses.length ≤ cs * Φ.val.variables → N₁ ≤ Φ.val.variables →
      JoinRealises D B Φ (kOf Φ.val.variables) E A)

theorem sparseDecider_of_join (cs : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12) :
    ∃ N₀ : ℕ, ∀ (E : SelectedTape.Algorithm) (A : ETape.Algorithm),
      EstimatesGrowingSel E c → DeciderAssemblyJoin D B E cs N₀ A → SparseDeciderR20 cs A := by
  obtain ⟨N₀, hN₀⟩ := decider_error_join D B cs c hc0 hc
  refine ⟨N₀, fun E A hE ⟨htime, hsmall, hlarge⟩ => ⟨fun input hwf hsp => ?_, htime⟩⟩
  obtain ⟨Φ, rfl⟩ := hwf
  rw [ADecider.cnfClauseCount_encode, ADecider.variableCount_encode] at hsp
  by_cases hN : Φ.val.variables < N₀
  · exact hsmall Φ hsp hN
  · exact hN₀ Φ hsp (Nat.le_of_not_lt hN) E A hE (hlarge Φ hsp (Nat.le_of_not_lt hN))

/-- **T24 at class level, route B** (`0 ≤ c < 1/12`). -/
theorem T24_class_effective_join (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12)
    (hAsm : ∀ E : SelectedTape.Algorithm, EstimatesGrowingSel E c →
      ∀ cs N₁ : ℕ, ∃ A : ETape.Algorithm, DeciderAssemblyJoin D B E cs N₁ A)
    (hE : ∃ E : SelectedTape.Algorithm, EstimatesGrowingSel E c) :
    ¬ RandomizedSparseETH_R20 := by
  rw [not_R20_iff]
  intro cs
  obtain ⟨E, hEe⟩ := hE
  obtain ⟨N₀, hN₀⟩ := sparseDecider_of_join D B cs c hc0 hc
  obtain ⟨A, hA⟩ := hAsm E hEe cs N₀
  exact ⟨A, hN₀ E A hEe hA⟩

/-- **T03, route B** (`0 < c < 1/12`). -/
theorem T03_class_effective_join (c : ℝ) (hc0 : 0 < c) (hc : c < 1 / 12)
    (hAsm : ∀ E : SelectedTape.Algorithm, EstimatesGrowingSel E c →
      ∀ cs N₁ : ℕ, ∃ A : ETape.Algorithm, DeciderAssemblyJoin D B E cs N₁ A)
    (hE : ∃ E : SelectedTape.Algorithm, EstimatesGrowingSel E c) :
    ¬ RandomizedSparseETH_R20 :=
  T24_class_effective_join D B c hc0.le hc hAsm hE


/-- **T24 at class level in the R20 carrier, final form** (lock v12 `thm:quantitative`,
`06-reduction.tex:107-117`: "Assuming randomized sparse ETH, for every fixed $0\le c<1/12$ there
is no bounded-error randomized algorithm, polynomial in the number $T$ of matrix entries, that
estimates $\D(M)$ with additive error at most $c\,\frac{\log T}{\log\log T}$ on every
sufficiently large explicit Boolean matrix."). From the estimator hypothesis `hE` (R19 carrier,
every decodable word) and the route-B assembly `hAsm` (a whole-decider machine premise in the
R20 carrier, NOT an implementation; it subsumes the front-to-instance BridgeSpec at `k = kOf N`),
randomized sparse ETH fails in the R20 carrier, hence also in the a-eth-owner-1 carrier, the
prefix carrier and the DRAFT shape (D-A2 `EncodedCNF.Language`, D-A6, D-A7 records `D`, `B`). -/
theorem T24_class_effective_final (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12)
    (hAsm : ∀ E : SelectedTape.Algorithm, EstimatesGrowingSel E c →
      ∀ cs N₁ : ℕ, ∃ A : ETape.Algorithm, DeciderAssemblyJoin D B E cs N₁ A)
    (hE : ∃ E : SelectedTape.Algorithm, EstimatesGrowingSel E c) :
    ¬ RandomizedSparseETH_R20 ∧ ¬ Paper2.AEth.RandomizedSparseETH_effective ∧
      ¬ Paper2.AModel.RandomizedSparseETH ∧
      ¬ Paper2.Unit4Shell.Definitions.RandomizedSparseETH EncodedCNF.Language
        Paper2.AModel.WellFormedCNF EncodedETHTail.variableCount Paper2.AModel.cnfClauseCount
        (1 / 3) true := by
  have h := T24_class_effective_join D B c hc0 hc hAsm hE
  exact ⟨h, not_old_of_not_R20 h, not_prefix_of_not_R20 h, not_draft_of_not_R20 h⟩

/-- **T03 at class level in the R20 carrier, final form** (lock v12 `intro:quantitative`:
"Under randomized sparse ETH, for every fixed $0<c<1/12$ there is no bounded-error
polynomial-time estimator of $\D(M)$ with additive error $c\log T/\log\log T$ on every
sufficiently large table."). Same premises, `0 < c`. -/
theorem T03_class_effective_final (c : ℝ) (hc0 : 0 < c) (hc : c < 1 / 12)
    (hAsm : ∀ E : SelectedTape.Algorithm, EstimatesGrowingSel E c →
      ∀ cs N₁ : ℕ, ∃ A : ETape.Algorithm, DeciderAssemblyJoin D B E cs N₁ A)
    (hE : ∃ E : SelectedTape.Algorithm, EstimatesGrowingSel E c) :
    ¬ RandomizedSparseETH_R20 ∧ ¬ Paper2.AEth.RandomizedSparseETH_effective ∧
      ¬ Paper2.AModel.RandomizedSparseETH ∧
      ¬ Paper2.Unit4Shell.Definitions.RandomizedSparseETH EncodedCNF.Language
        Paper2.AModel.WellFormedCNF EncodedETHTail.variableCount Paper2.AModel.cnfClauseCount
        (1 / 3) true :=
  T24_class_effective_final D B c hc0.le hc hAsm hE

/-- **The decider's clock plus the length budget `lenCap`, within the D-A6 budget** (R20; the gloss
"including its length computation" was withdrawn by root decision R22, point 4).
Under the premises of `T24_class_effective_final`, for every density there is an R20 sparse
decider whose clock plus length budget `lenCap` is `≤ C ⌈2^(εN)⌉ (|input|+1)^d` eventually, for
every `ε > 0`. -/
theorem T24_whole_budget (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12)
    (hAsm : ∀ E : SelectedTape.Algorithm, EstimatesGrowingSel E c →
      ∀ cs N₁ : ℕ, ∃ A : ETape.Algorithm, DeciderAssemblyJoin D B E cs N₁ A)
    (hE : ∃ E : SelectedTape.Algorithm, EstimatesGrowingSel E c) (cs : ℕ) :
    ∃ A : ETape.Algorithm, SparseDeciderR20 cs A ∧
      ∀ ε : ℝ, 0 < ε → ∃ C d N₀ : ℕ, ∀ input, Paper2.AModel.WellFormedCNF input →
        Paper2.AModel.cnfClauseCount input ≤ cs * EncodedETHTail.variableCount input →
        N₀ ≤ EncodedETHTail.variableCount input →
        A.lenCap input + A.time input ≤
          C * ⌈(2 : ℝ) ^ (ε * EncodedETHTail.variableCount input)⌉₊ * (input.length + 1) ^ d := by
  obtain ⟨E, hEe⟩ := hE
  obtain ⟨N₀, hN₀⟩ := sparseDecider_of_join D B cs c hc0 hc
  obtain ⟨A, hA⟩ := hAsm E hEe cs N₀
  have hS := hN₀ E A hEe hA
  exact ⟨A, hS, whole_budget cs A hS⟩

end Paper2.AEth2

end

#print axioms Paper2.AEth2.decider_error_join
#print axioms Paper2.AEth2.sparseDecider_of_join
#print axioms Paper2.AEth2.T24_class_effective_join
#print axioms Paper2.AEth2.T03_class_effective_join
#print axioms Paper2.AEth2.T24_class_effective_final
#print axioms Paper2.AEth2.T03_class_effective_final
#print axioms Paper2.AEth2.T24_whole_budget
