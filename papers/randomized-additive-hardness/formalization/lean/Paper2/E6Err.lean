import Paper2.E6Join

-- a-eth-owner-6 module E6Err: the error transfer of frozen a-eth-owner-2 `E2Join.decider_error_join`
-- (SHA-256 of E2Join.lean f54cfb7bbf499b7750a6f03a995e88c70097dcf3bf698ca32adc9eb411d4f060, lines 75-176) generalised to `JoinRealisesAt` (input word separated from the formula).

noncomputable section

namespace Paper2.AEth6

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2 Paper2.FiniteLaw Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics
open Paper2.Unit4Shell.Definitions (uniformTape)
open Paper2.AEth Paper2.AEth2

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

set_option hygiene false in
local notation "EXP" Φ:max k:max => TotalFiniteConstructorScratch.experiment (t10_vertices_pos D B Φ)
  (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) B.degreeBound (sourceGap D B) k

set_option maxHeartbeats 2000000 in
/-- a-eth-owner-6: `decider_error_join` of frozen a-eth-owner-2 `E2Join.lean` with the input word `x` separated from the formula `Φ` (`JoinRealisesAt`); proof text verbatim except `encode Φ.val` -> `x` in the probability and the tape type. Original docstring: **Route B, segment 4.** Error `≤ 1/3` (in fact `≥ 99/100` / `≤ 29/1000`) for every effective
decider realising the route-B identity at `k = kOf N`, sparse valid `Φ`, `N ≥ N₀`. -/
theorem decider_error_joinAt (cs : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12) :
    ∃ N₀ : ℕ, ∀ Φ : ValidFormula, Φ.val.clauses.length ≤ cs * Φ.val.variables →
      N₀ ≤ Φ.val.variables → ∀ (E : SelectedTape.Algorithm) (A : ETape.Algorithm) (x : List Bool),
      EstimatesGrowingSel E c → Paper2.AEth5.JoinRealisesAt D B x Φ (kOf Φ.val.variables) E A →
      (EncodedCNF.encode Φ.val ∈ EncodedCNF.Language →
        1 - 1 / 3 ≤ A.prob x (· = [true])) ∧
      (EncodedCNF.encode Φ.val ∉ EncodedCNF.Language →
        A.prob x (· = [true]) ≤ 1 / 3) := by
  obtain ⟨N₀, hN₀⟩ := classifier_per_tape D B cs c hc0 hc
  refine ⟨max N₀ 36, fun Φ hsp hN E A x hE hJ => ?_⟩
  have hN0 : N₀ ≤ Φ.val.variables := le_trans (le_max_left _ _) hN
  have h36 : 36 ≤ Φ.val.variables := le_trans (le_max_right _ _) hN
  have hk1 : 1 ≤ kOf Φ.val.variables := Paper2.Unit4Shell.AsymptoticsExplicit.kOf_pos _ h36
  letI : Fintype (EXP Φ (kOf Φ.val.variables)).output.Tape :=
    (EXP Φ (kOf Φ.val.variables)).tapeFintype
  obtain ⟨s, π, hs, hpush, hout⟩ := hJ
  have hper := hN₀ Φ hsp hN0 E hE
  -- the decider law is the two-stage law
  have key : ∀ Ev : List Bool → Prop,
      A.prob x Ev =
        ((EXP Φ (kOf Φ.val.variables)).tapeLaw.prod (uniformTape s)).prob
          (fun x => Ev ((Paper2.HeaderStrip.selectedClassifier E).output (headerWord D B Φ (kOf Φ.val.variables) x.1) (List.ofFn x.2))) := by
    intro Ev
    unfold ETape.Algorithm.prob
    have e : (fun t : Fin (A.tapeLen x.length) → Bool =>
        Ev (A.output x (List.ofFn t))) =
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


end Paper2.AEth6

end

#print axioms Paper2.AEth6.decider_error_joinAt
