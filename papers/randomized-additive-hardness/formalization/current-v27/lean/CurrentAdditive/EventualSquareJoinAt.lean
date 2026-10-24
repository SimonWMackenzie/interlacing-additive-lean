import CurrentAdditive.EventualClassifier
import Paper2.E7SqErr

/-! Private square routed-input probability transfer. Adapted from the
existing `E7SqErr.decider_error_joinAt_sq` proof, changing only the estimator
size domain and per-tape input. -/

noncomputable section
namespace CurrentAdditive.Eventual

open Paper2

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
theorem decider_error_joinAt_square_eventual (cs : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12)
    (E : SelectedTape.Algorithm) (hE : EstimatesGrowingEventuallySelSq E c) :
    ∃ N₀ : ℕ, ∀ Φ : ValidFormula, Φ.val.clauses.length ≤ cs * Φ.val.variables →
      N₀ ≤ Φ.val.variables → ∀ (A : ETape.Algorithm) (x : List Bool),
      Paper2.AEth7.JoinRealisesSqAt D B x Φ (kOf Φ.val.variables) E A →
      (EncodedCNF.encode Φ.val ∈ EncodedCNF.Language →
        1 - 1 / 3 ≤ A.prob x (· = [true])) ∧
      (EncodedCNF.encode Φ.val ∉ EncodedCNF.Language →
        A.prob x (· = [true]) ≤ 1 / 3) := by
  obtain ⟨N₀, hN₀⟩ := classifier_per_tape_square_eventual D B cs c hc0 hc E hE
  refine ⟨max N₀ 36, fun Φ hsp hN A x hJ => ?_⟩
  have hN0 : N₀ ≤ Φ.val.variables := le_trans (le_max_left _ _) hN
  have h36 : 36 ≤ Φ.val.variables := le_trans (le_max_right _ _) hN
  have hk1 : 1 ≤ kOf Φ.val.variables := Paper2.Unit4Shell.AsymptoticsExplicit.kOf_pos _ h36
  letI : Fintype (EXP Φ (kOf Φ.val.variables)).output.Tape :=
    (EXP Φ (kOf Φ.val.variables)).tapeFintype
  obtain ⟨s, π, hs, hpush, hout⟩ := hJ
  have hper := hN₀ Φ hsp hN0
  -- the decider law is the two-stage law
  have key : ∀ Ev : List Bool → Prop,
      A.prob x Ev =
        ((EXP Φ (kOf Φ.val.variables)).tapeLaw.prod (uniformTape s)).prob
          (fun x => Ev ((Paper2.HeaderStrip.selectedClassifier E).output (headerWordSq D B Φ (kOf Φ.val.variables) x.1) (List.ofFn x.2))) := by
    intro Ev
    unfold ETape.Algorithm.prob
    have e : (fun t : Fin (A.tapeLen x.length) → Bool =>
        Ev (A.output x (List.ofFn t))) =
        (fun t => (fun x : (EXP Φ (kOf Φ.val.variables)).output.Tape × (Fin s → Bool) =>
          Ev ((Paper2.HeaderStrip.selectedClassifier E).output (headerWordSq D B Φ (kOf Φ.val.variables) x.1) (List.ofFn x.2))) (π t)) := by
      funext t; rw [hout t]
    rw [e]
    exact hpush (fun x => Ev ((Paper2.HeaderStrip.selectedClassifier E).output (headerWordSq D B Φ (kOf Φ.val.variables) x.1) (List.ofFn x.2)))
  -- the second stage is the classifier law
  have perb : ∀ b (Ev : List Bool → Prop),
      (uniformTape s).prob (fun y => Ev ((Paper2.HeaderStrip.selectedClassifier E).output (headerWordSq D B Φ (kOf Φ.val.variables) b) (List.ofFn y))) =
        (Paper2.HeaderStrip.selectedClassifier E).prob (headerWordSq D B Φ (kOf Φ.val.variables) b) Ev := by
    intro b Ev
    unfold SelectedTape.Algorithm.prob
    exact (Paper2.AModel.uniformTape_prob_ofFn_congr (hs b) (fun w => Ev ((Paper2.HeaderStrip.selectedClassifier E).output (headerWordSq D B Φ (kOf Φ.val.variables) b) w))).symm
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
        (uniformTape s).prob (fun y => ¬ ((Paper2.HeaderStrip.selectedClassifier E).output (headerWordSq D B Φ (kOf Φ.val.variables) a) (List.ofFn y) = [true])) ≤ 1 / 100 := by
      intro a _
      have hn := Paper2.Unit4Shell.Amplification.prob_not (uniformTape s) (fun y => (Paper2.HeaderStrip.selectedClassifier E).output (headerWordSq D B Φ (kOf Φ.val.variables) a) (List.ofFn y) = [true])
      have hp := perb a (· = [true])
      have := (hper a).1 (hyes a)
      linarith
    have hrej := FiniteLaw.two_stage_failure_le (EXP Φ (kOf Φ.val.variables)).tapeLaw
      (uniformTape s) (fun _ => True)
      (fun a y => ¬ ((Paper2.HeaderStrip.selectedClassifier E).output (headerWordSq D B Φ (kOf Φ.val.variables) a) (List.ofFn y) = [true])) 0 (1 / 100) hfirst hsecond
      (by norm_num)
    have hcomp := Paper2.Unit4Shell.Amplification.prob_not ((EXP Φ (kOf Φ.val.variables)).tapeLaw.prod (uniformTape s))
      (fun x => (Paper2.HeaderStrip.selectedClassifier E).output (headerWordSq D B Φ (kOf Φ.val.variables) x.1) (List.ofFn x.2) = [true])
    have hacc := key (· = [true])
    rw [hacc]
    have hrej2 : ((EXP Φ (kOf Φ.val.variables)).tapeLaw.prod (uniformTape s)).prob
        (fun x => ¬ ((Paper2.HeaderStrip.selectedClassifier E).output (headerWordSq D B Φ (kOf Φ.val.variables) x.1) (List.ofFn x.2) = [true])) ≤ 0 + 1 / 100 := hrej
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
        (uniformTape s).prob (fun y => (Paper2.HeaderStrip.selectedClassifier E).output (headerWordSq D B Φ (kOf Φ.val.variables) a) (List.ofFn y) = [true]) ≤ 1 / 100 := by
      intro a ha
      have hp := perb a (· = [true])
      have := (hper a).2 ha
      linarith
    have hacc := FiniteLaw.two_stage_failure_le (EXP Φ (kOf Φ.val.variables)).tapeLaw
      (uniformTape s)
      (fun a => (EXP Φ (kOf Φ.val.variables)).output.budget + kOf Φ.val.variables ≤
          Workspace.Types.CommComplexity.D ((EXP Φ (kOf Φ.val.variables)).output.table a).matrix)
      (fun a y => (Paper2.HeaderStrip.selectedClassifier E).output (headerWordSq D B Φ (kOf Φ.val.variables) a) (List.ofFn y) = [true]) (19 / 1000) (1 / 100) hfirst hsecond
      (by norm_num)
    rw [key (· = [true])]
    have hacc2 : ((EXP Φ (kOf Φ.val.variables)).tapeLaw.prod (uniformTape s)).prob
        (fun x => (Paper2.HeaderStrip.selectedClassifier E).output (headerWordSq D B Φ (kOf Φ.val.variables) x.1) (List.ofFn x.2) = [true]) ≤ 19 / 1000 + 1 / 100 := hacc
    linarith


#print axioms decider_error_joinAt_square_eventual

end CurrentAdditive.Eventual
