import Paper2.ADecider3Class
import Paper2.CNFImagePullback
import Paper2.AEndpoint
import Paper2.AEndpointClass
import Paper2.AModelTapeBridge
import Paper2.AFrontProjection

/-!
# T02 decider, segment 2a: the BRIDGE INTERFACE and the source law on the actual image

Lock v12 `sections/01-introduction.tex:111-126` (`intro:corollary`): "Choose a fixed integer
$k>2a$. ... Accept the source exactly when its estimate is below $B+k/2$."

`BridgeSpec D B hN k` is the ONE named premise standing for the front-to-instance bridge that
lane a-bridge-1 builds in parallel: an image-only selected-tape graph stage
(`ImagePullback.Stage` on the actual all-input CNF graph compiler
`CNFGraphGuard.graphWord D B hN`, which composes the admitted `AFrontRoute`/`AFrontT10` front)
whose printed word, on every selected stage tape, is the canonical encoded instance of the
actual T10 selected experiment at gap `k` read at the prefix of the stage tape. It is a
physical/semantic identity only; no probability, gap or language statement is assumed: the
law below is DERIVED from the admitted finite law (`AEndpoint.t01_no`, `t01_finite_core`) and
the admitted uniform-prefix law (`AModel.experiment_prob_prefix`, `experiment_uniformExact`).
-/

noncomputable section
set_option maxHeartbeats 4000000

namespace Paper2.ADecider3

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2.Unit4Shell.T10Finite

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

/-- The actual T10 selected experiment of the routed formula of the raw CNF word `w`, gap `k`. -/
abbrev expOf {N : ℕ} (hN : 1 ≤ N) (k : ℕ) (w : List Bool) :
    TotalFiniteConstructorScratch.SelectedExperiment :=
  TotalFiniteConstructorScratch.experiment (t10_vertices_pos D B (AFront.T10.routed hN w))
    (CanonicalEdgeTape.graphEdge (t10Graph D B (AFront.T10.routed hN w))
      (t10Graph_valid D B (AFront.T10.routed hN w)))
    B.degreeBound (sourceGap D B) k

/-- The canonical encoded instance printed for experiment tape `t`. -/
abbrev instOf {N : ℕ} (hN : 1 ≤ N) (k : ℕ) (w : List Bool)
    (t : (expOf D B hN k w).output.Tape) : EncodedCommunication.Instance :=
  EncodedSelectedOutput.instanceOf ((expOf D B hN k w).output.table t)
    (expOf D B hN k w).output.budget

/-- **BRIDGE INTERFACE** (premise for lane a-bridge-1; one named structure).
* `stage`: ONE finite machine with fixed natural tape/clock constants, running (with its
  selected monomial clock) on every pair `(graphWord w, tape)` with `tape` of exactly
  `stage.cR * (|graphWord w|+1)^stage.dR` bits, for every raw word `w` (malformed words
  included, routed by the admitted front);
* `bits_le`: the experiment's random-bit count fits in the stage tape;
* `output_eq`: on every selected stage tape `s` and every experiment tape `t` whose tape bits
  are the length-`inputBits` prefix of `s`, the printed word is exactly the canonical
  `encodeInstance` of the selected instance at `t`. -/
structure BridgeSpec {N : ℕ} (hN : 1 ≤ N) (k : ℕ) where
  stage : ImagePullback.Stage (CNFGraphGuard.graphWord D B hN)
  bits_le : ∀ w, (expOf D B hN k w).output.inputBits ≤
    stage.tapeLength (CNFGraphGuard.graphWord D B hN w)
  output_eq : ∀ w (s : Fin (stage.tapeLength (CNFGraphGuard.graphWord D B hN w)) → Bool)
    (t : (expOf D B hN k w).output.Tape),
    (expOf D B hN k w).output.tapeBits t =
      (List.ofFn s).take (expOf D B hN k w).output.inputBits →
    stage.output (CNFGraphGuard.graphWord D B hN w) (List.ofFn s) =
      EncodedCommunication.encodeInstance (instOf D B hN k w t)

/-- Transport of a pointwise statement along `experiment.output = select`. -/
theorem forall_of_output_eq {O S : TotalFiniteConstructorScratch.SelectedOutput} (h : O = S)
    (P : (X : TotalFiniteConstructorScratch.SelectedOutput) → X.Tape → Prop)
    (hS : ∀ t, P S t) : ∀ t, P O t := by
  subst h
  exact hS

/-- Every experiment tape has exactly `inputBits` bits (actual routed T10 image). -/
theorem exp_lengths {N : ℕ} (hN : 1 ≤ N) (k : ℕ) (w : List Bool) :
    ∀ t, ((expOf D B hN k w).output.tapeBits t).length = (expOf D B hN k w).output.inputBits := by
  obtain ⟨hm, _, _, hdeg, hloop, _, _⟩ := t10_source D B (AFront.T10.routed hN w)
  exact forall_of_output_eq
    (TotalFiniteConstructorScratch.experiment_output_eq_select _ _ _ _ _)
    (fun X t => (X.tapeBits t).length = X.inputBits)
    (fun t => (TotalFiniteConstructorScratch.selected_exact_lengths _ _ _ _ k hloop hdeg
      (source_gap_pos D B) B.degreeBound_pos hm t).2)

/-- Surjectivity of the experiment tape bits onto words of length `inputBits`. -/
theorem exp_surj {N : ℕ} (hN : 1 ≤ N) (k : ℕ) (w : List Bool) (u : List Bool)
    (hu : u.length = (expOf D B hN k w).output.inputBits) :
    ∃ t, (expOf D B hN k w).output.tapeBits t = u := by
  obtain ⟨r, hr, _, hsurj, _⟩ := Paper2.AModel.experiment_uniformExact
    (t10_vertices_pos D B (AFront.T10.routed hN w))
    (CanonicalEdgeTape.graphEdge (t10Graph D B (AFront.T10.routed hN w))
      (t10Graph_valid D B (AFront.T10.routed hN w)))
    B.degreeBound (sourceGap D B) k
  obtain ⟨t0⟩ := @FiniteLaw.nonempty _ (expOf D B hN k w).tapeFintype (expOf D B hN k w).tapeLaw
  have hr' : r = (expOf D B hN k w).output.inputBits :=
    (hr t0).symm.trans (exp_lengths D B hN k w t0)
  exact hsurj u (hu.trans hr'.symm)

/-- The experiment law is the uniform prefix law of exactly `inputBits` bits. -/
theorem exp_prefix_law {N : ℕ} (hN : 1 ≤ N) (k : ℕ) (w : List Bool) (R : ℕ)
    (hR : (expOf D B hN k w).output.inputBits ≤ R) (F : List Bool → Prop) :
    @FiniteLaw.prob _ (expOf D B hN k w).tapeFintype (expOf D B hN k w).tapeLaw
        (fun t => F ((expOf D B hN k w).output.tapeBits t)) =
      (Paper2.Unit4Shell.Definitions.uniformTape R).prob
        (fun s => F ((List.ofFn s).take (expOf D B hN k w).output.inputBits)) := by
  obtain ⟨r, hr, hF⟩ := Paper2.AModel.experiment_prob_prefix
    (t10_vertices_pos D B (AFront.T10.routed hN w))
    (CanonicalEdgeTape.graphEdge (t10Graph D B (AFront.T10.routed hN w))
      (t10Graph_valid D B (AFront.T10.routed hN w)))
    B.degreeBound (sourceGap D B) k
  obtain ⟨t0⟩ := @FiniteLaw.nonempty _ (expOf D B hN k w).tapeFintype (expOf D B hN k w).tapeLaw
  have hr' : r = (expOf D B hN k w).output.inputBits :=
    (hr t0).symm.trans (exp_lengths D B hN k w t0)
  subst hr'
  exact hF R hR F

private def padFn (u : List Bool) (L : ℕ) : Fin L → Bool := fun i => (u.getD i.val false)

private theorem take_padFn (u : List Bool) (L : ℕ) (hu : u.length ≤ L) :
    (List.ofFn (padFn u L)).take u.length = u := by
  apply List.ext_getElem
  · simp [hu]
  · intro i h1 h2
    simp [padFn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-- **Stage law = experiment law** for every output event, on every raw word. -/
theorem stage_law {N : ℕ} (hN : 1 ≤ N) (k : ℕ) (S : BridgeSpec D B hN k)
    (w : List Bool) (E : List Bool → Prop) :
    (Paper2.Unit4Shell.Definitions.uniformTape
        (S.stage.tapeLength (CNFGraphGuard.graphWord D B hN w))).prob
      (fun s => E (S.stage.output (CNFGraphGuard.graphWord D B hN w) (List.ofFn s))) =
    @FiniteLaw.prob _ (expOf D B hN k w).tapeFintype (expOf D B hN k w).tapeLaw
      (fun t => E (EncodedCommunication.encodeInstance (instOf D B hN k w t))) := by
  classical
  let e := expOf D B hN k w
  let r := e.output.inputBits
  let L := S.stage.tapeLength (CNFGraphGuard.graphWord D B hN w)
  have hrL : r ≤ L := S.bits_le w
  let G : List Bool → Prop := fun u =>
    ∃ t, e.output.tapeBits t = u ∧ E (EncodedCommunication.encodeInstance (instOf D B hN k w t))
  have hleft : ∀ s : Fin L → Bool,
      E (S.stage.output (CNFGraphGuard.graphWord D B hN w) (List.ofFn s)) ↔
        G ((List.ofFn s).take r) := by
    intro s
    have hlen : ((List.ofFn s).take r).length = r := by simp [hrL]
    obtain ⟨t, ht⟩ := exp_surj D B hN k w _ hlen
    constructor
    · intro hE
      refine ⟨t, ht, ?_⟩
      rw [← S.output_eq w s t ht]
      exact hE
    · rintro ⟨t', ht', hE⟩
      rw [S.output_eq w s t' ht']
      exact hE
  have hright : ∀ t, G (e.output.tapeBits t) ↔
      E (EncodedCommunication.encodeInstance (instOf D B hN k w t)) := by
    intro t
    constructor
    · rintro ⟨t', ht', hE⟩
      have hlt : (e.output.tapeBits t).length ≤ L := by
        rw [exp_lengths D B hN k w t]; exact hrL
      let s := padFn (e.output.tapeBits t) L
      have hs : (List.ofFn s).take r = e.output.tapeBits t := by
        have h := take_padFn (e.output.tapeBits t) L hlt
        rwa [exp_lengths D B hN k w t] at h
      have h1 := S.output_eq w s t hs.symm
      have h2 := S.output_eq w s t' (ht'.trans hs.symm)
      rw [← h1, h2]
      exact hE
    · intro hE
      exact ⟨t, rfl, hE⟩
  calc
    _ = (Paper2.Unit4Shell.Definitions.uniformTape L).prob
          (fun s => G ((List.ofFn s).take r)) := by
        congr 1
        funext s
        exact propext (hleft s)
    _ = @FiniteLaw.prob _ e.tapeFintype e.tapeLaw (fun t => G (e.output.tapeBits t)) :=
        (exp_prefix_law D B hN k w L hrL G).symm
    _ = _ := by
        congr 1
        funext t
        exact propext (hright t)

/-- YES side of the admitted finite law on the actual routed image: on every experiment tape
`D(M) ≤ B`. -/
theorem exp_yes {N : ℕ} (hN : 1 ≤ N) (k : ℕ) (hk : 1 ≤ k) (w : List Bool)
    (hw : w ∈ EncodedCNF.Language) :
    ∀ t, Workspace.Types.CommComplexity.D ((expOf D B hN k w).output.table t).matrix ≤
      (expOf D B hN k w).output.budget := by
  have hsat : EncodedCNF.Satisfiable (AFront.T10.routed hN w).val :=
    (AFront.Route.routedFormula_sat_iff hN w).mpr hw
  have hcore := (t01_finite_core D B (AFront.T10.routed hN w) k hk).1 hsat
  exact forall_of_output_eq
    (TotalFiniteConstructorScratch.experiment_output_eq_select _ _ _ _ _)
    (fun X t => Workspace.Types.CommComplexity.D (X.table t).matrix ≤ X.budget)
    (fun t => (EncodedSelectedOutput.outputBits_language_iff _ _ _ _ _ t).mp (hcore t))

/-- NO side of the admitted finite law on the actual routed image (`AEndpoint.t01_no`). -/
theorem exp_no {N : ℕ} (hN : 1 ≤ N) (k : ℕ) (hk : 1 ≤ k) (w : List Bool)
    (hw : w ∉ EncodedCNF.Language) :
    (981 / 1000 : ℝ) ≤ @FiniteLaw.prob _ (expOf D B hN k w).tapeFintype
      (expOf D B hN k w).tapeLaw
      (fun t => (expOf D B hN k w).output.budget + k ≤
        Workspace.Types.CommComplexity.D ((expOf D B hN k w).output.table t).matrix) := by
  have hnot : EncodedCNF.encode (AFront.T10.routed hN w).val ∉ EncodedCNF.Language := by
    intro h
    exact hw ((AFront.Route.routedFormula_sat_iff hN w).mp
      ((Paper2.AEndpoint.DA2_recommended _).mp h))
  exact Paper2.AEndpoint.t01_no D B EncodedCNF.Language Paper2.AEndpoint.DA2_recommended
    (AFront.T10.routed hN w) k hk hnot

end Paper2.ADecider3

#print axioms Paper2.ADecider3.stage_law
#print axioms Paper2.ADecider3.exp_yes
#print axioms Paper2.ADecider3.exp_no
