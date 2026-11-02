import Paper2.ADecider3Decider
import Paper2.HA3Endpoints

/-!
# T02 deterministic clause, segment 1: the SAME composed decider is one-sided under an
# always-correct estimator (lane owner:a-decider-4, Paper A, selected-tape carrier R19)

Lock v12 `sections/01-introduction.tex:111-126` (`intro:corollary` and proof), quoted:
"For every fixed $a\ge0$, a bounded-error polynomial-time additive-error-$a$ estimator for
$\D$ implies $\NP\subseteq\BPP$. An always-correct deterministic polynomial-time estimator also
implies $\NP=\coNP$. ... If the estimator is always correct, the composed algorithm never
rejects a satisfiable formula and rejects an unsatisfiable one with constant probability.
Hence $\SAT\in\coRP\subseteq\coNP$ and $\NP=\coNP$."

The decider is EXACTLY lane a-decider-3's `ADecider3.decider` (frozen object, hash-verified):
front `CNFGraphGuard.graphWord`, bridge stage (`BridgeSpec`, premise), fixed-gap header, the
two-stage bind and `HeaderStrip.selectedClassifier E`. No new machine is introduced here.

* Pointwise classifier: the classifier's printed word on EVERY selected tape is
  `[decide (MajBelow decodeDyadic runs thrW)]` (`MedianOwner.Final.medOutput`), each run is the
  estimator on the stripped matrix word and a prefix of its segment (`selectedEstimator_output`),
  so under `EstimatesDExact` every run is within `a` of `D`.
* YES: on every decider tape the printed word is `[true]` (exp_yes pointwise + midpoint).
* NO: acceptance probability `≤ 2^-11`, from the admitted deterministic clause of
  `A3CloseEndpoints.T02_law_final` (applied to the exact estimate `e b := D b - a`).
-/

noncomputable section
set_option maxHeartbeats 4000000

namespace Paper2.ADecider4

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2.Unit4Shell.T10Finite
open Paper2.ADecider3
open Paper2.MedianOwner (Below MajBelow)

/-- A list of length `m` is `List.ofFn` of a function on `Fin m`. -/
theorem exists_ofFn (l : List Bool) (m : ℕ) (h : l.length = m) :
    ∃ t : Fin m → Bool, List.ofFn t = l := by
  subst h
  exact ⟨l.get, List.ofFn_get l⟩

/-! ## The selected classifier on every tape -/

/-- The classifier's selected tape is `reps` copies of the strip-estimator tape. -/
theorem classifier_tapeLength (E : SelectedTape.Algorithm) (w : List Bool) :
    (HeaderStrip.selectedClassifier E).tapeLength w =
      (146 + 1) * (HeaderStrip.selectedEstimator E).toPrefix.tapeLength w.length := by
  have hR : ∃ cR dR : ℕ, ∀ n, (HeaderStrip.selectedMedianDecision E).tapeLength n =
      cR * (n + 1) ^ dR :=
    ⟨_, _, HeaderStrip.selectedMedianDecision_tapeLength E⟩
  have h := Classical.choose_spec (Classical.choose_spec hR) w.length
  have h2 : (HeaderStrip.selectedClassifier E).tapeLength w =
      Classical.choose hR * (w.length + 1) ^ Classical.choose (Classical.choose_spec hR) := rfl
  rw [h2, ← h, HeaderStrip.selectedMedianDecision_tapeLength]
  change _ = (146 + 1) * ((HeaderStrip.selectedEstimator E).cR *
    (w.length + 1) ^ (HeaderStrip.selectedEstimator E).dR)
  rw [show (Paper2.Unit4Shell.Amplification.reps : ℕ) = 146 + 1 from rfl]
  ring

/-- The classifier's printed word on every tape (definitional). -/
theorem classifier_output (E : SelectedTape.Algorithm) (w tape : List Bool) :
    (HeaderStrip.selectedClassifier E).output w tape =
      Paper2.MedianOwner.Final.medOutput ((HeaderStrip.selectedEstimator E).toPrefix)
        Paper2.CmpOwner.thrW w tape := rfl

/-- Under an always-correct estimator, one strip-estimator run on a header-prefixed word, on
any tape at least as long as its selected tape, prints a dyadic within `a` of `D`. -/
theorem run_exact (E : SelectedTape.Algorithm) (a : ℝ) (hE : EstimatesDExact E a)
    (n : ℕ) (rest : List Bool) (c : ℕ) (hc : Paper2.AModel.targetD rest = some c)
    (tape : List Bool)
    (hlen : (HeaderStrip.selectedEstimator E).tapeLength
      (EncodedCommunication.natField n ++ rest) ≤ tape.length) :
    ∃ v, Paper2.AModel.decodeDyadic ((HeaderStrip.selectedEstimator E).output
      (EncodedCommunication.natField n ++ rest) tape) = some v ∧ |v - c| ≤ a := by
  rw [HeaderStrip.selectedEstimator_output]
  have hin : E.tapeLength rest ≤ (HeaderStrip.selectedEstimator E).tapeLength
      (EncodedCommunication.natField n ++ rest) := by
    have := SelectedTape.inner_le_outer HeaderStrip.strip HeaderStrip.polytime E
      (EncodedCommunication.natField n ++ rest)
    rw [HeaderStrip.strip_natField] at this
    exact this
  obtain ⟨t, ht⟩ := exists_ofFn (tape.take (E.tapeLength rest)) (E.tapeLength rest)
    (by rw [List.length_take]; omega)
  rw [← ht]
  exact hE rest c hc t

/-- Every run of the classifier on a selected tape is a full-length segment. -/
theorem classifier_run_exact (E : SelectedTape.Algorithm) (a : ℝ) (hE : EstimatesDExact E a)
    (n : ℕ) (rest : List Bool) (c : ℕ) (hc : Paper2.AModel.targetD rest = some c)
    (t : Fin ((HeaderStrip.selectedClassifier E).tapeLength
      (EncodedCommunication.natField n ++ rest)) → Bool)
    (i : Fin Paper2.Unit4Shell.Amplification.reps) :
    ∃ v, Paper2.AModel.decodeDyadic ((HeaderStrip.selectedEstimator E).toPrefix.output
      (EncodedCommunication.natField n ++ rest)
      (Paper2.MedianOwner.Final.chunk
        ((HeaderStrip.selectedEstimator E).toPrefix.tapeLength
          (EncodedCommunication.natField n ++ rest).length) i (List.ofFn t))) = some v ∧
      |v - c| ≤ a := by
  have hL : (List.ofFn t).length = (146 + 1) *
      (HeaderStrip.selectedEstimator E).toPrefix.tapeLength
        (EncodedCommunication.natField n ++ rest).length := by
    rw [List.length_ofFn, classifier_tapeLength]
  have hi : i.val ≤ 146 := by
    have := i.isLt
    change i.val < 147 at this
    omega
  have hch := Paper2.MedianOwner.Final.chunk_length _ 146 i.val _ hL hi
  exact run_exact E a hE n rest c hc _ (le_of_eq hch.symm)

/-- **Pointwise classifier, YES side**: under an always-correct estimator, on a word
`natField (2B+k) ++ rest` with `D(rest) = c ≤ B` and `2a < k`, the classifier prints `[true]`
on EVERY selected tape. -/
theorem classifier_every_tape_yes (E : SelectedTape.Algorithm) (a : ℝ)
    (hE : EstimatesDExact E a) (rest : List Bool) (c B k : ℕ)
    (htarget : Paper2.AModel.targetD rest = some c) (hk : 2 * a < k) (hcB : c ≤ B)
    (t : Fin ((HeaderStrip.selectedClassifier E).tapeLength
      (EncodedCommunication.natField (2 * B + k) ++ rest)) → Bool) :
    (HeaderStrip.selectedClassifier E).output
      (EncodedCommunication.natField (2 * B + k) ++ rest) (List.ofFn t) = [true] := by
  classical
  rw [classifier_output]
  unfold Paper2.MedianOwner.Final.medOutput
  simp only [List.cons.injEq, and_true, decide_eq_true_eq]
  rw [Paper2.CmpOwner.thrW_midpoint]
  have hall : ∀ i : Fin Paper2.Unit4Shell.Amplification.reps,
      Below Paper2.AModel.decodeDyadic ((B : ℝ) + (k : ℝ) / 2)
        ((HeaderStrip.selectedEstimator E).toPrefix.output
          (EncodedCommunication.natField (2 * B + k) ++ rest)
          (Paper2.MedianOwner.Final.chunk
            ((HeaderStrip.selectedEstimator E).toPrefix.tapeLength
              (EncodedCommunication.natField (2 * B + k) ++ rest).length) i
            (List.ofFn t))) := by
    intro i
    obtain ⟨v, hv, hva⟩ := classifier_run_exact E a hE (2 * B + k) rest c htarget t i
    refine ⟨v, hv, ?_⟩
    have hcB' : (c : ℝ) ≤ B := by exact_mod_cast hcB
    have := (abs_le.mp hva).2
    linarith
  unfold MajBelow
  have hcard : Fintype.card {i : Fin Paper2.Unit4Shell.Amplification.reps //
      Below Paper2.AModel.decodeDyadic ((B : ℝ) + (k : ℝ) / 2)
        ((HeaderStrip.selectedEstimator E).toPrefix.output
          (EncodedCommunication.natField (2 * B + k) ++ rest)
          (Paper2.MedianOwner.Final.chunk
            ((HeaderStrip.selectedEstimator E).toPrefix.tapeLength
              (EncodedCommunication.natField (2 * B + k) ++ rest).length) i
            (List.ofFn t)))} = Paper2.Unit4Shell.Amplification.reps := by
    rw [Fintype.card_subtype]
    rw [Finset.filter_true_of_mem (fun i _ => hall i)]
    simp
  rw [hcard]
  change 147 < 2 * 147
  norm_num

/-- **Pointwise classifier, NO side**: if `B + k/2 < c - a` then the classifier prints
`[false]` (in particular not `[true]`) on EVERY selected tape. -/
theorem classifier_every_tape_no (E : SelectedTape.Algorithm) (a : ℝ)
    (hE : EstimatesDExact E a) (rest : List Bool) (c B k : ℕ)
    (htarget : Paper2.AModel.targetD rest = some c)
    (hgap : (B : ℝ) + (k : ℝ) / 2 < (c : ℝ) - a)
    (t : Fin ((HeaderStrip.selectedClassifier E).tapeLength
      (EncodedCommunication.natField (2 * B + k) ++ rest)) → Bool) :
    (HeaderStrip.selectedClassifier E).output
      (EncodedCommunication.natField (2 * B + k) ++ rest) (List.ofFn t) ≠ [true] := by
  classical
  rw [classifier_output]
  unfold Paper2.MedianOwner.Final.medOutput
  simp only [ne_eq, List.cons.injEq, and_true, decide_eq_true_eq]
  rw [Paper2.CmpOwner.thrW_midpoint]
  have hnone : ∀ i : Fin Paper2.Unit4Shell.Amplification.reps,
      ¬ Below Paper2.AModel.decodeDyadic ((B : ℝ) + (k : ℝ) / 2)
        ((HeaderStrip.selectedEstimator E).toPrefix.output
          (EncodedCommunication.natField (2 * B + k) ++ rest)
          (Paper2.MedianOwner.Final.chunk
            ((HeaderStrip.selectedEstimator E).toPrefix.tapeLength
              (EncodedCommunication.natField (2 * B + k) ++ rest).length) i
            (List.ofFn t))) := by
    intro i
    obtain ⟨v, hv, hva⟩ := classifier_run_exact E a hE (2 * B + k) rest c htarget t i
    rintro ⟨v', hv', hlt⟩
    rw [hv] at hv'
    cases hv'
    have := (abs_le.mp hva).1
    linarith
  unfold MajBelow
  have hcard : Fintype.card {i : Fin Paper2.Unit4Shell.Amplification.reps //
      Below Paper2.AModel.decodeDyadic ((B : ℝ) + (k : ℝ) / 2)
        ((HeaderStrip.selectedEstimator E).toPrefix.output
          (EncodedCommunication.natField (2 * B + k) ++ rest)
          (Paper2.MedianOwner.Final.chunk
            ((HeaderStrip.selectedEstimator E).toPrefix.tapeLength
              (EncodedCommunication.natField (2 * B + k) ++ rest).length) i
            (List.ofFn t)))} = 0 := by
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun x => hnone x.1 x.2⟩
  rw [hcard]
  change ¬ (147 < 2 * 0)
  norm_num

/-! ## The composed decider on every tape -/

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

/-- Every selected tape of the source algorithm prints a headered selected instance. -/
theorem sourceAlg_every_tape {N : ℕ} (hN : 1 ≤ N) (k : ℕ) (hk : 0 < k)
    (S : BridgeSpec D B hN k) (w : List Bool)
    (f : Fin ((sourceAlg D B hN k hk S).tapeLength w) → Bool) :
    ∃ t : (expOf D B hN k w).output.Tape,
      (sourceAlg D B hN k hk S).output w (List.ofFn f) =
        HeaderWordRun.headeredWord k (instOf D B hN k w t) := by
  have hlen : S.stage.tapeLength (CNFGraphGuard.graphWord D B hN w) ≤ (List.ofFn f).length := by
    rw [List.length_ofFn]
    exact ImagePullback.inner_le_outer (CNFGraphGuard.graphWord_polytime D B hN)
      (headerStage D B hN k hk S) w
  obtain ⟨s, hs⟩ := exists_ofFn
    ((List.ofFn f).take (S.stage.tapeLength (CNFGraphGuard.graphWord D B hN w)))
    (S.stage.tapeLength (CNFGraphGuard.graphWord D B hN w))
    (by rw [List.length_take]; omega)
  obtain ⟨t, ht⟩ := stage_output_inst D B hN k S w s
  refine ⟨t, ?_⟩
  change headerOut k (S.stage.output (CNFGraphGuard.graphWord D B hN w)
      ((List.ofFn f).take (S.stage.tapeLength (CNFGraphGuard.graphWord D B hN w)))) = _
  rw [← hs, ht, headerOut_instOf]

/-- The decider's printed word on every tape is the classifier's word on the source's printed
word, both read at full-length selected tapes. -/
theorem decider_every_tape_split {N : ℕ} (hN : 1 ≤ N) (k : ℕ) (hk : 0 < k)
    (S : BridgeSpec D B hN k) (E : SelectedTape.Algorithm) (w : List Bool)
    (t : Fin ((decider D B hN k hk S E).tapeLength w) → Bool) :
    ∃ (f : Fin ((sourceAlg D B hN k hk S).tapeLength w) → Bool)
      (g : Fin ((HeaderStrip.selectedClassifier E).tapeLength
        ((sourceAlg D B hN k hk S).output w (List.ofFn f))) → Bool),
      (decider D B hN k hk S E).output w (List.ofFn t) =
        (HeaderStrip.selectedClassifier E).output
          ((sourceAlg D B hN k hk S).output w (List.ofFn f)) (List.ofFn g) := by
  have houter : (List.ofFn t).length =
      SelectedTape.Bind.outerLength (sourceAlg D B hN k hk S)
        (HeaderStrip.selectedClassifier E) w.length := by
    rw [List.length_ofFn]; rfl
  have hsum := SelectedTape.Bind.source_plus_suffix (sourceAlg D B hN k hk S)
    (HeaderStrip.selectedClassifier E) w.length
  obtain ⟨f, hf⟩ := exists_ofFn
    ((List.ofFn t).take ((sourceAlg D B hN k hk S).tapeLength w))
    ((sourceAlg D B hN k hk S).tapeLength w)
    (by
      rw [List.length_take, houter]
      unfold SelectedTape.Algorithm.tapeLength
      omega)
  have hsuf := SelectedTape.Bind.classifier_le_suffix (sourceAlg D B hN k hk S)
    (HeaderStrip.selectedClassifier E) w f
  obtain ⟨g, hg⟩ := exists_ofFn
    (((List.ofFn t).drop ((sourceAlg D B hN k hk S).tapeLength w)).take
      ((HeaderStrip.selectedClassifier E).tapeLength
        ((sourceAlg D B hN k hk S).output w (List.ofFn f))))
    ((HeaderStrip.selectedClassifier E).tapeLength
        ((sourceAlg D B hN k hk S).output w (List.ofFn f)))
    (by
      rw [List.length_take, List.length_drop, houter]
      unfold SelectedTape.Algorithm.tapeLength at *
      unfold SelectedTape.Bind.suffixLength at hsuf
      omega)
  refine ⟨f, g, ?_⟩
  change SelectedTape.Bind.mixedOutput (sourceAlg D B hN k hk S)
    (HeaderStrip.selectedClassifier E) w
    ((List.ofFn t).take ((sourceAlg D B hN k hk S).tapeLength w))
    ((List.ofFn t).drop ((sourceAlg D B hN k hk S).tapeLength w)) = _
  unfold SelectedTape.Bind.mixedOutput
  rw [← hf, hg]

/-- **Segment 1, YES side**: under an always-correct estimator the composed decider prints
`[true]` on EVERY selected tape of every satisfiable word ("never rejects a satisfiable
formula"). -/
theorem decider_every_tape_yes {N : ℕ} (hN : 1 ≤ N) (k : ℕ) (hk : 0 < k)
    (S : BridgeSpec D B hN k) (E : SelectedTape.Algorithm) (a : ℝ)
    (hE : EstimatesDExact E a) (hka : 2 * a < k) (w : List Bool)
    (hw : w ∈ EncodedCNF.Language)
    (t : Fin ((decider D B hN k hk S E).tapeLength w) → Bool) :
    (decider D B hN k hk S E).output w (List.ofFn t) = [true] := by
  obtain ⟨f, g, hfg⟩ := decider_every_tape_split D B hN k hk S E w t
  rw [hfg]
  have hgood : ∀ y, (∃ i : EncodedCommunication.Instance, ∃ c : ℕ,
      y = HeaderWordRun.headeredWord k i ∧
        Paper2.AModel.targetD (HeaderWordRun.matrix i) = some c ∧ c ≤ i.threshold) →
      ∀ g' : Fin ((HeaderStrip.selectedClassifier E).tapeLength y) → Bool,
        (HeaderStrip.selectedClassifier E).output y (List.ofFn g') = [true] := by
    rintro y ⟨i, c, rfl, hc, hcB⟩ g'
    exact classifier_every_tape_yes E a hE (HeaderWordRun.matrix i) c i.threshold k hc hka hcB g'
  apply hgood
  obtain ⟨t', ht'⟩ := sourceAlg_every_tape D B hN k hk S w f
  exact ⟨instOf D B hN k w t', _, ht', targetD_instOf D B hN k w t',
    exp_yes D B hN k (by omega) w hw t'⟩

theorem gapPos (a : ℝ) (ha : 0 ≤ a) : 0 < Paper2.AEndpoint.gapOf a := by
  have := (Paper2.AEndpoint.gapOf_spec a ha).1
  omega

private theorem prob_le_zero_of_forall_not {α : Type} (inst : Fintype α)
    (μ : @FiniteLaw α inst) (P : α → Prop) (h : ∀ x, ¬ P x) :
    @FiniteLaw.prob α inst μ P ≤ 0 := by
  have := @FiniteLaw.prob_mono α inst μ P (fun _ => False) (fun x hx => h x hx)
  rw [@FiniteLaw.prob_false α inst μ] at this
  exact this

/-- **Segment 1, NO side**: at the proof's gap `k = gapOf a`, under an always-correct
estimator the composed decider rejects every unsatisfiable word with probability at least
`1 - 2^-11` (reduction failure `≤ 2^-11` from the admitted deterministic clause of
`T02_law_final`; the classifier never errs on a good NO outcome). -/
theorem decider_no_exact {N : ℕ} (hN : 1 ≤ N) (a : ℝ) (ha : 0 ≤ a)
    (S : BridgeSpec D B hN (Paper2.AEndpoint.gapOf a)) (E : SelectedTape.Algorithm)
    (hE : EstimatesDExact E a) (w : List Bool) (hw : w ∉ EncodedCNF.Language) :
    1 - (1 / 2 : ℝ) ^ 11 ≤
      (decider D B hN (Paper2.AEndpoint.gapOf a) (gapPos a ha) S E).prob w (· ≠ [true]) := by
  let Good : List Bool → Prop := fun y => ∃ i : EncodedCommunication.Instance, ∃ c : ℕ,
    y = HeaderWordRun.headeredWord (Paper2.AEndpoint.gapOf a) i ∧ Paper2.AModel.targetD (HeaderWordRun.matrix i) = some c ∧
      (i.threshold : ℝ) + ((Paper2.AEndpoint.gapOf a) : ℝ) / 2 < (c : ℝ) - a
  have hnot : EncodedCNF.encode (AFront.T10.routed hN w).val ∉ EncodedCNF.Language := by
    intro h
    exact hw ((AFront.Route.routedFormula_sat_iff hN w).mp
      ((Paper2.AEndpoint.DA2_recommended _).mp h))
  have hlaw := ((Paper2.A3CloseEndpoints.T02_law_final D B EncodedCNF.Language
    Paper2.AEndpoint.DA2_recommended a ha).2.2 (AFront.T10.routed hN w)).2
    (fun b => (Workspace.Types.CommComplexity.D
      ((expOf D B hN (Paper2.AEndpoint.gapOf a) w).output.table b).matrix : ℝ) - a)
    (by
      intro b
      rw [show ∀ x : ℝ, x - a - x = -a from fun x => by ring, abs_neg, abs_of_nonneg ha])
  have hno := hlaw.2 hnot
  have hfirst : (sourceAlg D B hN (Paper2.AEndpoint.gapOf a) (gapPos a ha) S).prob w (fun y => ¬ Good y) ≤
      (1 / 2 : ℝ) ^ 11 := by
    rw [sourceAlg_prob]
    have hmono : @FiniteLaw.prob _ (expOf D B hN (Paper2.AEndpoint.gapOf a) w).tapeFintype (expOf D B hN (Paper2.AEndpoint.gapOf a) w).tapeLaw
        (fun b => ((expOf D B hN (Paper2.AEndpoint.gapOf a) w).output.budget : ℝ) + ((Paper2.AEndpoint.gapOf a) : ℝ) / 2 <
          (Workspace.Types.CommComplexity.D ((expOf D B hN (Paper2.AEndpoint.gapOf a) w).output.table b).matrix : ℝ) - a) ≤
        @FiniteLaw.prob _ (expOf D B hN (Paper2.AEndpoint.gapOf a) w).tapeFintype (expOf D B hN (Paper2.AEndpoint.gapOf a) w).tapeLaw
        (fun t => Good (HeaderWordRun.headeredWord (Paper2.AEndpoint.gapOf a) (instOf D B hN (Paper2.AEndpoint.gapOf a) w t))) :=
      @FiniteLaw.prob_mono _ (expOf D B hN (Paper2.AEndpoint.gapOf a) w).tapeFintype (expOf D B hN (Paper2.AEndpoint.gapOf a) w).tapeLaw _ _
        (fun t ht => ⟨instOf D B hN (Paper2.AEndpoint.gapOf a) w t, _, rfl, targetD_instOf D B hN (Paper2.AEndpoint.gapOf a) w t, ht⟩)
    have hcompl := @Paper2.Unit4Shell.Amplification.prob_not _ (expOf D B hN (Paper2.AEndpoint.gapOf a) w).tapeFintype
      (expOf D B hN (Paper2.AEndpoint.gapOf a) w).tapeLaw
      (fun t => Good (HeaderWordRun.headeredWord (Paper2.AEndpoint.gapOf a) (instOf D B hN (Paper2.AEndpoint.gapOf a) w t)))
    rw [hcompl]
    linarith
  have hsecond : ∀ y, Good y →
      (HeaderStrip.selectedClassifier E).prob y (· = [true]) ≤ 0 := by
    rintro y ⟨i, c, rfl, hc, hgap⟩
    unfold SelectedTape.Algorithm.prob
    exact prob_le_zero_of_forall_not _ _ _ (fun g hg =>
      classifier_every_tape_no E a hE (HeaderWordRun.matrix i) c i.threshold (Paper2.AEndpoint.gapOf a) hc hgap g hg)
  have h := SelectedTape.Bind.failure_le (sourceAlg D B hN (Paper2.AEndpoint.gapOf a) (gapPos a ha) S)
    (HeaderStrip.selectedClassifier E) w Good (· = [true]) ((1 / 2 : ℝ) ^ 11) 0
    hfirst hsecond le_rfl
  change (decider D B hN (Paper2.AEndpoint.gapOf a) (gapPos a ha) S E).prob w (· = [true]) ≤ (1 / 2 : ℝ) ^ 11 + 0 at h
  rw [prob_ne_true]
  linarith

/-- **Segment 1**: the same composed decider decides `EncodedCNF.Language` one-sidedly
(`DecidesOneSided`, D-A4 constant `1/2`) under an always-correct estimator. -/
theorem decider_decidesOneSided {N : ℕ} (hN : 1 ≤ N) (a : ℝ) (ha : 0 ≤ a)
    (S : BridgeSpec D B hN (Paper2.AEndpoint.gapOf a)) (E : SelectedTape.Algorithm)
    (hE : EstimatesDExact E a) :
    DecidesOneSided (decider D B hN (Paper2.AEndpoint.gapOf a) (gapPos a ha) S E)
      EncodedCNF.Language := by
  intro w
  refine ⟨fun hw t => decider_every_tape_yes D B hN _ (gapPos a ha) S E a hE
    (Paper2.AEndpoint.gapOf_spec a ha).2 w hw t, fun hw => ?_⟩
  have := decider_no_exact D B hN a ha S E hE w hw
  norm_num at this ⊢
  linarith

/-- **Segment 1 conclusion**: `SAT ∈ coRP` in the selected carrier. -/
theorem inCoRP_of_exact {N : ℕ} (hN : 1 ≤ N) (a : ℝ) (ha : 0 ≤ a)
    (E : SelectedTape.Algorithm) (hE : EstimatesDExact E a)
    (S : BridgeSpec D B hN (Paper2.AEndpoint.gapOf a)) :
    InCoRP EncodedCNF.Language :=
  ⟨_, decider_decidesOneSided D B hN a ha S E hE⟩

end Paper2.ADecider4

#print axioms Paper2.ADecider4.classifier_every_tape_yes
#print axioms Paper2.ADecider4.classifier_every_tape_no
#print axioms Paper2.ADecider4.sourceAlg_every_tape
#print axioms Paper2.ADecider4.decider_every_tape_split
#print axioms Paper2.ADecider4.decider_every_tape_yes
#print axioms Paper2.ADecider4.decider_no_exact
#print axioms Paper2.ADecider4.decider_decidesOneSided
#print axioms Paper2.ADecider4.inCoRP_of_exact
