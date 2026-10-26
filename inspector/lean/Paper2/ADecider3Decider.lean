import Paper2.ADecider3Bridge
import Paper2.BindSelected
import Paper2.HeaderClassifierJoin

/-!
# T02 decider, segments 2b-4: ONE selected-tape machine and its law (fixed gap `k = gapOf a`)

Lock v12 `sections/01-introduction.tex:111-122`: "For every fixed $a\ge0$, a bounded-error
polynomial-time additive-error-$a$ estimator for $\D$ implies $\NP\subseteq\BPP$. ...
Choose a fixed integer $k>2a$. Amplify the estimator's success probability to $99/100$ by a
constant number of independent calls and a median. Accept the source exactly when its estimate
is below $B+k/2$. On a correct estimate the YES and good NO cases lie on opposite sides of this
threshold. The sum of reduction and estimation errors is less than $1/2$, giving a BPP algorithm
for satisfiability."

Physical composition (all stages are actual finite machines, every handoff charged):
1. the all-input CNF graph compiler `CNFGraphGuard.graphWord` (admitted front `AFrontRoute` /
   `AFrontT10` inside the frozen private `CNFGraphMachine`), truncating the outer tape
   (`ImagePullback.pullback`, admitted `NPOwner1.Trunc`);
2. the bridge stage (`BridgeSpec`, premise), post-composed here with the fixed-gap threshold
   header machine `HeaderWordRun.machine k` (A27), printing `natField (2B+k) ++ matrixWord`;
3. the retained independent tape suffix and the selected median classifier
   `HeaderStrip.selectedClassifier E` (A27) through the two-stage bind `SelectedTape.Bind`.
-/

noncomputable section
set_option maxHeartbeats 4000000

namespace Paper2.ADecider3

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2.Unit4Shell.T10Finite

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

/-- D-A3 estimator in the selected carrier (lock I:72-74): on every decodable matrix word,
with probability at least `2/3` the printed word is a dyadic within `a` of `D`. -/
def EstimatesD (E : SelectedTape.Algorithm) (a : ℝ) : Prop :=
  ∀ w c, Paper2.AModel.targetD w = some c →
    2 / 3 ≤ E.prob w (fun out => ∃ v, Paper2.AModel.decodeDyadic out = some v ∧ |v - c| ≤ a)

/-- Deterministic always-correct D-A3 estimator in the selected carrier (lock I:113): on every
decodable matrix word and EVERY selected tape, the printed word is a dyadic within `a` of `D`. -/
def EstimatesDExact (E : SelectedTape.Algorithm) (a : ℝ) : Prop :=
  ∀ w c, Paper2.AModel.targetD w = some c → ∀ t : Fin (E.tapeLength w) → Bool,
    ∃ v, Paper2.AModel.decodeDyadic (E.output w (List.ofFn t)) = some v ∧ |v - c| ≤ a

theorem EstimatesDExact.estimatesD {E : SelectedTape.Algorithm} {a : ℝ}
    (h : EstimatesDExact E a) : EstimatesD E a := by
  intro w c hc
  have h1 : E.prob w (fun out => ∃ v, Paper2.AModel.decodeDyadic out = some v ∧ |v - c| ≤ a)
      = 1 := by
    unfold SelectedTape.Algorithm.prob
    exact Paper2.AEndpoint.prob_of_forall _ _ (h w c hc)
  rw [h1]; norm_num

/-- Header post-processing of a printed word: decode the canonical instance and print
`natField (2*threshold+k) ++ matrixWord`. -/
def headerOut (k : ℕ) (v : List Bool) : List Bool :=
  match EncodedCommunication.decodeInstance v with
  | some i => HeaderWordRun.headeredWord k i
  | none => []

theorem exp_dims {N : ℕ} (hN : 1 ≤ N) (k : ℕ) (w : List Bool) :
    0 < (expOf D B hN k w).output.rows ∧ 0 < (expOf D B hN k w).output.cols := by
  rw [TotalFiniteConstructorScratch.experiment_output_eq_select]
  exact EncodedSelectedOutput.selected_dimensions_pos _ _ _ _ _

theorem instOf_valid {N : ℕ} (hN : 1 ≤ N) (k : ℕ) (w : List Bool)
    (t : (expOf D B hN k w).output.Tape) : (instOf D B hN k w t).Valid :=
  EncodedSelectedOutput.instanceOf_valid _ _ (exp_dims D B hN k w).1 (exp_dims D B hN k w).2

theorem headerOut_instOf {N : ℕ} (hN : 1 ≤ N) (k : ℕ) (w : List Bool)
    (t : (expOf D B hN k w).output.Tape) :
    headerOut k (EncodedCommunication.encodeInstance (instOf D B hN k w t)) =
      HeaderWordRun.headeredWord k (instOf D B hN k w t) := by
  unfold headerOut
  rw [EncodedCommunication.decode_encode _ (instOf_valid D B hN k w t)]

/-- The D-A3 target of the matrix part of the selected instance is `D` of the selected table. -/
theorem targetD_instOf {N : ℕ} (hN : 1 ≤ N) (k : ℕ) (w : List Bool)
    (t : (expOf D B hN k w).output.Tape) :
    Paper2.AModel.targetD (HeaderWordRun.matrix (instOf D B hN k w t)) =
      some (Workspace.Types.CommComplexity.D ((expOf D B hN k w).output.table t).matrix) := by
  have hv : Paper2.AModel.MatrixValid (expOf D B hN k w).output.rows
      (expOf D B hN k w).output.cols ((expOf D B hN k w).output.table t).bits :=
    ⟨(exp_dims D B hN k w).1, (exp_dims D B hN k w).2, ((expOf D B hN k w).output.table t).length⟩
  have h := Paper2.AModel.targetD_matrixWord hv
  rw [EncodedSelectedOutput.tableGame_eq_matrix] at h
  exact h

/-! ## The header-composed bridge stage -/

private noncomputable def hdrC (k : ℕ) : ℕ :=
  Classical.choose (HeaderWordRun.machine_outputs_polynomial k)
private noncomputable def hdrD (k : ℕ) : ℕ :=
  Classical.choose (Classical.choose_spec (HeaderWordRun.machine_outputs_polynomial k))
private theorem hdrRun (k : ℕ) (i : EncodedCommunication.Instance) (hk : 0 < k) :
    (HeaderWordRun.machine k).OutputsWithin (EncodedCommunication.encodeInstance i)
      (HeaderWordRun.headeredWord k i)
      (hdrC k * ((EncodedCommunication.encodeInstance i).length + 1) ^ hdrD k) :=
  Classical.choose_spec (Classical.choose_spec (HeaderWordRun.machine_outputs_polynomial k)) i hk

private def hFull {N : ℕ} (hN : 1 ≤ N) (k : ℕ) (S : BridgeSpec D B hN k) (X : ℕ) : ℕ :=
  S.stage.cT * (X + 1) ^ S.stage.dT +
    2 * (2 * X + 1 + S.stage.cR * (X + 1) ^ S.stage.dR +
      S.stage.cT * (X + 1) ^ S.stage.dT * S.stage.machine.pushBound) + 2 +
    hdrC k * ((2 * X + 1 + S.stage.cR * (X + 1) ^ S.stage.dR +
      S.stage.cT * (X + 1) ^ S.stage.dT * S.stage.machine.pushBound) + 1) ^ hdrD k

private theorem hFull_poly {N : ℕ} (hN : 1 ≤ N) (k : ℕ) (S : BridgeSpec D B hN k) :
    Paper2.Unit4Shell.Poly.PolyIn id (hFull D B hN k S) := by
  unfold hFull
  repeat (first
    | exact Paper2.Unit4Shell.Poly.self
    | exact Paper2.Unit4Shell.Poly.const _
    | apply Paper2.Unit4Shell.Poly.add
    | apply Paper2.Unit4Shell.Poly.mul
    | apply Paper2.Unit4Shell.Poly.pow)

private noncomputable def hC {N : ℕ} (hN : 1 ≤ N) (k : ℕ) (S : BridgeSpec D B hN k) : ℕ :=
  Classical.choose (hFull_poly D B hN k S)
private noncomputable def hD {N : ℕ} (hN : 1 ≤ N) (k : ℕ) (S : BridgeSpec D B hN k) : ℕ :=
  Classical.choose (Classical.choose_spec (hFull_poly D B hN k S))
private theorem hBound {N : ℕ} (hN : 1 ≤ N) (k : ℕ) (S : BridgeSpec D B hN k) (X : ℕ) :
    hFull D B hN k S X ≤ hC D B hN k S * (X + 1) ^ hD D B hN k S :=
  Classical.choose_spec (Classical.choose_spec (hFull_poly D B hN k S)) X

private theorem ofFn_take_len {L : ℕ} (s : Fin L → Bool) (r : ℕ) (h : r ≤ L) :
    ((List.ofFn s).take r).length = r := by simp [h]

/-- Every selected stage tape prints a canonical selected instance. -/
theorem stage_output_inst {N : ℕ} (hN : 1 ≤ N) (k : ℕ) (S : BridgeSpec D B hN k)
    (w : List Bool) (s : Fin (S.stage.tapeLength (CNFGraphGuard.graphWord D B hN w)) → Bool) :
    ∃ t : (expOf D B hN k w).output.Tape,
      S.stage.output (CNFGraphGuard.graphWord D B hN w) (List.ofFn s) =
        EncodedCommunication.encodeInstance (instOf D B hN k w t) := by
  obtain ⟨t, ht⟩ := exp_surj D B hN k w _ (ofFn_take_len s _ (S.bits_le w))
  exact ⟨t, S.output_eq w s t ht⟩

private theorem headerRuns {N : ℕ} (hN : 1 ≤ N) (k : ℕ) (hk : 0 < k) (S : BridgeSpec D B hN k) :
    ∀ x (t : Fin (S.stage.cR * ((CNFGraphGuard.graphWord D B hN x).length + 1) ^ S.stage.dR)
        → Bool),
      (BitMachineComposition.composition S.stage.machine (HeaderWordRun.machine k)).OutputsWithin
        (EncodedComplexity.pair (CNFGraphGuard.graphWord D B hN x) (List.ofFn t))
        (headerOut k (S.stage.output (CNFGraphGuard.graphWord D B hN x) (List.ofFn t)))
        (hC D B hN k S * ((CNFGraphGuard.graphWord D B hN x).length + 1) ^ hD D B hN k S) := by
  intro x t
  obtain ⟨t', ht'⟩ : ∃ t' : (expOf D B hN k x).output.Tape,
      S.stage.output (CNFGraphGuard.graphWord D B hN x) (List.ofFn t) =
        EncodedCommunication.encodeInstance (instOf D B hN k x t') :=
    stage_output_inst D B hN k S x t
  have hrun : S.stage.machine.OutputsWithin
      (EncodedComplexity.pair (CNFGraphGuard.graphWord D B hN x) (List.ofFn t))
      (EncodedCommunication.encodeInstance (instOf D B hN k x t'))
      (S.stage.cT * ((CNFGraphGuard.graphWord D B hN x).length + 1) ^ S.stage.dT) := by
    rw [← ht']
    exact S.stage.runs x t
  rw [ht', headerOut_instOf]
  have hmid := BitMachine.output_length_bound S.stage.machine hrun
  have hpair : (EncodedComplexity.pair (CNFGraphGuard.graphWord D B hN x)
      (List.ofFn t)).length = 2 * (CNFGraphGuard.graphWord D B hN x).length + 1 +
        S.stage.cR * ((CNFGraphGuard.graphWord D B hN x).length + 1) ^ S.stage.dR := by
    rw [EncodedComplexity.pair_length]; simp
  have hcomp := BitMachineComposition.composition_outputsWithin S.stage.machine
    (HeaderWordRun.machine k) hrun
    (hdrRun k (instOf D B hN k x t') hk)
  refine BitMachine.outputsWithin_mono _ hcomp ?_
  refine le_trans ?_ (hBound D B hN k S (CNFGraphGuard.graphWord D B hN x).length)
  unfold hFull
  have hmid' : (EncodedCommunication.encodeInstance (instOf D B hN k x t')).length ≤
      2 * (CNFGraphGuard.graphWord D B hN x).length + 1 +
        S.stage.cR * ((CNFGraphGuard.graphWord D B hN x).length + 1) ^ S.stage.dR +
        S.stage.cT * ((CNFGraphGuard.graphWord D B hN x).length + 1) ^ S.stage.dT *
          S.stage.machine.pushBound := by
    rw [hpair] at hmid; exact hmid
  have hpow : hdrC k * ((EncodedCommunication.encodeInstance (instOf D B hN k x t')).length + 1)
        ^ hdrD k ≤
      hdrC k * ((2 * (CNFGraphGuard.graphWord D B hN x).length + 1 +
        S.stage.cR * ((CNFGraphGuard.graphWord D B hN x).length + 1) ^ S.stage.dR +
        S.stage.cT * ((CNFGraphGuard.graphWord D B hN x).length + 1) ^ S.stage.dT *
          S.stage.machine.pushBound) + 1) ^ hdrD k := by
    gcongr
  omega

/-- The bridge stage followed by the fixed-gap header machine: one image-only stage with the
same selected tape and a fixed monomial clock. -/
noncomputable def headerStage {N : ℕ} (hN : 1 ≤ N) (k : ℕ) (hk : 0 < k)
    (S : BridgeSpec D B hN k) : ImagePullback.Stage (CNFGraphGuard.graphWord D B hN) where
  cR := S.stage.cR
  dR := S.stage.dR
  cT := hC D B hN k S
  dT := hD D B hN k S
  machine := BitMachineComposition.composition S.stage.machine (HeaderWordRun.machine k)
  output := fun y tape => headerOut k (S.stage.output y tape)
  runs := headerRuns D B hN k hk S

/-- The randomized source-to-headered-word algorithm on EVERY raw CNF word (front, bridge,
header), in the selected carrier. -/
noncomputable def sourceAlg {N : ℕ} (hN : 1 ≤ N) (k : ℕ) (hk : 0 < k)
    (S : BridgeSpec D B hN k) : SelectedTape.Algorithm :=
  ImagePullback.pullback (CNFGraphGuard.graphWord_polytime D B hN) (headerStage D B hN k hk S)

/-- Exact output law of `sourceAlg`: the experiment law of the headered selected instance. -/
theorem sourceAlg_prob {N : ℕ} (hN : 1 ≤ N) (k : ℕ) (hk : 0 < k) (S : BridgeSpec D B hN k)
    (w : List Bool) (E : List Bool → Prop) :
    (sourceAlg D B hN k hk S).prob w E =
      @FiniteLaw.prob _ (expOf D B hN k w).tapeFintype (expOf D B hN k w).tapeLaw
        (fun t => E (HeaderWordRun.headeredWord k (instOf D B hN k w t))) := by
  rw [sourceAlg, ImagePullback.pullback_prob]
  change (Paper2.Unit4Shell.Definitions.uniformTape
      (S.stage.tapeLength (CNFGraphGuard.graphWord D B hN w))).prob
    (fun s => (fun v => E (headerOut k v))
      (S.stage.output (CNFGraphGuard.graphWord D B hN w) (List.ofFn s))) = _
  rw [stage_law D B hN k S w (fun v => E (headerOut k v))]
  simp only [headerOut_instOf]

/-- **THE composed T02 decider** at gap `k`: ONE `SelectedTape.Algorithm` (fixed tape and clock
constants, one finite machine) = two-stage bind of `sourceAlg` and the selected classifier on
the retained independent tape suffix. -/
noncomputable def decider {N : ℕ} (hN : 1 ≤ N) (k : ℕ) (hk : 0 < k) (S : BridgeSpec D B hN k)
    (E : SelectedTape.Algorithm) : SelectedTape.Algorithm :=
  SelectedTape.Bind.algorithm (sourceAlg D B hN k hk S) (HeaderStrip.selectedClassifier E)

theorem decider_machine {N : ℕ} (hN : 1 ≤ N) (k : ℕ) (hk : 0 < k) (S : BridgeSpec D B hN k)
    (E : SelectedTape.Algorithm) :
    (decider D B hN k hk S E).machine =
      SelectedTape.Bind.machine (sourceAlg D B hN k hk S) (HeaderStrip.selectedClassifier E) :=
  rfl

private theorem prob_zero_of_forall_not {α : Type} (inst : Fintype α) (μ : @FiniteLaw α inst)
    (P : α → Prop) (h : ∀ x, ¬ P x) : @FiniteLaw.prob α inst μ P ≤ 0 := by
  have := @FiniteLaw.prob_mono α inst μ P (fun _ => False) (fun x hx => h x hx)
  rw [@FiniteLaw.prob_false α inst μ] at this
  exact this

/-- **Law, YES side**: from `EstimatesD` and the admitted finite law, acceptance
probability `≥ 99/100`. -/
theorem decider_yes {N : ℕ} (hN : 1 ≤ N) (k : ℕ) (hk1 : 1 ≤ k) (S : BridgeSpec D B hN k)
    (E : SelectedTape.Algorithm) (a : ℝ) (hE : EstimatesD E a) (hka : 2 * a < k)
    (w : List Bool) (hw : w ∈ EncodedCNF.Language) :
    99 / 100 ≤ (decider D B hN k (by omega) S E).prob w (· = [true]) := by
  let Good : List Bool → Prop := fun y => ∃ i : EncodedCommunication.Instance, ∃ c : ℕ,
    y = HeaderWordRun.headeredWord k i ∧ Paper2.AModel.targetD (HeaderWordRun.matrix i) = some c ∧
      c ≤ i.threshold
  have hfirst : (sourceAlg D B hN k (by omega) S).prob w (fun y => ¬ Good y) ≤ 0 := by
    rw [sourceAlg_prob]
    refine prob_zero_of_forall_not _ _ _ ?_
    intro t hnot
    exact hnot ⟨instOf D B hN k w t, _, rfl, targetD_instOf D B hN k w t,
      exp_yes D B hN k hk1 w hw t⟩
  have hsecond : ∀ y, Good y → (HeaderStrip.selectedClassifier E).prob y (· ≠ [true]) ≤ 1 / 100 := by
    rintro y ⟨i, c, rfl, hc, hcB⟩
    rw [prob_ne_true]
    have := HeaderStrip.selectedClassifier_yes E a hE (HeaderWordRun.matrix i) c i.threshold k
      hc hka hcB
    change 99 / 100 ≤ (HeaderStrip.selectedClassifier E).prob (HeaderWordRun.headeredWord k i)
      (· = [true]) at this
    linarith
  have h := SelectedTape.Bind.failure_le (sourceAlg D B hN k (by omega) S)
    (HeaderStrip.selectedClassifier E) w Good (· ≠ [true]) 0 (1 / 100) hfirst hsecond
    (by norm_num)
  change (decider D B hN k (by omega) S E).prob w (· ≠ [true]) ≤ 0 + 1 / 100 at h
  rw [prob_ne_true] at h
  linarith

/-- **Law, NO side**: acceptance probability `≤ 19/1000 + 1/100`. -/
theorem decider_no {N : ℕ} (hN : 1 ≤ N) (k : ℕ) (hk1 : 1 ≤ k) (S : BridgeSpec D B hN k)
    (E : SelectedTape.Algorithm) (a : ℝ) (hE : EstimatesD E a) (hka : 2 * a < k)
    (w : List Bool) (hw : w ∉ EncodedCNF.Language) :
    (decider D B hN k (by omega) S E).prob w (· = [true]) ≤ 19 / 1000 + 1 / 100 := by
  let Good : List Bool → Prop := fun y => ∃ i : EncodedCommunication.Instance, ∃ c : ℕ,
    y = HeaderWordRun.headeredWord k i ∧ Paper2.AModel.targetD (HeaderWordRun.matrix i) = some c ∧
      i.threshold + k ≤ c
  have hfirst : (sourceAlg D B hN k (by omega) S).prob w (fun y => ¬ Good y) ≤ 19 / 1000 := by
    rw [sourceAlg_prob]
    have hno := exp_no D B hN k hk1 w hw
    have hmono : @FiniteLaw.prob _ (expOf D B hN k w).tapeFintype (expOf D B hN k w).tapeLaw
        (fun t => (expOf D B hN k w).output.budget + k ≤
          Workspace.Types.CommComplexity.D ((expOf D B hN k w).output.table t).matrix) ≤
        @FiniteLaw.prob _ (expOf D B hN k w).tapeFintype (expOf D B hN k w).tapeLaw
        (fun t => Good (HeaderWordRun.headeredWord k (instOf D B hN k w t))) :=
      @FiniteLaw.prob_mono _ (expOf D B hN k w).tapeFintype (expOf D B hN k w).tapeLaw _ _
        (fun t ht => ⟨instOf D B hN k w t, _, rfl, targetD_instOf D B hN k w t, ht⟩)
    have hnot := @Paper2.Unit4Shell.Amplification.prob_not _ (expOf D B hN k w).tapeFintype
      (expOf D B hN k w).tapeLaw
      (fun t => Good (HeaderWordRun.headeredWord k (instOf D B hN k w t)))
    rw [hnot]
    linarith
  have hsecond : ∀ y, Good y → (HeaderStrip.selectedClassifier E).prob y (· = [true]) ≤ 1 / 100 := by
    rintro y ⟨i, c, rfl, hc, hBc⟩
    exact HeaderStrip.selectedClassifier_no E a hE (HeaderWordRun.matrix i) c i.threshold k
      hc hka hBc
  exact SelectedTape.Bind.failure_le (sourceAlg D B hN k (by omega) S)
    (HeaderStrip.selectedClassifier E) w Good (· = [true]) (19 / 1000) (1 / 100) hfirst hsecond
    (by norm_num)

/-- **Segment 3: the decider decides SAT with error `≤ 1/3` on every word.** -/
theorem decider_decides {N : ℕ} (hN : 1 ≤ N) (k : ℕ) (hk1 : 1 ≤ k) (S : BridgeSpec D B hN k)
    (E : SelectedTape.Algorithm) (a : ℝ) (hE : EstimatesD E a) (hka : 2 * a < k) :
    (decider D B hN k (by omega) S E).Decides EncodedCNF.Language (1 / 3) := by
  intro w
  refine ⟨fun hw => ?_, fun hw => ?_⟩
  · have := decider_yes D B hN k hk1 S E a hE hka w hw
    linarith
  · have := decider_no D B hN k hk1 S E a hE hka w hw
    linarith

/-- **Segment 4: T02, first clause, class level in the selected carrier** (lock v12
`sections/01-introduction.tex:111-122`, `intro:corollary`: "For every fixed $a\ge0$, a
bounded-error polynomial-time additive-error-$a$ estimator for $\D$ implies
$\NP\subseteq\BPP$."). Premises: a fixed `a ≥ 0` and a selected-carrier estimator with
`EstimatesD` at error `a` (D-A1/D-A3); `NPHard EncodedCNF.Language` (D-A5); the records `D`, `B`
(D-A7); the bridge `BridgeSpec` at the proof's gap `k = gapOf a` (premise, lane a-bridge-1).
Conclusion: every NP language is in selected-carrier `BPP` (D-A1 + D-A4, R19). -/
theorem T02_class_bpp_selected {N : ℕ} (hN : 1 ≤ N) (a : ℝ) (ha : 0 ≤ a)
    (E : SelectedTape.Algorithm) (hE : EstimatesD E a)
    (hNP : EncodedComplexity.NPHard EncodedCNF.Language)
    (S : BridgeSpec D B hN (Paper2.AEndpoint.gapOf a)) :
    ∀ L, EncodedComplexity.InNP L → InBPP L := by
  obtain ⟨hk1, hka⟩ := Paper2.AEndpoint.gapOf_spec a ha
  exact SelectedTape.np_subset_inBPP hNP
    ⟨decider D B hN _ (by omega) S E, decider_decides D B hN _ hk1 S E a hE hka⟩

end Paper2.ADecider3

#print axioms Paper2.ADecider3.sourceAlg_prob
#print axioms Paper2.ADecider3.decider_yes
#print axioms Paper2.ADecider3.decider_no
#print axioms Paper2.ADecider3.decider_decides
#print axioms Paper2.ADecider3.T02_class_bpp_selected
