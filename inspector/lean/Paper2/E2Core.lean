import Paper2.AEthDLaw
import Paper2.AModelEstimator
import Paper2.AModelETH
import Paper2.HA3Endpoints
import Paper2.AEndpointDA1

/-! a-eth-owner-2 copy of frozen `a-eth-owner-1/AEthDT24.lean` (SHA-256 74a4bbccb3f80fda228575bab878b0d828492c9be20907b8ec70b967c910a1c5). Changes: removed `DeciderAssembly`, `T24_class_decided`, `T03_class_decided` (prefix-carrier conclusions `¬ AModel.RandomizedSparseETH`, R19/R20: not cited) and their #print lines; nothing else. -/


/-!
# Lane `owner:a-decider-2` (Paper A, lock v12): T24 / T03 at class level in the author's model,
modulo ONE physical assembly statement

Private module, 27 September 2026. Nothing here is admitted; no ledger row is closed.

Lock v12 `06-reduction.tex:107-117` (`thm:quantitative`, T24):
"Assuming randomized sparse ETH, for every fixed $0\le c<1/12$ there is no bounded-error randomized
algorithm, polynomial in the number $T$ of matrix entries, that estimates $\D(M)$ with additive
error at most $c\,\frac{\log T}{\log\log T}$ on every sufficiently large explicit Boolean matrix.
The conclusion also holds when the inputs are square matrices of power-of-two side length."

Proof, `06-reduction.tex:119-124, 134-141`: "On a sparse $N$-variable formula, form the source in
\cref{lem:source-size} and choose $k=\floor{N/\ceil{\log N}^2}$ for sufficiently large $N$. ...
Thus for every fixed $c<1/12$ the gap $k$ eventually exceeds twice the proposed error. The midpoint
test from \cref{intro:corollary} decides the formula with bounded error. Both the construction and
any fixed polynomial-time estimator take $n^{O(k+1)}=2^{O(N/\log N)}=2^{o(N)}$, contrary to
randomized sparse ETH."

Lock v12 `01-introduction.tex:142-146` (`intro:quantitative`, T03): "Under randomized sparse ETH,
for every fixed $0<c<1/12$ there is no bounded-error polynomial-time estimator of $\D(M)$ with
additive error $c\log T/\log\log T$ on every sufficiently large table."

Model (author decisions of 27 September 2026): D-A1 (c) prefix model (`AModel.PrefixAlgorithm`),
D-A2 `EncodedCNF.Language`, D-A3 estimator input = matrix word, output = dyadic rational
(`AModel.matrixWord`, `AModel.decodeDyadic`, `AModel.targetD`), D-A4 error 1/3, D-A6 the prefix-model
`AModel.RandomizedSparseETH` of lane a-model-1, D-A7 the records `D`, `B`.

Content.
* `EstimatesGrowing E c`: `E` estimates `D` of every decodable matrix word `w` within
  `accT c w = c · log₂ T / log₂ log₂ T`, `T = rows·cols` of `w`, with probability `≥ 2/3`.
* `RealisesMidpoint D B E A Φ k`: the segment-1 deliverable at one formula (a DETERMINISTIC output
  identity on a tape layout with the product pushforward); `canonical_layout` shows the canonical
  layout `[reduction bits][147 estimator blocks][rest]` has the required pushforward.
* `decider_error` (segment 2): from `EstimatesGrowing` and `RealisesMidpoint`, the decider errs with
  probability `≤ 1/3` on every sparse valid formula beyond one `N₀`, by the admitted
  `A3CloseEndpoints.T24_final` (law level, H_A3 closed).
* `T24_class_decided`, `T03_class_decided` (segment 3): NOT prefix-model randomized sparse ETH
  from an estimator and the physical assembly statement `hAsm` (the remaining premise).
-/

set_option maxHeartbeats 4000000

namespace Paper2.ADecider

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2 Paper2.FiniteLaw Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics
open Paper2.Unit4Shell.Definitions (uniformTape)
open Paper2.Unit4Shell.Amplification (reps)
open Paper2.MedianOwner

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

set_option hygiene false in
local notation "SEL" Φ:max k:max => TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
  (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) B.degreeBound (sourceGap D B) k

set_option hygiene false in
local notation "EXP" Φ:max k:max => TotalFiniteConstructorScratch.experiment (t10_vertices_pos D B Φ)
  (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) B.degreeBound (sourceGap D B) k

/-- The growing accuracy of `thm:quantitative` at a matrix word: `c · log₂ T / log₂ log₂ T` with
`T = rows · cols` the number of entries of the decoded matrix (`0` off the codec, where
`targetD` is `none` and nothing is required). -/
noncomputable def accT (c : ℝ) (w : List Bool) : ℝ :=
  match AModel.decodeMatrix w with
  | some m => c * (Real.logb 2 ((m.1 * m.2.1 : ℕ) : ℝ) /
      Real.logb 2 (Real.logb 2 ((m.1 * m.2.1 : ℕ) : ℝ)))
  | none => 0

/-- **The estimator hypothesis of `thm:quantitative`** in the D-A1/D-A3 model: on every decodable
matrix word `w` (target `D` of the decoded matrix), `E` prints a dyadic rational within
`accT c w` of it with probability at least `2/3`. (Polynomiality in `T` is `E.Polynomial`, which is
polynomial in `|w| ≥ T`; see the checkpoint for the "sufficiently large" clause.) -/
def EstimatesGrowing (E : AModel.PrefixAlgorithm) (c : ℝ) : Prop :=
  ∀ w (d : ℕ), AModel.targetD w = some d →
    2 / 3 ≤ E.prob w (fun out => ∃ v, AModel.decodeDyadic out = some v ∧ |v - d| ≤ accT c w)

/-- The matrix word the estimator is run on: the matrix part of the reduction's printed instance
at reduction tape `b` (D-A3, lane a-front-1's projection / split machines print exactly this). -/
noncomputable def mwOf (Φ : ValidFormula) (k : ℕ) (b : (EXP Φ k).output.Tape) : List Bool :=
  AModel.matrixWord (EXP Φ k).output.rows (EXP Φ k).output.cols ((EXP Φ k).output.table b).bits

/-- The midpoint threshold `B + k/2` (lock `01-introduction.tex:119`). -/
noncomputable def thetaOf (Φ : ValidFormula) (k : ℕ) : ℝ :=
  ((EXP Φ k).output.budget : ℝ) + (k : ℝ) / 2

/-- **Segment-1 deliverable at one formula (a deterministic statement about the decider)**, for a
word map `mw` (the word the estimator is run on at reduction tape `b`). The decider `A` on input
`encode Φ` reads its uniform tape through a layout `π` (first component a reduction tape, then
`reps = 147` estimator tapes of the common length `s = E.tapeLength |mw b|`) whose pushforward is the
reduction law times the 147-fold uniform law, and it accepts on tape `t` exactly when a strict
majority of the 147 estimator outputs on `mw (π t).1` decode below `B + k/2` (the bit lane
a-median-1's `medMachine` prints). -/
def RealisesMidpointW (Φ : ValidFormula) (k : ℕ) (mw : (EXP Φ k).output.Tape → List Bool)
    (E A : AModel.PrefixAlgorithm) : Prop :=
  letI : Fintype (EXP Φ k).output.Tape := (EXP Φ k).tapeFintype
  ∃ (s : ℕ) (π : (Fin (A.tapeLength (EncodedCNF.encode Φ.val).length) → Bool) →
      (EXP Φ k).output.Tape × (Fin reps → Fin s → Bool)),
    (∀ b, E.tapeLength (mw b).length = s) ∧
    (∀ P : (EXP Φ k).output.Tape × (Fin reps → Fin s → Bool) → Prop,
      (uniformTape (A.tapeLength (EncodedCNF.encode Φ.val).length)).prob (fun t => P (π t)) =
        ((EXP Φ k).tapeLaw.prod ((uniformTape s).iid reps)).prob P) ∧
    ∀ t, A.output (EncodedCNF.encode Φ.val) (List.ofFn t) = [true] ↔
      MajBelow AModel.decodeDyadic
        (fun i => E.output (mw (π t).1) (List.ofFn ((π t).2 i))) (thetaOf D B Φ k)

/-- `RealisesMidpointW` at the printed matrix word `mwOf` (rectangular D-A3 input). -/
def RealisesMidpoint (E A : AModel.PrefixAlgorithm) (Φ : ValidFormula) (k : ℕ) : Prop :=
  RealisesMidpointW D B Φ k (mwOf D B Φ k) E A

/-- **The canonical layout has the required pushforward** (so a physical decider only has to realise
the output identity on `layout`): for every `k ≥ 1` the reduction tape model is `uniformExact` of some
exact length `r` (admitted `AEndpoint.DA1_uniformExact`), and for every decider tape length
`R ≥ r + 147 s` the canonical layout pushes `uniformTape R` forward to `tapeLaw × (uniformTape s)^147`. -/
theorem canonical_layout (Φ : ValidFormula) (k : ℕ) (hk : 1 ≤ k) :
    letI : Fintype (EXP Φ k).output.Tape := (EXP Φ k).tapeFintype
    ∃ r : ℕ, (∀ b, ((EXP Φ k).output.tapeBits b).length = r) ∧
      ∃ e : (EXP Φ k).output.Tape ≃ (Fin r → Bool),
        (∀ b, List.ofFn (e b) = (EXP Φ k).output.tapeBits b) ∧
        ∀ (s R : ℕ) (h : r + reps * s ≤ R)
          (P : (EXP Φ k).output.Tape × (Fin reps → Fin s → Bool) → Prop),
          (uniformTape R).prob (fun t => P (layout e h t)) =
            ((EXP Φ k).tapeLaw.prod ((uniformTape s).iid reps)).prob P := by
  letI : Fintype (EXP Φ k).output.Tape := (EXP Φ k).tapeFintype
  obtain ⟨r, hlen, hinj, hsurj, hw⟩ := AEndpoint.DA1_uniformExact D B Φ k hk
  refine ⟨r, hlen, bitsEquiv r _ hlen hinj hsurj, ofFn_bitsEquiv r _ hlen hinj hsurj,
    fun s R h P => ?_⟩
  exact layout_prob (EXP Φ k).tapeLaw (bitsEquiv r _ hlen hinj hsurj) hw h P

/-- Dimensions of the experiment output are positive (admitted `selected_dimensions_pos`). -/
theorem exp_dims_pos (Φ : ValidFormula) (k : ℕ) :
    0 < (EXP Φ k).output.rows ∧ 0 < (EXP Φ k).output.cols := by
  rw [TotalFiniteConstructorScratch.experiment_output_eq_select]
  exact EncodedSelectedOutput.selected_dimensions_pos _ _ _ _ _

theorem mwOf_valid (Φ : ValidFormula) (k : ℕ) (b : (EXP Φ k).output.Tape) :
    AModel.MatrixValid (EXP Φ k).output.rows (EXP Φ k).output.cols
      ((EXP Φ k).output.table b).bits :=
  ⟨(exp_dims_pos D B Φ k).1, (exp_dims_pos D B Φ k).2, ((EXP Φ k).output.table b).length⟩

theorem targetD_mwOf (Φ : ValidFormula) (k : ℕ) (b : (EXP Φ k).output.Tape) :
    AModel.targetD (mwOf D B Φ k b) =
      some (Workspace.Types.CommComplexity.D ((EXP Φ k).output.table b).matrix) := by
  unfold mwOf
  rw [AModel.targetD_matrixWord (mwOf_valid D B Φ k b), EncodedSelectedOutput.tableGame_eq_matrix]

theorem accT_mwOf (c : ℝ) (Φ : ValidFormula) (k : ℕ) (b : (EXP Φ k).output.Tape) :
    accT c (mwOf D B Φ k b) =
      c * (Real.logb 2 (((EXP Φ k).output.rows * (EXP Φ k).output.cols : ℕ) : ℝ) /
        Real.logb 2 (Real.logb 2 (((EXP Φ k).output.rows * (EXP Φ k).output.cols : ℕ) : ℝ))) := by
  unfold accT mwOf
  rw [AModel.decodeMatrix_matrixWord (mwOf_valid D B Φ k b)]

/-- **Segment 2, at one formula and one gap `k`.** If `A` realises the midpoint test on `Φ` at `k`,
every run of `E` on every printed matrix word is within `a` of `D` with probability `≥ 2/3`, and the
law-level statement holds at `a` (the shape of the admitted `T24_final` / `T24_actual_cut`), then `A`
accepts `encode Φ` with probability `≥ 99/100` when `encode Φ ∈ L` and `≤ 2^-11 + 1/100` otherwise. -/
theorem decider_error_at (L : EncodedComplexity.BinaryLanguage) (Φ : ValidFormula) (k : ℕ) (a : ℝ)
    (mw : (EXP Φ k).output.Tape → List Bool)
    (E A : AModel.PrefixAlgorithm) (hA : RealisesMidpointW D B Φ k mw E A)
    (hrun : ∀ b, 2 / 3 ≤ E.prob (mw b) (fun out => ∃ v, AModel.decodeDyadic out = some v ∧
      |v - (Workspace.Types.CommComplexity.D ((EXP Φ k).output.table b).matrix : ℝ)| ≤ a))
    (hlaw : ∀ {α : Type} [Fintype α] (μ : FiniteLaw α) (est : (EXP Φ k).output.Tape → α → ℝ),
      letI : Fintype (EXP Φ k).output.Tape := (EXP Φ k).tapeFintype
      (∀ b, 2 / 3 ≤ μ.prob (fun t => |est b t -
        Workspace.Types.CommComplexity.D ((EXP Φ k).output.table b).matrix| ≤ a)) →
      (EncodedCNF.encode Φ.val ∈ L →
        ((EXP Φ k).tapeLaw.prod (μ.iid reps)).prob
          (fun x => ¬ Paper2.Unit4Shell.Shells.accepts est (EXP Φ k).output.budget k x) ≤ 1 / 100) ∧
      (EncodedCNF.encode Φ.val ∉ L →
        ((EXP Φ k).tapeLaw.prod (μ.iid reps)).prob
          (fun x => Paper2.Unit4Shell.Shells.accepts est (EXP Φ k).output.budget k x) ≤
            (1 / 2) ^ 11 + 1 / 100 ∧ (1 / 2 : ℝ) ^ 11 + 1 / 100 < 1 / 3)) :
    (EncodedCNF.encode Φ.val ∈ L → 99 / 100 ≤ A.prob (EncodedCNF.encode Φ.val) (· = [true])) ∧
    (EncodedCNF.encode Φ.val ∉ L →
      A.prob (EncodedCNF.encode Φ.val) (· = [true]) ≤ (1 / 2) ^ 11 + 1 / 100) := by
  letI : Fintype (EXP Φ k).output.Tape := (EXP Φ k).tapeFintype
  obtain ⟨s, π, hs, hπ, hout⟩ := hA
  let est : (EXP Φ k).output.Tape → (Fin s → Bool) → ℝ := fun b g =>
    estOf AModel.decodeDyadic (thetaOf D B Φ k) (E.output (mw b) (List.ofFn g))
  have hacc : ∀ b, 2 / 3 ≤ (uniformTape s).prob (fun g => |est b g -
      Workspace.Types.CommComplexity.D ((EXP Φ k).output.table b).matrix| ≤ a) := by
    intro b
    have h1 := hrun b
    unfold AModel.PrefixAlgorithm.prob at h1
    have h2 := AModel.uniformTape_prob_ofFn_congr (hs b)
      (fun w => ∃ v, AModel.decodeDyadic (E.output (mw b) w) = some v ∧
        |v - (Workspace.Types.CommComplexity.D ((EXP Φ k).output.table b).matrix : ℝ)| ≤ a)
    rw [h2] at h1
    exact h1.trans (FiniteLaw.prob_mono _ (fun g hg => est_of_runGood _ _ _ _ _ hg))
  have hmain := hlaw (uniformTape s) est hacc
  have hprob : A.prob (EncodedCNF.encode Φ.val) (· = [true]) =
      ((EXP Φ k).tapeLaw.prod ((uniformTape s).iid reps)).prob
        (fun x => Paper2.Unit4Shell.Shells.accepts est (EXP Φ k).output.budget k x) := by
    unfold AModel.PrefixAlgorithm.prob
    rw [← hπ]
    congr 1
    funext t
    apply propext
    show A.output (EncodedCNF.encode Φ.val) (List.ofFn t) = [true] ↔ _
    rw [hout t]
    exact (accepts_iff_majBelow AModel.decodeDyadic
      (fun b g => E.output (mw b) (List.ofFn g)) (EXP Φ k).output.budget k (π t)).symm
  refine ⟨fun hin => ?_, fun hout' => ?_⟩
  · have h := hmain.1 hin
    rw [Paper2.Unit4Shell.Amplification.prob_not] at h
    rw [hprob]
    linarith
  · rw [hprob]
    exact (hmain.2 hout').1

/-- **Segment 2: the error of the growing-gap decider.** For every sparsity density `cs` and
`0 ≤ c < 1/12` there is `N₀` such that for every valid `Φ` with `clauses ≤ cs·N`, `N ≥ N₀`, every
estimator `E` with `EstimatesGrowing E c` and every decider `A` realising the midpoint test at
`k = kOf N` on `Φ` (`RealisesMidpoint`): `A` accepts `encode Φ` with probability `≥ 2/3` if
`Φ` is satisfiable and `≤ 1/3` otherwise. The law-level content is the admitted
`A3CloseEndpoints.T24_final` at `L = EncodedCNF.Language` (`DA2_recommended`), non-square. -/
theorem decider_error (cs : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12) :
    ∃ N₀ : ℕ, ∀ Φ : ValidFormula, Φ.val.clauses.length ≤ cs * Φ.val.variables →
      N₀ ≤ Φ.val.variables → ∀ E A : AModel.PrefixAlgorithm, EstimatesGrowing E c →
      RealisesMidpoint D B E A Φ (kOf Φ.val.variables) →
      (EncodedCNF.encode Φ.val ∈ EncodedCNF.Language →
        1 - 1 / 3 ≤ A.prob (EncodedCNF.encode Φ.val) (· = [true])) ∧
      (EncodedCNF.encode Φ.val ∉ EncodedCNF.Language →
        A.prob (EncodedCNF.encode Φ.val) (· = [true]) ≤ 1 / 3) := by
  obtain ⟨M, hM⟩ := A3CloseEndpoints.T24_final D B EncodedCNF.Language AEndpoint.DA2_recommended
    cs c hc0 hc false
  obtain ⟨N₀, hN₀⟩ := hM 1 one_pos
  refine ⟨N₀, fun Φ hsp hN E A hE hA => ?_⟩
  obtain ⟨_, _, _, hdims, _, hlaw⟩ := hN₀ Φ hsp hN
  have hdimsE : (EXP Φ (kOf Φ.val.variables)).output.rows *
      (EXP Φ (kOf Φ.val.variables)).output.cols =
      printedT (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length B.degreeBound
        (sourceGap D B) (kOf Φ.val.variables) := by
    rw [TotalFiniteConstructorScratch.experiment_output_eq_select]; exact hdims
  have hrun : ∀ b, 2 / 3 ≤ E.prob (mwOf D B Φ (kOf Φ.val.variables) b)
      (fun out => ∃ v, AModel.decodeDyadic out = some v ∧
        |v - (Workspace.Types.CommComplexity.D
          ((EXP Φ (kOf Φ.val.variables)).output.table b).matrix : ℝ)| ≤
        c * (Real.logb 2 ((printedT (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length
            B.degreeBound (sourceGap D B) (kOf Φ.val.variables) : ℕ) : ℝ) /
          Real.logb 2 (Real.logb 2 ((printedT (t10Graph D B Φ).vertices
            (t10Graph D B Φ).edges.length B.degreeBound (sourceGap D B)
            (kOf Φ.val.variables) : ℕ) : ℝ)))) := by
    intro b
    have h1 := hE (mwOf D B Φ (kOf Φ.val.variables) b) _
      (targetD_mwOf D B Φ (kOf Φ.val.variables) b)
    rw [accT_mwOf, hdimsE] at h1
    exact h1
  have h := decider_error_at D B EncodedCNF.Language Φ (kOf Φ.val.variables) _ _ E A hA hrun
    (fun μ est hacc => hlaw μ est hacc)
  refine ⟨fun hin => ?_, fun hout => ?_⟩
  · have := h.1 hin
    linarith
  · have := h.2 hout
    have h3 : (1 / 2 : ℝ) ^ 11 + 1 / 100 ≤ 1 / 3 := by norm_num
    linarith

theorem variableCount_encode (Φ : ValidFormula) :
    EncodedETHTail.variableCount (EncodedCNF.encode Φ.val) = Φ.val.variables := by
  simp [EncodedETHTail.variableCount, EncodedCNF.decode_encode Φ.val Φ.property]

theorem cnfClauseCount_encode (Φ : ValidFormula) :
    AModel.cnfClauseCount (EncodedCNF.encode Φ.val) = Φ.val.clauses.length := by
  simp [AModel.cnfClauseCount, EncodedCNF.decode_encode Φ.val Φ.property]

end Paper2.ADecider

#print axioms Paper2.ADecider.canonical_layout
#print axioms Paper2.ADecider.exp_dims_pos
#print axioms Paper2.ADecider.targetD_mwOf
#print axioms Paper2.ADecider.accT_mwOf
#print axioms Paper2.ADecider.decider_error_at
#print axioms Paper2.ADecider.decider_error
#print axioms Paper2.ADecider.variableCount_encode
#print axioms Paper2.ADecider.cnfClauseCount_encode
