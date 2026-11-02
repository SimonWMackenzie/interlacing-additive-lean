import Paper2.AEndpoint

/-!
# T02 class level from the law level: `NP ⊆ BPP` modulo ONE explicit machine-realization contract (U18)

Lane `owner:a-endpoint-1` (private, 26 September 2026). This replaces the thin premise `hU18 : C L` of
`AEndpoint.T02_class_bpp` by an explicit machine contract `U18Decider` in the DRAFT randomized model
`Unit4Shell.Definitions.RandomizedAlgorithm` (D-A1 recommended shape; a draft, not an author choice): a polynomial
randomized algorithm whose acceptance probability on every valid formula EQUALS the acceptance probability of the
median-of-147 midpoint test at gap `k` on the ACTUAL reduction law and some estimator law of per-run accuracy `a`,
and which never accepts an input that is not the encoding of a valid formula. Building such an algorithm from a
polynomial estimator (U18: estimator runs, median, comparison, tape split, product-law identification, validator) is
OPEN and has no lane; everything else (error analysis, `BPP` membership, `NP ⊆ BPP`) is proved here from the law-level
`T02_endpoint_law`. No new machine; no ledger row is closed.
-/

set_option maxHeartbeats 4000000

namespace Paper2.AEndpoint

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2 Paper2.Unit4Shell.T10Finite

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

set_option hygiene false in
local notation "EXP" Φ:max k:max => TotalFiniteConstructorScratch.experiment (t10_vertices_pos D B Φ)
  (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) B.degreeBound (sourceGap D B) k

/-- **OPEN machine contract U18 (no lane; NOT an author decision).** `A` is a polynomial randomized algorithm
(DRAFT model) such that (i) it never accepts an input that is not the encoding of a valid formula, and (ii) for
every valid `Φ` there is an estimator law `μ` and reading `est` of the actual reduction tape with per-run accuracy
`a` (probability `≥ 2/3` for every reduction tape) such that `A` accepts `encode Φ` with exactly the probability
that the median-of-147 midpoint test at gap `k` accepts under the actual reduction law times `μ^147`. -/
def U18Decider (a : ℝ) (k : ℕ) (A : Unit4Shell.Definitions.RandomizedAlgorithm) : Prop :=
  A.Polynomial ∧
  (∀ input, (¬ ∃ Φ : ValidFormula, EncodedCNF.encode Φ.val = input) →
    A.prob input (· = [true]) = 0) ∧
  ∀ Φ : ValidFormula, ∃ (α : Type) (_ : Fintype α) (μ : FiniteLaw α)
    (est : (EXP Φ k).output.Tape → α → ℝ),
    (letI : Fintype (EXP Φ k).output.Tape := (EXP Φ k).tapeFintype
     (∀ b, 2 / 3 ≤ μ.prob (fun t => |est b t -
        Workspace.Types.CommComplexity.D ((EXP Φ k).output.table b).matrix| ≤ a)) ∧
     A.prob (EncodedCNF.encode Φ.val) (· = [true]) =
       ((EXP Φ k).tapeLaw.prod (μ.iid Unit4Shell.Amplification.reps)).prob
         (fun x => Unit4Shell.Shells.accepts est (EXP Φ k).output.budget k x))

/-- **T02 (first clause) at class level, modulo the U18 contract.** For every fixed `a ≥ 0`: if some algorithm
satisfies the U18 contract at the fixed gap `gapOf a` (D-A1 draft model), then for every error bound
`err ≥ 2^-11 + 1/100` (D-A4; e.g. `1/3`) the language `L` (D-A2, containing only encodings of valid formulas) is in
the DRAFT `InBPP err`; with the Cook-Levin contract `NPHard L` (D-A5) and closure of `InBPP err` under the banked
reductions (D-A4, machine level), every `InNP` language is in `InBPP err`. -/
theorem T02_bpp_of_U18 (L : EncodedComplexity.BinaryLanguage) (hDA2 : DA2 L)
    (hLvalid : ∀ input ∈ L, ∃ Φ : ValidFormula, EncodedCNF.encode Φ.val = input)
    (a : ℝ) (ha : 0 ≤ a) (err : ℝ) (herr : (1 / 2 : ℝ) ^ 11 + 1 / 100 ≤ err)
    (hU18 : ∃ A, U18Decider D B a (gapOf a) A) :
    Unit4Shell.Definitions.InBPP err L ∧
    (Unit4Shell.ClassLemmas.ReductionClosed (Unit4Shell.Definitions.InBPP err) →
      EncodedComplexity.NPHard L →
      ∀ L', EncodedComplexity.InNP L' → Unit4Shell.Definitions.InBPP err L') := by
  obtain ⟨A, hpoly, hbad, hgood⟩ := hU18
  have hlaw := (T02_endpoint_law D B L hDA2 a ha).2.2
  have hmem : Unit4Shell.Definitions.InBPP err L := by
    refine ⟨A, hpoly, fun input => ⟨fun hin => ?_, fun hout => ?_⟩⟩
    · obtain ⟨Φ, rfl⟩ := hLvalid input hin
      obtain ⟨α, _, μ, est, hacc, heq⟩ := hgood Φ
      have h := ((hlaw Φ).1 μ est hacc).1 hin
      letI := (EXP Φ (gapOf a)).tapeFintype
      rw [Unit4Shell.Amplification.prob_not] at h
      rw [heq]
      have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ 11 := by positivity
      linarith
    · by_cases hv : ∃ Φ : ValidFormula, EncodedCNF.encode Φ.val = input
      · obtain ⟨Φ, rfl⟩ := hv
        obtain ⟨α, _, μ, est, hacc, heq⟩ := hgood Φ
        have h := (((hlaw Φ).1 μ est hacc).2 hout).1
        rw [heq]
        linarith
      · rw [hbad input hv]
        have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ 11 + 1 / 100 := by positivity
        linarith
  exact ⟨hmem, fun hC hCL => Unit4Shell.DocFix.np_subset_of_hard_mem _ hC hCL hmem⟩

/-- An event holding at every point has probability one. -/
theorem prob_of_forall {α : Type} [Fintype α] (μ : FiniteLaw α) (E : α → Prop) (h : ∀ x, E x) :
    μ.prob E = 1 := by
  classical
  unfold FiniteLaw.prob
  simp only [h, if_true]
  exact μ.total

/-- **OPEN machine contract U18, one-sided form (no lane; NOT an author decision).** `A` is a polynomial
randomized algorithm (DRAFT model) with a polynomial-time rejection indicator `reject` on `pair input tape`
(exactly the non-accepting runs on tapes of the right length, and `false` on tapes of another length); it never
accepts an input that is not the encoding of a valid formula; and for every valid `Φ` there are a DETERMINISTIC
estimate `e` of `D(table b)` within `a` on every actual reduction tape `b` and a tape map `π` from `A`'s tapes to
reduction tapes, pushing the uniform tape law forward to the actual reduction law, with `A` accepting on tape
`tape` exactly when `e (π tape) < budget + k/2`. -/
def U18OneSided (a : ℝ) (k : ℕ) (A : Unit4Shell.Definitions.RandomizedAlgorithm)
    (reject : List Bool → Bool) : Prop :=
  A.Polynomial ∧ BitMachine.Polytime (fun code => [reject code]) ∧
  (∀ input (tape : Fin (A.tapeLength input) → Bool),
    reject (EncodedComplexity.pair input (List.ofFn tape)) = true ↔
      A.output input (List.ofFn tape) ≠ [true]) ∧
  (∀ input tape, tape.length ≠ A.tapeLength input →
    reject (EncodedComplexity.pair input tape) = false) ∧
  (∀ input, (¬ ∃ Φ : ValidFormula, EncodedCNF.encode Φ.val = input) →
    ∀ tape : Fin (A.tapeLength input) → Bool, A.output input (List.ofFn tape) ≠ [true]) ∧
  ∀ Φ : ValidFormula, ∃ (e : (EXP Φ k).output.Tape → ℝ)
    (π : (Fin (A.tapeLength (EncodedCNF.encode Φ.val)) → Bool) → (EXP Φ k).output.Tape),
    (∀ b, |e b - Workspace.Types.CommComplexity.D ((EXP Φ k).output.table b).matrix| ≤ a) ∧
    (∀ tape, A.output (EncodedCNF.encode Φ.val) (List.ofFn tape) = [true] ↔
      e (π tape) < ((EXP Φ k).output.budget : ℝ) + (k : ℝ) / 2) ∧
    ∀ P : (EXP Φ k).output.Tape → Prop,
      (Unit4Shell.Definitions.uniformTape (A.tapeLength (EncodedCNF.encode Φ.val))).prob
          (fun tape => P (π tape)) =
        @FiniteLaw.prob _ (EXP Φ k).tapeFintype (EXP Φ k).tapeLaw P

/-- **T02 (second clause) at class level, modulo the one-sided U18 contract: `NP = coNP`.** For every fixed
`a ≥ 0`: if some algorithm and rejection indicator satisfy the one-sided U18 contract at the gap `gapOf a`
(an always-correct deterministic estimator composed with the reduction), then `L` (D-A2, containing only
encodings of valid formulas) has the one-sided normal form, hence is in the DRAFT `coNP`; with the Cook-Levin
contract `NPHard L` (D-A5) and the reduction closure of `InNP` (machine level), `NP = coNP` (DRAFT `NPEqCoNP`).
The probabilistic content is `T02_endpoint_law` (deterministic clause). -/
theorem T02_coNP_of_U18 (L : EncodedComplexity.BinaryLanguage) (hDA2 : DA2 L)
    (hLvalid : ∀ input ∈ L, ∃ Φ : ValidFormula, EncodedCNF.encode Φ.val = input)
    (a : ℝ) (ha : 0 ≤ a)
    (hU18 : ∃ A reject, U18OneSided D B a (gapOf a) A reject) :
    Unit4Shell.ClassLemmas.OneSidedRejectShape L ∧
    (Unit4Shell.ClassLemmas.ReductionClosed EncodedComplexity.InNP →
      EncodedComplexity.NPHard L → Unit4Shell.ClassLemmas.NPEqCoNP) := by
  obtain ⟨A, reject, hpoly, hrej, hspec, hlong, hbad, hgood⟩ := hU18
  have hlaw := (T02_endpoint_law D B L hDA2 a ha).2.2
  have hone : A.DecidesOneSided L := by
    intro input
    refine ⟨fun hin tape => ?_, fun hout => ?_⟩
    · obtain ⟨Φ, rfl⟩ := hLvalid input hin
      obtain ⟨e, π, he, hacc, -⟩ := hgood Φ
      exact (hacc tape).mpr (((hlaw Φ).2 e he).1 hin (π tape))
    · by_cases hv : ∃ Φ : ValidFormula, EncodedCNF.encode Φ.val = input
      · obtain ⟨Φ, rfl⟩ := hv
        obtain ⟨e, π, he, hacc, hpush⟩ := hgood Φ
        have hno := ((hlaw Φ).2 e he).2 hout
        have h1 : (Unit4Shell.Definitions.uniformTape (A.tapeLength (EncodedCNF.encode Φ.val))).prob
            (fun tape => ¬ (e (π tape) < ((EXP Φ (gapOf a)).output.budget : ℝ) + (gapOf a : ℝ) / 2)) ≤
            A.prob (EncodedCNF.encode Φ.val) (· ≠ [true]) := by
          unfold Unit4Shell.Definitions.RandomizedAlgorithm.prob
          exact FiniteLaw.prob_mono _ (fun tape ht hout' => ht ((hacc tape).mp hout'))
        rw [hpush (fun b => ¬ (e b < ((EXP Φ (gapOf a)).output.budget : ℝ) + (gapOf a : ℝ) / 2))] at h1
        have h2 := @FiniteLaw.prob_mono _ (EXP Φ (gapOf a)).tapeFintype (EXP Φ (gapOf a)).tapeLaw
          (fun b => ((EXP Φ (gapOf a)).output.budget : ℝ) + (gapOf a : ℝ) / 2 < e b)
          (fun b => ¬ (e b < ((EXP Φ (gapOf a)).output.budget : ℝ) + (gapOf a : ℝ) / 2))
          (fun b hb => not_lt.mpr hb.le)
        have h3 : (1 / 2 : ℝ) ≤ 1 - (1 / 2 : ℝ) ^ 11 := by norm_num
        linarith
      · have h := prob_of_forall
          (Unit4Shell.Definitions.uniformTape (A.tapeLength input))
          (fun tape => A.output input (List.ofFn tape) ≠ [true]) (hbad input hv)
        unfold Unit4Shell.Definitions.RandomizedAlgorithm.prob
        rw [h]
        norm_num
  have hshape := Unit4Shell.Definitions.oneSided_shape_of_decides A hpoly hone reject hrej hspec hlong
  exact ⟨hshape, fun hNP hCL => Unit4Shell.DocFix.np_eq_coNP_of_hard_mem_coNP hNP hCL
    (Unit4Shell.DocFix.coNP_of_oneSided hshape)⟩

/-- **OPEN machine contract U18, growing-gap form (no lane; NOT an author decision)**, for one sparsity density
`cs`, one `c`, one output shape `square`, error `err`, and the D-A6 parameters `vc`, `cc` (variable and clause
counts read from the input) and `withPoly`. For every cutoff `N₁` there is a randomized algorithm `A` (DRAFT
model) with the `def:reth`-shaped subexponential time bound on well-formed sparse inputs, which decides `L` with
error `err` directly below `N₁` (the finite small-input branch), and which from `N₁` on accepts every sparse valid
`Φ` with exactly the acceptance probability of the median-of-147 midpoint test at the gap `kOf N` on the actual
reduction law and an estimator law of per-run accuracy `c·log₂T/log₂log₂T`, `T` the printed (or square-padded)
entry count. -/
def U18Growing (cs : ℕ) (c : ℝ) (square : Bool) (err : ℝ) (L : EncodedComplexity.BinaryLanguage)
    (vc cc : List Bool → ℕ) (withPoly : Bool) : Prop :=
  ∀ N₁ : ℕ, ∃ A : Unit4Shell.Definitions.RandomizedAlgorithm,
    (∀ ε : ℝ, 0 < ε → ∃ C d N₀ : ℕ, ∀ input, (∃ Φ : ValidFormula, EncodedCNF.encode Φ.val = input) →
      cc input ≤ cs * vc input → N₀ ≤ vc input →
      A.time input ≤ C * ⌈(2 : ℝ) ^ (ε * vc input)⌉₊ *
        (if withPoly then (input.length + 1) ^ d else 1)) ∧
    (∀ Φ : ValidFormula, Φ.val.clauses.length ≤ cs * Φ.val.variables → Φ.val.variables < N₁ →
      (EncodedCNF.encode Φ.val ∈ L → 1 - err ≤ A.prob (EncodedCNF.encode Φ.val) (· = [true])) ∧
      (EncodedCNF.encode Φ.val ∉ L → A.prob (EncodedCNF.encode Φ.val) (· = [true]) ≤ err)) ∧
    (∀ Φ : ValidFormula, Φ.val.clauses.length ≤ cs * Φ.val.variables → N₁ ≤ Φ.val.variables →
      ∃ (α : Type) (_ : Fintype α) (μ : FiniteLaw α)
        (est : (EXP Φ (Unit4Shell.Asymptotics.kOf Φ.val.variables)).output.Tape → α → ℝ),
        letI : Fintype (EXP Φ (Unit4Shell.Asymptotics.kOf Φ.val.variables)).output.Tape :=
          (EXP Φ (Unit4Shell.Asymptotics.kOf Φ.val.variables)).tapeFintype
        (∀ b, 2 / 3 ≤ μ.prob (fun t => |est b t - Workspace.Types.CommComplexity.D
          ((EXP Φ (Unit4Shell.Asymptotics.kOf Φ.val.variables)).output.table b).matrix| ≤
            c * (Real.logb 2 ((if square then
                Unit4Shell.Asymptotics.printedTsq (t10Graph D B Φ).vertices
                  (t10Graph D B Φ).edges.length B.degreeBound (sourceGap D B)
                  (Unit4Shell.Asymptotics.kOf Φ.val.variables)
              else Unit4Shell.Asymptotics.printedT (t10Graph D B Φ).vertices
                  (t10Graph D B Φ).edges.length B.degreeBound (sourceGap D B)
                  (Unit4Shell.Asymptotics.kOf Φ.val.variables) : ℕ) : ℝ) /
              Real.logb 2 (Real.logb 2 ((if square then
                Unit4Shell.Asymptotics.printedTsq (t10Graph D B Φ).vertices
                  (t10Graph D B Φ).edges.length B.degreeBound (sourceGap D B)
                  (Unit4Shell.Asymptotics.kOf Φ.val.variables)
              else Unit4Shell.Asymptotics.printedT (t10Graph D B Φ).vertices
                  (t10Graph D B Φ).edges.length B.degreeBound (sourceGap D B)
                  (Unit4Shell.Asymptotics.kOf Φ.val.variables) : ℕ) : ℝ))))) ∧
        A.prob (EncodedCNF.encode Φ.val) (· = [true]) =
          ((EXP Φ (Unit4Shell.Asymptotics.kOf Φ.val.variables)).tapeLaw.prod
            (μ.iid Unit4Shell.Amplification.reps)).prob
            (fun x => Unit4Shell.Shells.accepts est
              (EXP Φ (Unit4Shell.Asymptotics.kOf Φ.val.variables)).output.budget
              (Unit4Shell.Asymptotics.kOf Φ.val.variables) x))

/-- **T24 at class level (lock v12 `thm:quantitative`), modulo the growing-gap U18 contract and D-A6.** Fix
`0 ≤ c < 1/12`, an output shape, an error `err ≥ 2^-11 + 1/100`, and the D-A6 parameters (`vc`, `cc` agreeing with
the variable and clause counts on valid encodings; `withPoly`). If for EVERY sparsity density the growing-gap U18
contract holds (an estimator of additive error `c·log₂T/log₂log₂T`, polynomial in `T`, composed with the reduction
within `2^{o(N)}`), then the DRAFT randomized sparse ETH (`Definitions.RandomizedSparseETH`, D04 shape D-A6) FAILS
for `L` (D-A2) on well-formed = valid-formula encodings. Equivalently: randomized sparse ETH refutes every such
contract. The probabilistic and asymptotic content is the admitted `T24ActualCut.T24_actual_cut`. -/
theorem T24_class_of_U18 (L : EncodedComplexity.BinaryLanguage) (hDA2 : DA2 L)
    (vc cc : List Bool → ℕ)
    (hvc : ∀ Φ : ValidFormula, vc (EncodedCNF.encode Φ.val) = Φ.val.variables)
    (hcc : ∀ Φ : ValidFormula, cc (EncodedCNF.encode Φ.val) = Φ.val.clauses.length)
    (err : ℝ) (herr : (1 / 2 : ℝ) ^ 11 + 1 / 100 ≤ err) (withPoly : Bool)
    (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12) (square : Bool)
    (hU18 : ∀ cs : ℕ, U18Growing D B cs c square err L vc cc withPoly) :
    ¬ Unit4Shell.Definitions.RandomizedSparseETH L
      (fun input => ∃ Φ : ValidFormula, EncodedCNF.encode Φ.val = input) vc cc err withPoly := by
  rintro ⟨cs, hno⟩
  obtain ⟨N₀, hN₀⟩ := Unit4Shell.T24ActualCut.T24_actual_cut D B cs c hc0 hc square
  obtain ⟨A, htime, hsmall, hlarge⟩ := hU18 cs N₀
  apply hno
  refine ⟨A, fun input hwf hsp => ?_, htime⟩
  obtain ⟨Φ, rfl⟩ := hwf
  rw [hvc Φ, hcc Φ] at hsp
  by_cases hN : Φ.val.variables < N₀
  · exact hsmall Φ hsp hN
  · have hN' : N₀ ≤ Φ.val.variables := Nat.le_of_not_lt hN
    obtain ⟨α, _, μ, est, hacc, heq⟩ := hlarge Φ hsp hN'
    have h := hN₀ Φ hsp hN' μ est hacc
    refine ⟨fun hin => ?_, fun hout => ?_⟩
    · have h1 := h.1 ((hDA2 Φ).mp hin)
      letI := (EXP Φ (Unit4Shell.Asymptotics.kOf Φ.val.variables)).tapeFintype
      rw [Unit4Shell.Amplification.prob_not] at h1
      rw [heq]
      have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ 11 := by positivity
      linarith
    · have h2 := (h.2 (fun hs => hout ((hDA2 Φ).mpr hs))).1
      rw [heq]
      linarith

end Paper2.AEndpoint

#print axioms Paper2.AEndpoint.T02_bpp_of_U18
#print axioms Paper2.AEndpoint.prob_of_forall
#print axioms Paper2.AEndpoint.T02_coNP_of_U18
#print axioms Paper2.AEndpoint.T24_class_of_U18
