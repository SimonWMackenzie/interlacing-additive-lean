import Paper2.ASquare

/-!
# Paper A (lock v12): the square power-of-two variant of T24 (`thm:quantitative`, ledger U17)

Lane `owner:a-square-1` (private, 26 September 2026). Lock v12 `sections/06-reduction.tex:115-116`
("The conclusion also holds when the inputs are square matrices of power-of-two side length.")
and `144-150` ("let $S$ be the least power of two at least $m_Y$ ... $\log(S^2)=\log T+O(\log L)$;
the leading constant in \cref{eq:quantitative-size} is unchanged").

* (segment 1) `T24Square`: the literal target, `T24_endpoint`'s statement at the square count with
  the printed word replaced by the encoded square instance and the estimator reading the square
  table.
* (segment 3) `square_law_T24`: the law level from the admitted `T24_actual_cut` (square count)
  and exact preservation `D_squareTable`. No `hA3`.
* (segment 4) `square_log_T24`: `log₂ T ≤ log₂ S² ≤ log₂ T + 3 + log₂ L` with `S² = printedTsq`,
  `T = printedT`, `L = clog₂ n`, and `S² = 2^(2·exponent)`, from the admitted
  `Asymptotics.square_log_bounds` (itself from `ReductionDimensions.square_entries_lt`) and
  `SquarePadding.entries_pow`, at the T10 graph beyond the public-check cutoff (`entries_eq_printed`).
* (segment 2, composition part) `T24_square`: `T24Square` from `hA3`, D-A2, D-A6 (`cs`), D-A7 and
  the OPEN post-stage contract `SquarePost P CP EP`, by the admitted
  `BitMachineComposition.composition_outputsWithin` and the admitted `T24Runtime.subexponential`.

**No ledger row is closed.**
-/

set_option maxHeartbeats 4000000

namespace Paper2.ASquare

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2 Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics
open Paper2.AEndpoint

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

set_option hygiene false in
local notation "SEL" Φ:max k:max => TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
  (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) B.degreeBound (sourceGap D B) k

set_option hygiene false in
local notation "EXP" Φ:max k:max => TotalFiniteConstructorScratch.experiment (t10_vertices_pos D B Φ)
  (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) B.degreeBound (sourceGap D B) k

set_option hygiene false in
local notation "OUT" Φ:max k:max t:max => EncodedSelectedOutput.outputBits (t10_vertices_pos D B Φ)
  (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) B.degreeBound (sourceGap D B) k t

set_option hygiene false in
local notation "SQOUT" Φ:max k:max t:max => EncodedCommunication.encodeInstance (squareInstance
  (EncodedSelectedOutput.selectedInstance (t10_vertices_pos D B Φ)
  (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) B.degreeBound (sourceGap D B) k t))

set_option hygiene false in
local notation "SQE" Φ:max k:max t:max => squareTable (EXP Φ k).output t

set_option hygiene false in
local notation "TSQ" Φ:max k:max => printedTsq (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length
  B.degreeBound (sourceGap D B) k

set_option hygiene false in
local notation "TREC" Φ:max k:max => printedT (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length
  B.degreeBound (sourceGap D B) k

/-! ## Segment 1: the literal target statement -/

/-- **T24, square option (lock `06-reduction.tex:107-117`, `144-150`), target statement.** For the
sparsity density `cs` and `0 ≤ c < 1/12`: ONE machine `M`; for every `ε > 0` a cutoff `N₀`; for
every valid sparse `Φ` with `N ≥ N₀` and `k = kOf N`: `1 ≤ k`, random bits `≤ 2^(εN)`, on every
tape `M` prints exactly the encoded SQUARE power-of-two instance within `T ≤ 2^(εN)` steps, the
square has exactly `printedTsq` entries, and with `T = printedTsq`, `a = c·log₂T/log₂log₂T`, every
estimator of `D` of the SQUARE table with per-run accuracy `a` w.p. `≥ 2/3` makes the median
midpoint test at gap `k` err w.p. `≤ 1/100` (YES) and `≤ 2^-11 + 1/100 < 1/3` (NO). -/
def T24Square (L : EncodedComplexity.BinaryLanguage) (cs : ℕ) (c : ℝ) : Prop :=
  ∃ M : BitMachine.Machine, ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ Φ : ValidFormula,
    Φ.val.clauses.length ≤ cs * Φ.val.variables → N₀ ≤ Φ.val.variables →
    1 ≤ kOf Φ.val.variables ∧
    ((SEL Φ (kOf Φ.val.variables)).inputBits : ℝ) ≤ (2 : ℝ) ^ (ε * Φ.val.variables) ∧
    (∀ t : (SEL Φ (kOf Φ.val.variables)).Tape, ∃ T : ℕ,
      M.OutputsWithin
        (EncodedComplexity.pair (EncodedCNF.encode Φ.val)
          ((SEL Φ (kOf Φ.val.variables)).tapeBits t))
        (SQOUT Φ (kOf Φ.val.variables) t) T ∧
      (T : ℝ) ≤ (2 : ℝ) ^ (ε * Φ.val.variables)) ∧
    SquarePadding.entries (SEL Φ (kOf Φ.val.variables)).rows
        (SEL Φ (kOf Φ.val.variables)).cols = TSQ Φ (kOf Φ.val.variables) ∧
    let T : ℕ := TSQ Φ (kOf Φ.val.variables)
    let a : ℝ := c * (Real.logb 2 T / Real.logb 2 (Real.logb 2 T))
    ∀ {α : Type} [Fintype α] (μ : FiniteLaw α)
      (est : (EXP Φ (kOf Φ.val.variables)).output.Tape → α → ℝ),
      letI : Fintype (EXP Φ (kOf Φ.val.variables)).output.Tape :=
        (EXP Φ (kOf Φ.val.variables)).tapeFintype
      (∀ b, 2 / 3 ≤ μ.prob (fun t => |est b t - Workspace.Types.CommComplexity.D
        (SQE Φ (kOf Φ.val.variables) b)| ≤ a)) →
      (EncodedCNF.encode Φ.val ∈ L →
        ((EXP Φ (kOf Φ.val.variables)).tapeLaw.prod (μ.iid Unit4Shell.Amplification.reps)).prob
          (fun x => ¬ Unit4Shell.Shells.accepts est (EXP Φ (kOf Φ.val.variables)).output.budget
            (kOf Φ.val.variables) x) ≤ 1 / 100) ∧
      (EncodedCNF.encode Φ.val ∉ L →
        ((EXP Φ (kOf Φ.val.variables)).tapeLaw.prod (μ.iid Unit4Shell.Amplification.reps)).prob
          (fun x => Unit4Shell.Shells.accepts est (EXP Φ (kOf Φ.val.variables)).output.budget
            (kOf Φ.val.variables) x) ≤ (1 / 2) ^ 11 + 1 / 100 ∧
        (1 / 2 : ℝ) ^ 11 + 1 / 100 < 1 / 3)

/-! ## Segment 3: the law level for T24 -/

/-- **Square law, T24 (segment 3).** Beyond a cutoff, for every valid sparse `Φ`, an estimator of
`D` of the SQUARE table with accuracy `c·log₂T/log₂log₂T` (`T = printedTsq`) makes the midpoint
test err as in `T24Square`, on the actual reduction law. From the admitted `T24_actual_cut` at
`square = true` and exact preservation. No `hA3`. -/
theorem square_law_T24 (L : EncodedComplexity.BinaryLanguage) (hDA2 : DA2 L)
    (cs : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12) :
    ∃ N₀ : ℕ, ∀ Φ : ValidFormula, Φ.val.clauses.length ≤ cs * Φ.val.variables →
      N₀ ≤ Φ.val.variables →
      let T : ℕ := TSQ Φ (kOf Φ.val.variables)
      let a : ℝ := c * (Real.logb 2 T / Real.logb 2 (Real.logb 2 T))
      ∀ {α : Type} [Fintype α] (μ : FiniteLaw α)
        (est : (EXP Φ (kOf Φ.val.variables)).output.Tape → α → ℝ),
        letI : Fintype (EXP Φ (kOf Φ.val.variables)).output.Tape :=
          (EXP Φ (kOf Φ.val.variables)).tapeFintype
        (∀ b, 2 / 3 ≤ μ.prob (fun t => |est b t - Workspace.Types.CommComplexity.D
          (SQE Φ (kOf Φ.val.variables) b)| ≤ a)) →
        (EncodedCNF.encode Φ.val ∈ L →
          ((EXP Φ (kOf Φ.val.variables)).tapeLaw.prod (μ.iid Unit4Shell.Amplification.reps)).prob
            (fun x => ¬ Unit4Shell.Shells.accepts est (EXP Φ (kOf Φ.val.variables)).output.budget
              (kOf Φ.val.variables) x) ≤ 1 / 100) ∧
        (EncodedCNF.encode Φ.val ∉ L →
          ((EXP Φ (kOf Φ.val.variables)).tapeLaw.prod (μ.iid Unit4Shell.Amplification.reps)).prob
            (fun x => Unit4Shell.Shells.accepts est (EXP Φ (kOf Φ.val.variables)).output.budget
              (kOf Φ.val.variables) x) ≤ (1 / 2) ^ 11 + 1 / 100 ∧
          (1 / 2 : ℝ) ^ 11 + 1 / 100 < 1 / 3) := by
  obtain ⟨N₁, hN₁⟩ := Unit4Shell.T24ActualCut.T24_actual_cut D B cs c hc0 hc true
  refine ⟨N₁, fun Φ hsparse hN => ?_⟩
  intro T a α _ μ est hμ
  have he := exp_pos D B Φ (kOf Φ.val.variables)
  have hμ' : ∀ b, 2 / 3 ≤ μ.prob (fun t => |est b t - Workspace.Types.CommComplexity.D
      ((EXP Φ (kOf Φ.val.variables)).output.table b).matrix| ≤ a) := by
    intro b
    have h := hμ b
    rwa [D_squareTable _ he.1 he.2 b] at h
  have h := hN₁ Φ hsparse hN μ est hμ'
  exact ⟨fun hmem => h.1 ((hDA2 Φ).mp hmem), fun hnot => h.2 (fun hs => hnot ((hDA2 Φ).mpr hs))⟩

/-! ## Segment 4: the square asymptotics -/

/-- **T24 square size (segment 4), `06-reduction.tex:148-149`.** For every valid `Φ` with
`N ≥ Δ·sizeThreshold` and every `k`: the square has exactly `S² = printedTsq = 2^(2·exponent)`
entries with `S = side rows cols` the least power of two at least both dimensions, the rectangle
exactly `T = printedT = rows·cols` entries, and `log₂ T ≤ log₂ S² ≤ log₂ T + 3 + log₂ L`
(`L = clog₂ n ≥ 1`), i.e. `log(S²) = log T + O(log L)`. -/
theorem square_log_T24 (Φ : ValidFormula) (k : ℕ)
    (hN : B.degreeBound * CompletePublicScheduleScratch.sizeThreshold B.degreeBound (sourceGap D B)
      ≤ Φ.val.variables)
    (hL : 1 ≤ Nat.clog 2 (t10Graph D B Φ).vertices) :
    SquarePadding.entries (SEL Φ k).rows (SEL Φ k).cols = TSQ Φ k ∧
    (SEL Φ k).rows * (SEL Φ k).cols = TREC Φ k ∧
    TSQ Φ k = SquarePadding.side (SEL Φ k).rows (SEL Φ k).cols ^ 2 ∧
    TSQ Φ k = 2 ^ (2 * SquarePadding.exponent (SEL Φ k).rows (SEL Φ k).cols) ∧
    (SEL Φ k).cols ≤ SquarePadding.side (SEL Φ k).rows (SEL Φ k).cols ∧
    TREC Φ k ≤ TSQ Φ k ∧
    Real.logb 2 (TREC Φ k) ≤ Real.logb 2 (TSQ Φ k) ∧
    Real.logb 2 (TSQ Φ k) ≤
      Real.logb 2 (TREC Φ k) + 3 + Real.logb 2 (Nat.clog 2 (t10Graph D B Φ).vertices) := by
  have hent := entries_eq_printed D B Φ k (size_of_large D B Φ hN)
  have hs := sel_pos D B Φ k
  obtain ⟨hlog, hlow⟩ := square_log_bounds (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length
    B.degreeBound (sourceGap D B) k hL
  have hle : (SEL Φ k).rows * (SEL Φ k).cols ≤
      SquarePadding.entries (SEL Φ k).rows (SEL Φ k).cols :=
    Nat.mul_le_mul (SquarePadding.rows_le_side _ _) (SquarePadding.cols_le_side _ _)
  have hTle : TREC Φ k ≤ TSQ Φ k := by rw [← hent.1, ← hent.2]; exact hle
  have hpos : 0 < TREC Φ k := by
    rw [← hent.1]; exact Nat.mul_pos hs.1 hs.2
  refine ⟨hent.2, hent.1, ?_, ?_, SquarePadding.cols_le_side _ _, hTle, ?_, hlog⟩
  · rw [← hent.2, SquarePadding.entries, sq]
  · rw [← hent.2, SquarePadding.entries_pow]
  · apply Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hpos)
    exact_mod_cast hTle

/-! ## Segment 2 (composition part): T24 square from the post-stage contract -/

/-- Real clock arithmetic of the two-stage T24 machine: every quantity below `u ≥ 4`. -/
theorem clock_real (u T I o pb CP : ℝ) (EP : ℕ) (hu : 4 ≤ u) (hT : T ≤ u)
    (hI : I ≤ 2 * u) (ho0 : 0 ≤ o) (ho : o ≤ I + T * pb) (hpb0 : 0 ≤ pb) (hpb : pb ≤ u)
    (hCP : CP ≤ u) :
    T + 2 * o + 2 + CP * (o + 1) ^ EP ≤ u ^ (3 * EP + 4) := by
  have hu1 : 1 ≤ u := by linarith
  have hTpb : T * pb ≤ u * u := mul_le_mul hT hpb hpb0 (by linarith)
  have ho' : o ≤ 2 * u + u * u := by linarith
  have ho1 : o + 1 ≤ u ^ 3 := by nlinarith
  have hpow : (o + 1) ^ EP ≤ (u ^ 3) ^ EP := pow_le_pow_left₀ (by linarith) ho1 EP
  have hK : CP * (o + 1) ^ EP ≤ u * (u ^ 3) ^ EP :=
    mul_le_mul hCP hpow (by positivity) (by linarith)
  have hK' : u * (u ^ 3) ^ EP = u ^ (3 * EP + 1) := by
    rw [← pow_mul, pow_succ]; ring
  have hA : T + 2 * o + 2 ≤ u ^ 3 := by nlinarith
  have h3 : u ^ 3 ≤ u ^ (3 * EP + 3) := pow_le_pow_right₀ hu1 (by omega)
  have h1 : u ^ (3 * EP + 1) ≤ u ^ (3 * EP + 3) := pow_le_pow_right₀ hu1 (by omega)
  have h4 : u ^ (3 * EP + 4) = u * u ^ (3 * EP + 3) := by rw [pow_succ]; ring
  have hp : 0 ≤ u ^ (3 * EP + 3) := by positivity
  rw [h4]
  nlinarith

/-- **T24, square option, from the post-stage contract.** Modulo `hA3`, D-A2, D-A6 (`cs`), D-A7
and the OPEN post stage `SquarePost P CP EP`: the machine `composition M P` (`M` the T24 machine of
`T24_endpoint`, which computes `kOf N` itself) witnesses `T24Square`. -/
theorem T24_square (L : EncodedComplexity.BinaryLanguage) (hDA2 : DA2 L)
    (hA3 : Unit4Shell.Shells.H_A3 B.degreeBound (sourceGap D B))
    (cs : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12)
    (P : BitMachine.Machine) (CP EP : ℕ) (hP : SquarePost P CP EP) :
    T24Square D B L cs c := by
  obtain ⟨M, hM⟩ := T24_endpoint D B L hDA2 hA3 cs c hc0 hc true
  obtain ⟨N₁, hN₁⟩ := square_law_T24 D B L hDA2 cs c hc0 hc
  refine ⟨BitMachineComposition.composition M P, fun ε hε => ?_⟩
  set δ : ℝ := ε / (3 * EP + 4) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδε : δ ≤ ε := by
    have h1 : (1 : ℝ) ≤ 3 * EP + 4 := by
      have : (0 : ℝ) ≤ EP := Nat.cast_nonneg _
      linarith
    exact div_le_self hε.le h1
  obtain ⟨N₂, hN₂⟩ := hM δ hδ0
  obtain ⟨N₃, hN₃⟩ := Unit4Shell.T24Runtime.subexponential 3 0 δ hδ0
  obtain ⟨N₄, hN₄⟩ := Unit4Shell.T24Runtime.subexponential 1 0 δ hδ0
  refine ⟨max (max (max N₁ N₂) (max N₃ N₄))
    (max (max (28 * cs + 9) (M.pushBound + CP)) (max ⌈2 / δ⌉₊ 1)), ?_⟩
  intro Φ hsparse hN
  set N := Φ.val.variables with hNdef
  have hA : max (max N₁ N₂) (max N₃ N₄) ≤ N := le_trans (le_max_left _ _) hN
  have hB : max (max (28 * cs + 9) (M.pushBound + CP)) (max ⌈2 / δ⌉₊ 1) ≤ N :=
    le_trans (le_max_right _ _) hN
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hA
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hA
  have hN3 : N₃ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hA
  have hN4 : N₄ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hA
  have hcs : 28 * cs + 9 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hB
  have hK : M.pushBound + CP ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hB
  have hδN : ⌈2 / δ⌉₊ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hB
  have hN1le : 1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hB
  obtain ⟨hk, hbits, hrun, -, hent2, -⟩ := hN₂ Φ hsparse hN2
  -- `u = 2^(δN)`
  set u : ℝ := (2 : ℝ) ^ (δ * N) with hu
  have hu4 : 4 ≤ u := by
    have h2 : (2 : ℝ) ≤ δ * N := by
      have := (Nat.le_ceil (2 / δ)).trans (show ((⌈2 / δ⌉₊ : ℕ) : ℝ) ≤ (N : ℝ) by exact_mod_cast hδN)
      rw [div_le_iff₀ hδ0] at this
      linarith
    calc (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by norm_num
      _ ≤ u := Real.rpow_le_rpow_of_exponent_le (by norm_num) h2
  have hNself : N ≤ N * (Nat.clog 2 (N + 2)) ^ 0 := by simp
  have hsub3 := hN₃ N hN3 N hN1le hNself
  have hsub1 := hN₄ N hN4 N hN1le hNself
  have hN2R : (((N + 2 : ℕ) : ℝ)) ≥ 1 := by
    have : (1 : ℕ) ≤ N + 2 := by omega
    exact_mod_cast this
  have hcube : (((N + 2) ^ 3 : ℕ) : ℝ) ≤ u := by
    have hle : (((N + 2) ^ 3 : ℕ) : ℝ) ≤ (((N + 2 : ℕ) : ℝ)) ^ (3 * (kOf N + 1)) := by
      push_cast
      exact pow_le_pow_right₀ (by exact_mod_cast (show (1 : ℕ) ≤ N + 2 by omega))
        (by nlinarith)
    exact hle.trans hsub3
  have hlin : (((N + 2 : ℕ) : ℝ)) ≤ u := by
    have hle : (((N + 2 : ℕ) : ℝ)) ≤ (((N + 2 : ℕ) : ℝ)) ^ (1 * (kOf N + 1)) := by
      calc (((N + 2 : ℕ) : ℝ)) = (((N + 2 : ℕ) : ℝ)) ^ 1 := (pow_one _).symm
        _ ≤ _ := pow_le_pow_right₀ hN2R (by omega)
    exact hle.trans hsub1
  have hpbR : (M.pushBound : ℝ) ≤ u :=
    le_trans (by exact_mod_cast (show M.pushBound ≤ N + 2 by omega)) hlin
  have hCPR : (CP : ℝ) ≤ u :=
    le_trans (by exact_mod_cast (show CP ≤ N + 2 by omega)) hlin
  have huR : u ^ (3 * EP + 4) = (2 : ℝ) ^ (ε * N) := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    rw [hδ]
    push_cast
    field_simp
  have hδεN : (2 : ℝ) ^ (δ * N) ≤ (2 : ℝ) ^ (ε * N) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_right hδε (Nat.cast_nonneg _))
  refine ⟨hk, le_trans hbits ?_, fun t => ?_, hent2, ?_⟩
  · -- random bits: `2^(δN) ≤ 2^(εN)`
    exact hδεN
  · obtain ⟨T, hrunT, hTR⟩ := hrun t
    have hs := sel_pos D B Φ (kOf N)
    have hvalid := EncodedSelectedOutput.instanceOf_valid ((SEL Φ (kOf N)).table t)
      (SEL Φ (kOf N)).budget hs.1 hs.2
    have hPrun := hP _ hvalid
    change P.OutputsWithin (OUT Φ (kOf N) t) (SQOUT Φ (kOf N) t)
      (CP * ((OUT Φ (kOf N) t).length + 1) ^ EP) at hPrun
    have hC := BitMachineComposition.composition_outputsWithin M P hrunT hPrun
    refine ⟨_, hC, ?_⟩
    have ho := BitMachine.output_length_bound M hrunT
    have hlen := Unit4Shell.RandomBits.tape_length_eq D B Φ (kOf N) t
    have hpl := EncodedComplexity.pair_length (EncodedCNF.encode Φ.val)
      ((SEL Φ (kOf N)).tapeBits t)
    have henc : 2 * (EncodedCNF.encode Φ.val).length + 3 ≤ (N + 2) ^ 3 :=
      Unit4Shell.T24RuntimeComposed.encode_length_cube cs Φ hsparse hcs
    -- the input length is at most `2u`
    have hIR : (((EncodedComplexity.pair (EncodedCNF.encode Φ.val)
        ((SEL Φ (kOf N)).tapeBits t)).length : ℕ) : ℝ) ≤ 2 * u := by
      rw [hpl, hlen]
      have h1 : 2 * (EncodedCNF.encode Φ.val).length + 1 ≤ (N + 2) ^ 3 := by omega
      have h1R : ((2 * (EncodedCNF.encode Φ.val).length + 1 : ℕ) : ℝ) ≤ u :=
        le_trans (by exact_mod_cast h1) hcube
      push_cast at h1R ⊢
      linarith
    have hoR : (((OUT Φ (kOf N) t).length : ℕ) : ℝ) ≤
        (((EncodedComplexity.pair (EncodedCNF.encode Φ.val)
          ((SEL Φ (kOf N)).tapeBits t)).length : ℕ) : ℝ) + (T : ℝ) * (M.pushBound : ℝ) := by
      exact_mod_cast ho
    have hTR' : (T : ℝ) ≤ u := hTR
    have hmain := clock_real u (T : ℝ) _ _ (M.pushBound : ℝ) (CP : ℝ) EP hu4
      hTR' hIR (Nat.cast_nonneg _) hoR (Nat.cast_nonneg _) hpbR hCPR
    rw [huR] at hmain
    push_cast
    exact hmain
  · intro T a α _ μ est hμ
    exact hN₁ Φ hsparse hN1 μ est hμ

#print axioms square_law_T24
#print axioms square_log_T24
#print axioms clock_real
#print axioms T24_square

end Paper2.ASquare
