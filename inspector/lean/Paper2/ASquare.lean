import Paper2.AEndpoint
import EthInapproximability.CurrentPaper.BitMachineComposition

/-!
# Paper A (lock v12): the square power-of-two variants of T01 and T24 (ledger U17)

Lane `owner:a-square-1` (private, 26 September 2026). Imports the frozen private object
`AEndpoint` (lane a-endpoint-owner-1, wave16-a11 under admission; object hash checked against its
RECEIPT) and admitted production modules only.

Lock v12 source (`papers/randomized-additive-hardness/versions/2026-09-22-protocol-labels-v12/source/`):

* `sections/01-introduction.tex:92` (`intro:theorem`): "The output can be a square matrix of
  power-of-two side length."
* `sections/06-reduction.tex:83-86`: "To obtain its square power-of-two version, repeat rows and
  columns until both dimensions equal the least power of two above the larger original dimension.
  Retaining every original label preserves $\D$ exactly, and the square still has polynomial size
  for fixed $k$."
* `sections/06-reduction.tex:115-116` (`thm:quantitative`): "The conclusion also holds when the
  inputs are square matrices of power-of-two side length."; proof `144-150`: "let $S$ be the least
  power of two at least $m_Y$, and repeat rows and columns until both dimensions are $S$. Every
  original row and column is retained, so these repetitions preserve communication complexity
  exactly. Since $m_Y/m_X=\Theta(L)$, $\log(S^2)=\log T+O(\log L)$".

The lock states the square version as an ADDITIONAL claim of the theorems (not as a D-A3
choice); it is formalized here as such. The padding is the banked `SquarePadding` (least power
of two `side m n = 2^clog₂(max m n)` at least both dimensions, cyclic repetition `i % d`); the
budget is the unchanged public integer `B`.

Contents:
1. (segment 1) the generic square instance `squareInstance`, the square table `squareTable` of a
   selected output, the printed square word `SQOUT`, and the literal target statements
   `T01Square` / `T24Square` (Props, same author-decision parameters as `AEndpoint`);
2. (segment 3) the law level: `D` of the square table equals `D` of the printed table, so the YES
   bound and the NO probability transfer verbatim (`square_law_T01`);
3. (segment 2, composition part) `T01_square`: `T01Square` from `hA3`, D-A1, D-A2, D-A7 and ONE
   explicit physical post-stage contract `SquarePost P CP EP` (a fixed machine printing the
   square instance from the encoded instance within a polynomial clock), by the admitted
   `BitMachineComposition.composition_outputsWithin`.

**No ledger row is closed.** `SquarePost` is NOT proved here (see the checkpoint).
-/

set_option maxHeartbeats 4000000

namespace Paper2.ASquare

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2 Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics
open Paper2.AEndpoint

/-! ## The generic square instance (no positivity needed in the definition) -/

/-- The square power-of-two table of a row-major word with `r` rows and `c` columns: entry
`(x, y)` of the `side r c × side r c` table is entry `(x % r, y % c)` of the word. -/
def squareFun (r c : ℕ) (bits : List Bool) :
    Fin (SquarePadding.side r c) → Fin (SquarePadding.side r c) → Bool :=
  fun x y => bits[(x.val % r) * c + y.val % c]?.getD false

/-- The square power-of-two instance: dimensions `side × side` (a power of two, at least both
original dimensions), the SAME public integer, and the row-major square table. -/
def squareInstance (I : EncodedCommunication.Instance) : EncodedCommunication.Instance :=
  ⟨SquarePadding.side I.rows I.cols, SquarePadding.side I.rows I.cols, I.threshold,
    MatrixMaterialization.rowMajor (squareFun I.rows I.cols I.table)⟩

/-- On a valid rectangle, the square function is the banked padding of the decoded table. -/
theorem squareFun_eq_matrix {r c : ℕ} (hr : 0 < r) (hc : 0 < c) (bits : List Bool) :
    squareFun r c bits = SquarePadding.matrix hr hc (ProtocolVerifier.tableGame r c bits) := by
  funext x y
  rfl

theorem squareInstance_valid (I : EncodedCommunication.Instance) :
    (squareInstance I).Valid :=
  ⟨SquarePadding.side_pos _ _, SquarePadding.side_pos _ _, by
    simp only [squareInstance, MatrixMaterialization.rowMajor_length]⟩

/-- Power-of-two side length, both dimensions equal. -/
theorem squareInstance_side (I : EncodedCommunication.Instance) :
    (squareInstance I).rows = 2 ^ SquarePadding.exponent I.rows I.cols ∧
    (squareInstance I).cols = 2 ^ SquarePadding.exponent I.rows I.cols ∧
    I.rows ≤ (squareInstance I).rows ∧ I.cols ≤ (squareInstance I).cols ∧
    (∀ e, I.rows ≤ 2 ^ e → I.cols ≤ 2 ^ e → (squareInstance I).rows ≤ 2 ^ e) :=
  ⟨rfl, rfl, SquarePadding.rows_le_side _ _, SquarePadding.cols_le_side _ _,
    fun e hr hc => SquarePadding.side_minimal _ _ e hr hc⟩

/-- The printed square word decodes to the square instance. -/
theorem decode_square (I : EncodedCommunication.Instance) :
    EncodedCommunication.decodeInstance
        (EncodedCommunication.encodeInstance (squareInstance I)) = some (squareInstance I) :=
  EncodedCommunication.decode_encode _ (squareInstance_valid I)

/-- The square table of one tape of a selected output (total definition). -/
def squareTable (o : TotalFiniteConstructorScratch.SelectedOutput) (t : o.Tape) :
    Fin (SquarePadding.side o.rows o.cols) → Fin (SquarePadding.side o.rows o.cols) → Bool :=
  squareFun o.rows o.cols (o.table t).bits

/-- **Exact preservation** (`06-reduction.tex:84-85`, `146-147`): the square table has exactly the
communication complexity of the printed table. -/
theorem D_squareTable (o : TotalFiniteConstructorScratch.SelectedOutput)
    (hr : 0 < o.rows) (hc : 0 < o.cols) (t : o.Tape) :
    Workspace.Types.CommComplexity.D (squareTable o t) =
      Workspace.Types.CommComplexity.D (o.table t).matrix := by
  unfold squareTable
  rw [squareFun_eq_matrix hr hc, SquarePadding.D_matrix,
    EncodedSelectedOutput.tableGame_eq_matrix]

/-- Every original row and column is retained, at its original index. -/
theorem squareTable_original (o : TotalFiniteConstructorScratch.SelectedOutput)
    (hr : 0 < o.rows) (hc : 0 < o.cols) (t : o.Tape) (i : Fin o.rows) (j : Fin o.cols) :
    squareTable o t (Fin.castLE (SquarePadding.rows_le_side _ _) i)
        (Fin.castLE (SquarePadding.cols_le_side _ _) j) = (o.table t).matrix i j := by
  unfold squareTable
  rw [squareFun_eq_matrix hr hc, SquarePadding.matrix_original_entry,
    EncodedSelectedOutput.tableGame_eq_matrix]

/-- The square instance of a selected instance is literally the square table with the same
budget. -/
theorem squareInstance_selected {n m : ℕ} (hn : 0 < n) (edge : Fin m → Bool → Fin n) (Δ : ℕ)
    (γ : ℚ) (k : ℕ) (t : (TotalFiniteConstructorScratch.select hn edge Δ γ k).Tape) :
    squareInstance (EncodedSelectedOutput.selectedInstance hn edge Δ γ k t) =
      ⟨SquarePadding.side (TotalFiniteConstructorScratch.select hn edge Δ γ k).rows
          (TotalFiniteConstructorScratch.select hn edge Δ γ k).cols,
        SquarePadding.side (TotalFiniteConstructorScratch.select hn edge Δ γ k).rows
          (TotalFiniteConstructorScratch.select hn edge Δ γ k).cols,
        (TotalFiniteConstructorScratch.select hn edge Δ γ k).budget,
        MatrixMaterialization.rowMajor
          (squareTable (TotalFiniteConstructorScratch.select hn edge Δ γ k) t)⟩ := rfl

/-! ## The physical post stage: the explicit contract (segment 2, NOT proved here) -/

/-- **U17 post-stage contract (OPEN).** ONE fixed machine `P` that, on the encoded word of every
valid instance, prints exactly the encoded square instance within `CP·(|word|+1)^EP` steps. -/
def SquarePost (P : BitMachine.Machine) (CP EP : ℕ) : Prop :=
  ∀ I : EncodedCommunication.Instance, I.Valid →
    P.OutputsWithin (EncodedCommunication.encodeInstance I)
      (EncodedCommunication.encodeInstance (squareInstance I))
      (CP * ((EncodedCommunication.encodeInstance I).length + 1) ^ EP)

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
local notation "SQ" Φ:max k:max t:max => squareTable (SEL Φ k) t

set_option hygiene false in
local notation "SQE" Φ:max k:max t:max => squareTable (EXP Φ k).output t

/-! ## Segment 1: the literal target statements -/

/-- **T01, square option (lock `01-introduction.tex:80-96` last sentence, `06-reduction.tex:83-86`),
target statement.** Exactly `T01_endpoint`'s statement with the printed word replaced by the
encoded square power-of-two instance `SQOUT` (dimensions `side = 2^clog₂(max rows cols)`, same
budget, table `SQ`), and the YES/NO clauses about `D` of the square table. -/
def T01Square (TM : TapeModel) (L : EncodedComplexity.BinaryLanguage) (k : ℕ) : Prop :=
  ∃ (M : BitMachine.Machine) (C E : ℕ), ∀ Φ : ValidFormula,
    TM (EXP Φ k).output.Tape (EXP Φ k).tapeFintype (EXP Φ k).tapeLaw
      (EXP Φ k).output.tapeBits ∧
    (EXP Φ k).output = SEL Φ k ∧
    (SEL Φ k).inputBits ≤ C * ((EncodedCNF.encode Φ.val).length + 1) ^ E ∧
    (∀ t : (SEL Φ k).Tape,
      ((SEL Φ k).tapeBits t).length = (SEL Φ k).inputBits ∧
      (∃ T : ℕ, T ≤ C * ((EncodedCNF.encode Φ.val).length + 1) ^ E ∧
        M.OutputsWithin
          (EncodedComplexity.pair (EncodedCNF.encode Φ.val) ((SEL Φ k).tapeBits t))
          (SQOUT Φ k t) T) ∧
      (SQOUT Φ k t).length ≤ C * ((EncodedCNF.encode Φ.val).length + 1) ^ E ∧
      (EncodedCNF.encode Φ.val ∈ L →
        Workspace.Types.CommComplexity.D (SQ Φ k t) ≤ (SEL Φ k).budget)) ∧
    (EncodedCNF.encode Φ.val ∉ L →
      (981 / 1000 : ℝ) ≤ @FiniteLaw.prob _ (EXP Φ k).tapeFintype (EXP Φ k).tapeLaw
        (fun t => (EXP Φ k).output.budget + k ≤
          Workspace.Types.CommComplexity.D (SQE Φ k t)))

/-! ## Segment 3: the law level -/

theorem sel_pos (Φ : ValidFormula) (k : ℕ) : 0 < (SEL Φ k).rows ∧ 0 < (SEL Φ k).cols :=
  EncodedSelectedOutput.selected_dimensions_pos _ _ _ _ k

theorem exp_pos (Φ : ValidFormula) (k : ℕ) :
    0 < (EXP Φ k).output.rows ∧ 0 < (EXP Φ k).output.cols := by
  rw [TotalFiniteConstructorScratch.experiment_output_eq_select]
  exact sel_pos D B Φ k

/-- **Square law, T01 (segment 3).** For every valid `Φ` and `k ≥ 1`: the square table has
exactly the communication complexity of the printed table on every tape; YES: `D(square) ≤ B`
on every tape; NO: `Pr[D(square) ≥ B + k] ≥ 981/1000` under the actual experiment law. From the
admitted-by-name `t01_yes` / `t01_no` (frozen AEndpoint) and `SquarePadding.D_matrix`. No `hA3`. -/
theorem square_law_T01 (L : EncodedComplexity.BinaryLanguage) (hDA2 : DA2 L) (Φ : ValidFormula)
    (k : ℕ) (hk : 1 ≤ k) :
    (∀ t : (SEL Φ k).Tape, Workspace.Types.CommComplexity.D (SQ Φ k t) =
        Workspace.Types.CommComplexity.D ((SEL Φ k).table t).matrix) ∧
    (∀ t : (SEL Φ k).Tape, EncodedCNF.encode Φ.val ∈ L →
        Workspace.Types.CommComplexity.D (SQ Φ k t) ≤ (SEL Φ k).budget) ∧
    (EncodedCNF.encode Φ.val ∉ L →
      (981 / 1000 : ℝ) ≤ @FiniteLaw.prob _ (EXP Φ k).tapeFintype (EXP Φ k).tapeLaw
        (fun t => (EXP Φ k).output.budget + k ≤
          Workspace.Types.CommComplexity.D (SQE Φ k t))) := by
  have hs := sel_pos D B Φ k
  have he := exp_pos D B Φ k
  refine ⟨fun t => D_squareTable _ hs.1 hs.2 t, fun t hmem => ?_, fun hnot => ?_⟩
  · rw [D_squareTable _ hs.1 hs.2 t]
    exact t01_yes D B L hDA2 Φ k t hmem
  · refine le_trans (t01_no D B L hDA2 Φ k hk hnot) ?_
    exact @FiniteLaw.prob_mono _ (EXP Φ k).tapeFintype (EXP Φ k).tapeLaw _ _
      (fun t ht => by rw [D_squareTable _ he.1 he.2 t]; exact ht)

/-! ## Segment 2 (composition part): T01 square from the post-stage contract -/

/-- Polynomial arithmetic of the two-stage clock. -/
theorem square_poly (X C E T o CP EP pb s : ℕ)
    (hT : T ≤ C * (X + 1) ^ E) (ho : o ≤ C * (X + 1) ^ E)
    (hs : s ≤ o + CP * (o + 1) ^ EP * pb) :
    T + 2 * o + 2 + CP * (o + 1) ^ EP ≤
        (3 * C + 2 + CP * (C + 1) ^ EP * (1 + pb)) * (X + 1) ^ (E * (EP + 1)) ∧
      C * (X + 1) ^ E ≤
        (3 * C + 2 + CP * (C + 1) ^ EP * (1 + pb)) * (X + 1) ^ (E * (EP + 1)) ∧
      s ≤ (3 * C + 2 + CP * (C + 1) ^ EP * (1 + pb)) * (X + 1) ^ (E * (EP + 1)) := by
  set Y := (X + 1) ^ E with hY
  set Z := (X + 1) ^ (E * (EP + 1)) with hZ
  have hY1 : 1 ≤ Y := Nat.one_le_pow _ _ (Nat.succ_pos X)
  have hZY : Z = Y ^ (EP + 1) := by rw [hZ, hY, ← pow_mul]
  have hYZ : Y ≤ Z := by
    rw [hZY]
    calc Y = Y ^ 1 := (pow_one _).symm
      _ ≤ Y ^ (EP + 1) := Nat.pow_le_pow_right hY1 (by omega)
  have hYEZ : Y ^ EP ≤ Z := by
    rw [hZY]; exact Nat.pow_le_pow_right hY1 (by omega)
  have hZ1 : 1 ≤ Z := le_trans hY1 hYZ
  have ho1 : o + 1 ≤ (C + 1) * Y := by
    have : (C + 1) * Y = C * Y + Y := by ring
    rw [this]; omega
  have hpow : (o + 1) ^ EP ≤ (C + 1) ^ EP * Z := by
    calc (o + 1) ^ EP ≤ ((C + 1) * Y) ^ EP := Nat.pow_le_pow_left ho1 _
      _ = (C + 1) ^ EP * Y ^ EP := mul_pow _ _ _
      _ ≤ (C + 1) ^ EP * Z := Nat.mul_le_mul_left _ hYEZ
  have hK : CP * (o + 1) ^ EP ≤ CP * (C + 1) ^ EP * Z := by
    rw [mul_assoc]; exact Nat.mul_le_mul_left _ hpow
  have hCY : C * Y ≤ C * Z := Nat.mul_le_mul_left _ hYZ
  have hKpb : CP * (o + 1) ^ EP * pb ≤ CP * (C + 1) ^ EP * pb * Z := by
    calc CP * (o + 1) ^ EP * pb ≤ CP * (C + 1) ^ EP * Z * pb := Nat.mul_le_mul_right _ hK
      _ = CP * (C + 1) ^ EP * pb * Z := by ring
  have hexp : (3 * C + 2 + CP * (C + 1) ^ EP * (1 + pb)) * Z =
      3 * (C * Z) + 2 * Z + CP * (C + 1) ^ EP * Z + CP * (C + 1) ^ EP * pb * Z := by ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hexp]; omega
  · rw [hexp]; omega
  · rw [hexp]; omega

/-- **T01, square option, from the post-stage contract.** Modulo `hA3`, D-A1 (`hDA1`), D-A2
(`hDA2`), D-A7 (`D`, `B`) and the OPEN physical post stage `SquarePost P CP EP`, the composed
machine `composition M P` (`M` the T01 machine of `T01_endpoint`) witnesses `T01Square`. -/
theorem T01_square (TM : TapeModel) (hDA1 : DA1 D B TM)
    (L : EncodedComplexity.BinaryLanguage) (hDA2 : DA2 L)
    (hA3 : Unit4Shell.Shells.H_A3 B.degreeBound (sourceGap D B)) (k : ℕ) (hk : 1 ≤ k)
    (P : BitMachine.Machine) (CP EP : ℕ) (hP : SquarePost P CP EP) :
    T01Square D B TM L k := by
  obtain ⟨M, C, E, hM⟩ := T01_endpoint D B TM hDA1 L hDA2 hA3 k hk
  refine ⟨BitMachineComposition.composition M P,
    3 * C + 2 + CP * (C + 1) ^ EP * (1 + P.pushBound), E * (EP + 1), fun Φ => ?_⟩
  obtain ⟨h1, h2, h3, h4, -⟩ := hM Φ
  have hlaw := square_law_T01 D B L hDA2 Φ k hk
  have hs := sel_pos D B Φ k
  refine ⟨h1, h2, ?_, fun t => ?_, hlaw.2.2⟩
  · refine le_trans h3 ?_
    obtain ⟨-, h, -⟩ := square_poly (EncodedCNF.encode Φ.val).length C E 0 0 CP EP P.pushBound 0
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    exact h
  · obtain ⟨hlen, ⟨T, hT, hrun⟩, hout, -⟩ := h4 t
    have hvalid := EncodedSelectedOutput.instanceOf_valid ((SEL Φ k).table t) (SEL Φ k).budget
      hs.1 hs.2
    have hPrun := hP _ hvalid
    change P.OutputsWithin (OUT Φ k t) (SQOUT Φ k t) (CP * ((OUT Φ k t).length + 1) ^ EP) at hPrun
    have hC := BitMachineComposition.composition_outputsWithin M P hrun hPrun
    have hsq := BitMachine.output_length_bound P hPrun
    obtain ⟨hA, -, hB⟩ := square_poly (EncodedCNF.encode Φ.val).length C E T (OUT Φ k t).length
      CP EP P.pushBound (SQOUT Φ k t).length hT hout hsq
    exact ⟨hlen, ⟨_, hA, hC⟩, hB, hlaw.2.1 t⟩

#print axioms squareFun_eq_matrix
#print axioms squareInstance_valid
#print axioms squareInstance_side
#print axioms decode_square
#print axioms D_squareTable
#print axioms squareTable_original
#print axioms squareInstance_selected
#print axioms square_law_T01
#print axioms square_poly
#print axioms T01_square

end Paper2.ASquare
