import Paper2.E6Dec
import Paper2.ASquarePost

/-!
# Paper A (lock v12), lane `owner:a-eth-7`, segment 6a: the square-padding header stage

Lock v12 `sections/06-reduction.tex:115-116` (`thm:quantitative`): "The conclusion also holds when the inputs
are square matrices of power-of-two side length." Proof, `:143-148`: "To obtain a square power-of-two table,
let $S$ be the least power of two at least $m_Y$, and repeat rows and columns until both dimensions are $S$.
Every original row and column is retained, so these repetitions preserve communication complexity exactly."

The square header tail `hdTailSq` is the frozen a-eth-owner-5/6 header tail `Paper2.AEth5.hdTail`
(`Pack ; PairMap (MF ; GS) ; Swap ; PairConcat ; KHeader`) with ONE extra stage: after `MF ; GS` prints the
encoded selected instance `i`, the admitted fixed machine `Paper2.ASquare.Post.squareMachine` prints the encoded
square instance `Paper2.ASquare.squareInstance i` (admitted `Paper2.ASquare.Post.squarePost`: within
`squareCP · (|encodeInstance i| + 1)^squareEP`; side `SquarePadding.side rows cols`, cyclic repetition, the SAME
threshold). `KHeader` (a-eth-owner-4 `Paper2.AEth4.KHeader`, module `Paper2.E4Head`, registered in `lean/Paper2.lean`) is generic in the
instance and prints `headeredWord (kOf N) (squareInstance i)`. Every handoff is charged by
`BitMachineComposition.composition_outputsWithin`; nothing is inserted.

* `tail_outputs_sq`: the square tail on the reduction block, with the explicit clock `tailTimeSq`.
* `hw_length_eq_sq`: the square header word has the tape-independent length `hwLenSq`.
* `hw_length_le_sq`, `hw_fit_sq`, `classifier_fit_sq`: the size facts of a-eth-owner-4 `E4Size` for the square
  word (`|hwSq| + 1 ≤ (n+2)^(332(k+1))`), hence every fixed power fits in `expLen N`.

No ledger row is closed. Nothing here is admitted.
-/

noncomputable section

namespace Paper2.AEth7

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics
open Paper2.AEth4 Paper2.AEth5
open Paper2.AEth3 (MF CF EF GS cut0 inputBits_fit cutLen cutLen_eq cutLen_ge fOut)

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

/-- The side of the square table of the selected output. -/
def sideOf (Φ : ValidFormula) : ℕ := SquarePadding.side (Sel D B Φ).rows (Sel D B Φ).cols

/-- The (tape-independent) length of the encoded square instance. -/
def sobLen (Φ : ValidFormula) : ℕ :=
  2 * ((sideOf D B Φ).bits.length + (sideOf D B Φ).bits.length + (Sel D B Φ).budget.bits.length) + 3 +
    sideOf D B Φ * sideOf D B Φ

/-- The square instance of the selected instance at reduction tape `t'`. -/
def sqInst (Φ : ValidFormula) (t' : (Sel D B Φ).Tape) : EncodedCommunication.Instance :=
  Paper2.ASquare.squareInstance (EncodedSelectedOutput.selectedInstance (t10_vertices_pos D B Φ)
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
    B.degreeBound (sourceGap D B) (kOf Φ.val.variables) t')

theorem sob_length (Φ : ValidFormula) (t' : (Sel D B Φ).Tape) :
    (EncodedCommunication.encodeInstance (sqInst D B Φ t')).length = sobLen D B Φ := by
  rw [EncodedCommunication.encodeInstance_length]
  simp only [sqInst, Paper2.ASquare.squareInstance, MatrixMaterialization.rowMajor_length]
  rfl

/-- The square header clock (tape-independent). -/
def khTimeSq (Φ : ValidFormula) : ℕ :=
  (2 * (EncodedCNF.encode Φ.val).length +
      Paper2.Unit4Shell.KofFront.BK * (Φ.val.variables + 1) ^ 2 + 2 * kOf Φ.val.variables + 6) +
    2 * (2 * kOf Φ.val.variables + 1 + sobLen D B Φ) + 2 +
    GrowHeader.clock (kOf Φ.val.variables) (sideOf D B Φ) (sideOf D B Φ) (Sel D B Φ).budget

theorem khTimeSq_eq (Φ : ValidFormula) (t' : (Sel D B Φ).Tape) :
    KHeader.clock Φ.val (sqInst D B Φ t') = khTimeSq D B Φ := by
  have hl := sob_length D B Φ t'
  unfold KHeader.clock khTimeSq
  simp only [EncodedComplexity.pair_length, List.length_replicate, hl]
  rfl

/-- The fixed reduction core followed by the admitted square post machine. -/
def MGS : BitMachine.Machine :=
  BitMachineComposition.composition (BitMachineComposition.composition (MF D B) (GS D B))
    Paper2.ASquare.Post.squareMachine

/-- **THE square header tail** (one fixed machine). -/
def hdTailSq : BitMachine.Machine :=
  BitMachineComposition.composition Pack.machine
    (BitMachineComposition.composition
      (Paper2.Unit4Shell.PairMap.machine (MGS D B))
      (BitMachineComposition.composition Paper2.Unit4Shell.KofLoops.Swap.machine
        (BitMachineComposition.composition PairConcat.machine KHeader.machine)))

/-- The square tail clock (tape-independent; the square post clock is the admitted `squareCP (ob+1)^squareEP`). -/
def tailTimeSq (Φ : ValidFormula) : ℕ :=
  let eL := (EncodedCNF.encode Φ.val).length
  let XL := 2 * eL + 1 + cutLen Φ.val
  let ob := obLen D B Φ
  let sb := sobLen D B Φ
  8 * (XL + 2) + 2 * (2 * XL + 4 * eL + 4) + 2 +
    ((2 * XL + (mgTime D B Φ + 2 * ob + 2 +
        Paper2.ASquare.Post.squareCP * (ob + 1) ^ Paper2.ASquare.Post.squareEP) + 2 * sb + 6) +
      2 * (2 * sb + 4 * eL + 4) + 2 +
      (3 * (2 * sb + 4 * eL + 5) + 2 * (2 * sb + 4 * eL + 4) + 2 +
        (3 * (2 * sb + 4 * eL + 5) + 2 * (2 * eL + 1 + sb) + 2 + khTimeSq D B Φ)))

/-- The printed SQUARE header word at the growing gap. -/
def hwOfSq (Φ : ValidFormula) (t' : (Sel D B Φ).Tape) : List Bool :=
  Paper2.HeaderWordRun.headeredWord (kOf Φ.val.variables) (sqInst D B Φ t')

set_option maxHeartbeats 1600000 in
/-- **The square header tail on the reduction block.** -/
theorem tail_outputs_sq (Φ : ValidFormula) (hk : 1 ≤ kOf Φ.val.variables)
    (hN : cut0 D B ≤ Φ.val.variables) (c : List Bool) (hcl : c.length ≤ cutLen Φ.val)
    (hIc : (Sel D B Φ).inputBits ≤ c.length) :
    ∃ t' : (Sel D B Φ).Tape, (Sel D B Φ).tapeBits t' = c.take (Sel D B Φ).inputBits ∧
      (hdTailSq D B).OutputsWithin (EncodedComplexity.pair (EncodedCNF.encode Φ.val) c)
        (hwOfSq D B Φ t') (tailTimeSq D B Φ) := by
  obtain ⟨t', ht', hmg⟩ := mg_outputs D B Φ hk hN c hcl hIc
  refine ⟨t', ht', ?_⟩
  set e := EncodedCNF.encode Φ.val with he
  set ob := EncodedSelectedOutput.outputBits (t10_vertices_pos D B Φ)
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
    B.degreeBound (sourceGap D B) (kOf Φ.val.variables) t' with hob
  set i := EncodedSelectedOutput.selectedInstance (t10_vertices_pos D B Φ)
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
    B.degreeBound (sourceGap D B) (kOf Φ.val.variables) t' with hi
  have hobi : ob = EncodedCommunication.encodeInstance i := rfl
  have hpos := EncodedSelectedOutput.selected_dimensions_pos (t10_vertices_pos D B Φ)
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
    B.degreeBound (sourceGap D B) (kOf Φ.val.variables)
  have hval : i.Valid := EncodedSelectedOutput.instanceOf_valid _ _ hpos.1 hpos.2
  have hsq := Paper2.ASquare.Post.squarePost i hval
  rw [← hobi] at hsq
  set so := EncodedCommunication.encodeInstance (sqInst D B Φ t') with hso
  have hsq' : Paper2.ASquare.Post.squareMachine.OutputsWithin ob so
      (Paper2.ASquare.Post.squareCP * (ob.length + 1) ^ Paper2.ASquare.Post.squareEP) := hsq
  have hmgs := BitMachineComposition.composition_outputsWithin _ _ hmg hsq'
  have h2 := Pack.outputs e c
  have h3 := Paper2.Unit4Shell.PairMap.machine_outputs (M := MGS D B) (EncodedComplexity.pair e c) so
    (EncodedComplexity.pair (EncodedCommunication.field e) []) _ hmgs
  have h4 := Paper2.Unit4Shell.KofLoops.Swap.machine_outputs so (EncodedCommunication.field e) []
  have h5 := PairConcat.outputs
    (EncodedComplexity.pair (EncodedCommunication.field e) (EncodedComplexity.pair so []))
  rw [PairConcat.concat_pair] at h5
  have h6 := KHeader.machine_outputs Φ.val hk (sqInst D B Φ t')
  rw [khTimeSq_eq D B Φ t'] at h6
  have hfe : EncodedCommunication.field e ++ so = EncodedComplexity.pair e so := rfl
  rw [hfe] at h5
  have hC := BitMachineComposition.composition_outputsWithin _ _ h2
    (BitMachineComposition.composition_outputsWithin _ _ h3
      (BitMachineComposition.composition_outputsWithin _ _ h4
        (BitMachineComposition.composition_outputsWithin _ _ h5 h6)))
  refine BitMachine.outputsWithin_mono _ hC ?_
  have hobl : ob.length = obLen D B Φ := outputBits_length D B Φ t'
  have hsol : so.length = sobLen D B Φ := sob_length D B Φ t'
  simp only [tailTimeSq, EncodedComplexity.pair_length, EncodedCommunication.field_length,
    List.length_nil, hobl, hsol]
  rw [← he]
  omega

/-- The tape-independent length of the printed square header word. -/
def hwLenSq (Φ : ValidFormula) : ℕ :=
  (EncodedCommunication.natField (2 * (Sel D B Φ).budget + kOf Φ.val.variables)).length +
    ((EncodedCommunication.natField (sideOf D B Φ)).length +
      (EncodedCommunication.natField (sideOf D B Φ)).length + sideOf D B Φ * sideOf D B Φ)

theorem hw_length_eq_sq (Φ : ValidFormula) (t' : (Sel D B Φ).Tape) :
    (hwOfSq D B Φ t').length = hwLenSq D B Φ := by
  unfold hwOfSq hwLenSq sqInst
  simp only [Paper2.HeaderWordRun.headeredWord, Paper2.HeaderWordRun.matrix,
    Paper2.ASquare.squareInstance, EncodedSelectedOutput.selectedInstance,
    EncodedSelectedOutput.instanceOf, AFront.Projection.matrixWord, List.length_append,
    MatrixMaterialization.rowMajor_length]
  rfl

theorem natField_length_le (m : ℕ) : (EncodedCommunication.natField m).length ≤ 2 * m + 1 := by
  simp only [EncodedCommunication.natField, EncodedCommunication.field_length]
  have := UnaryBinaryEncoding.bits_length_le m
  omega

theorem hw_length_le_sq (Φ : ValidFormula) (hk : 1 ≤ kOf Φ.val.variables) (t' : (Sel D B Φ).Tape) :
    (hwOfSq D B Φ t').length + 1 ≤
      ((t10Graph D B Φ).vertices + 2) ^ (332 * (kOf Φ.val.variables + 1)) := by
  have hob := EncodedOutputSize.outputBits_length_le_poly (t10_vertices_pos D B Φ)
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
    B.degreeBound (sourceGap D B) (kOf Φ.val.variables) hk t'
  rw [outputBits_length D B Φ t'] at hob
  have hbud := EncodedOutputSize.selected_budget_le_resource (t10_vertices_pos D B Φ)
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
    B.degreeBound (sourceGap D B) (kOf Φ.val.variables)
  have hR : TotalFiniteResourcesScratch.resourceBound (t10Graph D B Φ).vertices (kOf Φ.val.variables) ≤
      ((t10Graph D B Φ).vertices + 2) ^ (164 * (kOf Φ.val.variables + 1)) := by
    unfold TotalFiniteResourcesScratch.resourceBound
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hkP : kOf Φ.val.variables ≤ ((t10Graph D B Φ).vertices + 2) ^ (164 * (kOf Φ.val.variables + 1)) := by
    have h1 : kOf Φ.val.variables < 2 ^ kOf Φ.val.variables := Nat.lt_two_pow_self
    have h2 : 2 ^ kOf Φ.val.variables ≤ ((t10Graph D B Φ).vertices + 2) ^ kOf Φ.val.variables :=
      Nat.pow_le_pow_left (by omega) _
    have h3 : ((t10Graph D B Φ).vertices + 2) ^ kOf Φ.val.variables ≤
        ((t10Graph D B Φ).vertices + 2) ^ (164 * (kOf Φ.val.variables + 1)) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hP2 : 2 ≤ ((t10Graph D B Φ).vertices + 2) ^ (164 * (kOf Φ.val.variables + 1)) := by
    have : ((t10Graph D B Φ).vertices + 2) ^ 1 ≤
        ((t10Graph D B Φ).vertices + 2) ^ (164 * (kOf Φ.val.variables + 1)) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    simp only [pow_one] at this
    omega
  have hthr : (Sel D B Φ).budget ≤
      ((t10Graph D B Φ).vertices + 2) ^ (164 * (kOf Φ.val.variables + 1)) := le_trans hbud hR
  have hpos := EncodedSelectedOutput.selected_dimensions_pos (t10_vertices_pos D B Φ)
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
    B.degreeBound (sourceGap D B) (kOf Φ.val.variables)
  have hr0 : 0 < (Sel D B Φ).rows := hpos.1
  have hc0 : 0 < (Sel D B Φ).cols := hpos.2
  have hrc : (Sel D B Φ).rows * (Sel D B Φ).cols ≤ obLen D B Φ := by unfold obLen; omega
  have hrr : (Sel D B Φ).rows ≤ (Sel D B Φ).rows * (Sel D B Φ).cols := Nat.le_mul_of_pos_right _ hc0
  have hcc : (Sel D B Φ).cols ≤ (Sel D B Φ).rows * (Sel D B Φ).cols := Nat.le_mul_of_pos_left _ hr0
  have hS : sideOf D B Φ ≤ 2 * ((Sel D B Φ).rows + (Sel D B Φ).cols) :=
    Paper2.Unit4Shell.SquareWriter.side_le_two_sum hr0
  have h1 := natField_length_le (2 * (Sel D B Φ).budget + kOf Φ.val.variables)
  have h2 := natField_length_le (sideOf D B Φ)
  have hlen := hw_length_eq_sq D B Φ t'
  unfold hwLenSq at hlen
  have h81 : 81 ≤ ((t10Graph D B Φ).vertices + 2) ^ (4 * (kOf Φ.val.variables + 1)) := by
    have : (3 : ℕ) ^ 4 ≤ ((t10Graph D B Φ).vertices + 2) ^ 4 :=
      Nat.pow_le_pow_left (by have := t10_vertices_pos D B Φ; omega) 4
    have h' : ((t10Graph D B Φ).vertices + 2) ^ 4 ≤
        ((t10Graph D B Φ).vertices + 2) ^ (4 * (kOf Φ.val.variables + 1)) :=
      Nat.pow_le_pow_right (by omega) (by nlinarith)
    norm_num at this
    omega
  have hsplit : ((t10Graph D B Φ).vertices + 2) ^ (332 * (kOf Φ.val.variables + 1)) =
      ((t10Graph D B Φ).vertices + 2) ^ (4 * (kOf Φ.val.variables + 1)) *
        (((t10Graph D B Φ).vertices + 2) ^ (164 * (kOf Φ.val.variables + 1)) *
          ((t10Graph D B Φ).vertices + 2) ^ (164 * (kOf Φ.val.variables + 1))) := by
    rw [← pow_add, ← pow_add, show 4 * (kOf Φ.val.variables + 1) + (164 * (kOf Φ.val.variables + 1) +
      164 * (kOf Φ.val.variables + 1)) = 332 * (kOf Φ.val.variables + 1) by ring]
  rw [hsplit]
  generalize ((t10Graph D B Φ).vertices + 2) ^ (164 * (kOf Φ.val.variables + 1)) = P at *
  generalize ((t10Graph D B Φ).vertices + 2) ^ (4 * (kOf Φ.val.variables + 1)) = Q at *
  generalize sideOf D B Φ = S at *
  have hSP : S ≤ 4 * P := by omega
  have hSS : S * S ≤ 16 * (P * P) := by
    have := Nat.mul_le_mul hSP hSP
    nlinarith
  have hPP : 2 * P ≤ P * P := Nat.mul_le_mul_right P hP2
  have hbase : (hwOfSq D B Φ t').length + 1 ≤ 81 * (P * P) := by omega
  exact hbase.trans (Nat.mul_le_mul_right _ h81)

/-- **Every fixed power of the printed square header length fits in `expLen N`.** -/
theorem hw_fit_sq (cs K : ℕ) :
    ∃ N₀ : ℕ, ∀ Φ : ValidFormula, Φ.val.clauses.length ≤ cs * Φ.val.variables →
      N₀ ≤ Φ.val.variables → 1 ≤ kOf Φ.val.variables ∧
      ∀ t' : (Sel D B Φ).Tape, ((hwOfSq D B Φ t').length + 1) ^ K ≤
        Paper2.AEth.expLen Φ.val.variables := by
  obtain ⟨N₁, hN₁⟩ := Paper2.AEth3.bits_fit (332 * K) (D.sizeExponent + 2)
  refine ⟨max N₁ (max 36
    (2 ^ (2 ^ (D.sizeExponent + 1) * Paper2.Unit4Shell.T10Size.t45C D B cs))), ?_⟩
  intro Φ hsp hN
  have h1 : N₁ ≤ Φ.val.variables := le_trans (le_max_left _ _) hN
  have h2 : 36 ≤ Φ.val.variables := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have h4 : 2 ^ (2 ^ (D.sizeExponent + 1) * Paper2.Unit4Shell.T10Size.t45C D B cs) ≤
      Φ.val.variables := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hk1 : 1 ≤ kOf Φ.val.variables := Paper2.Unit4Shell.AsymptoticsExplicit.kOf_pos _ h2
  refine ⟨hk1, fun t' => ?_⟩
  have hsize := Paper2.Unit4Shell.T10Size.t45_shell_form D B cs Φ hsp h4
  have hfit := hN₁ Φ.val.variables h1 _ hsize
  set n := (t10Graph D B Φ).vertices
  set k := kOf Φ.val.variables
  have hbase := hw_length_le_sq D B Φ hk1 t'
  calc ((hwOfSq D B Φ t').length + 1) ^ K ≤ ((n + 2) ^ (332 * (k + 1))) ^ K :=
        Nat.pow_le_pow_left hbase K
    _ = (n + 2) ^ (332 * K * (k + 1)) := by
        rw [← pow_mul, show 332 * (k + 1) * K = 332 * K * (k + 1) by ring]
    _ ≤ Paper2.AEth.expLen Φ.val.variables := hfit

/-- **The classifier fits on the square word.** -/
theorem classifier_fit_sq (cs : ℕ) (C : Paper2.SelectedTape.Algorithm) :
    ∃ N₀ : ℕ, ∀ Φ : ValidFormula, Φ.val.clauses.length ≤ cs * Φ.val.variables →
      N₀ ≤ Φ.val.variables → ∀ t' : (Sel D B Φ).Tape,
        C.tapeLength (hwOfSq D B Φ t') ≤ C.cR * Paper2.AEth.expLen Φ.val.variables ∧
        C.cT * ((hwOfSq D B Φ t').length + 1) ^ C.dT ≤ C.cT * Paper2.AEth.expLen Φ.val.variables := by
  obtain ⟨N₁, hN₁⟩ := hw_fit_sq D B cs C.dR
  obtain ⟨N₂, hN₂⟩ := hw_fit_sq D B cs C.dT
  refine ⟨max N₁ N₂, fun Φ hsp hN t' => ?_⟩
  have hR := (hN₁ Φ hsp (le_trans (le_max_left _ _) hN)).2 t'
  have hT := (hN₂ Φ hsp (le_trans (le_max_right _ _) hN)).2 t'
  exact ⟨Nat.mul_le_mul_left _ hR, Nat.mul_le_mul_left _ hT⟩

end Paper2.AEth7

end

#print axioms Paper2.AEth7.sob_length
#print axioms Paper2.AEth7.khTimeSq_eq
#print axioms Paper2.AEth7.tail_outputs_sq
#print axioms Paper2.AEth7.hw_length_eq_sq
#print axioms Paper2.AEth7.hw_length_le_sq
#print axioms Paper2.AEth7.hw_fit_sq
#print axioms Paper2.AEth7.classifier_fit_sq
