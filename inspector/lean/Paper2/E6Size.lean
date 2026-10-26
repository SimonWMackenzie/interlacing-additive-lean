import Paper2.E6Hd
import Paper2.EncodedOutputSize
import Paper2.HeaderClassifierSelected
-- a-eth-owner-6 copy of frozen a-eth-owner-5/E5Size.lean (SHA-256 4c159b5658526957903abefd0bf9941fa6e1ee7633bc25f090c1ebfc9e22d242); import lines renamed only.

/-! a-eth-owner-5 copy of frozen `a-eth-owner-4/E4Size.lean` (SHA-256 3fb3f0f68a14f23f1b9e37a33f8f64bf1de1ed5b22f4cbaa59d319db7bfcd0ac). Changes: import lines renamed E4Budget/E4Red/E4Hd/E4Size -> E5Budget/E5Red/E5Hd/E5Size; nothing else. -/

/-!
# Paper A (lock v12), lane `owner:a-eth-4`, segment 4 (partial, 4b ingredient): the header word and the classifier fit

For sparse valid `Φ` with `N` large, every header word printed at `k = kOf N` (segment 4d) satisfies
`(|hw| + 1)^K ≤ expLen N` for every fixed `K` (admitted `EncodedOutputSize.outputBits_length_le_poly`,
`selected_budget_le_resource`, admitted `T10Size.t45_shell_form`, a-eth-owner-3 `bits_fit`). Hence for every
selected-carrier algorithm `C` (in particular `HeaderStrip.selectedClassifier E`), its tape on the header word has
at most `C.cR · expLen N` bits and its clock is at most `C.cT · expLen N`: the classifier block and the classifier
run fit the D-A6 budget. No ledger row is closed. Nothing here is admitted.
-/

noncomputable section

namespace Paper2.AEth4

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

/-- The printed header word at the growing gap. -/
def hwOf (Φ : ValidFormula) (t' : (Sel D B Φ).Tape) : List Bool :=
  Paper2.HeaderWordRun.headeredWord (kOf Φ.val.variables)
    (EncodedSelectedOutput.selectedInstance (t10_vertices_pos D B Φ)
      (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
      B.degreeBound (sourceGap D B) (kOf Φ.val.variables) t')

theorem hw_length_le (Φ : ValidFormula) (hk : 1 ≤ kOf Φ.val.variables) (t' : (Sel D B Φ).Tape) :
    (hwOf D B Φ t').length + 1 ≤
      8 * ((t10Graph D B Φ).vertices + 2) ^ (164 * (kOf Φ.val.variables + 1)) := by
  set k := kOf Φ.val.variables
  set P := ((t10Graph D B Φ).vertices + 2) ^ (164 * (k + 1)) with hP
  have hob := EncodedOutputSize.outputBits_length_le_poly (t10_vertices_pos D B Φ)
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
    B.degreeBound (sourceGap D B) k hk t'
  have hbud := EncodedOutputSize.selected_budget_le_resource (t10_vertices_pos D B Φ)
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
    B.degreeBound (sourceGap D B) k
  have hR : TotalFiniteResourcesScratch.resourceBound (t10Graph D B Φ).vertices k ≤ P := by
    unfold TotalFiniteResourcesScratch.resourceBound
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hkP : k ≤ P := by
    have h1 : k < 2 ^ k := Nat.lt_two_pow_self
    have h2 : 2 ^ k ≤ ((t10Graph D B Φ).vertices + 2) ^ k := Nat.pow_le_pow_left (by omega) k
    have h3 : ((t10Graph D B Φ).vertices + 2) ^ k ≤ P := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  simp only [EncodedSelectedOutput.outputBits] at hob
  set i := EncodedSelectedOutput.selectedInstance (t10_vertices_pos D B Φ)
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
    B.degreeBound (sourceGap D B) k t' with hi
  have hhw : (hwOf D B Φ t').length =
      (EncodedCommunication.natField (2 * i.threshold + k)).length +
        (AFront.Projection.matrixWord i.rows i.cols i.table).length := by
    show (EncodedCommunication.natField (2 * i.threshold + k) ++
      AFront.Projection.matrixWord i.rows i.cols i.table).length = _
    rw [List.length_append]
  have hmat : (AFront.Projection.matrixWord i.rows i.cols i.table).length ≤
      (EncodedCommunication.encodeInstance i).length := by
    simp only [AFront.Projection.matrixWord, EncodedCommunication.encodeInstance,
      List.length_append]
    omega
  have hnf : (EncodedCommunication.natField (2 * i.threshold + k)).length ≤
      2 * (2 * i.threshold + k) + 1 := by
    simp only [EncodedCommunication.natField, EncodedCommunication.field_length]
    have := UnaryBinaryEncoding.bits_length_le (2 * i.threshold + k)
    omega
  have hthr : i.threshold ≤ TotalFiniteResourcesScratch.resourceBound (t10Graph D B Φ).vertices k := by
    simp only [hi, EncodedSelectedOutput.selectedInstance, EncodedSelectedOutput.instanceOf]
    exact hbud
  have hP2 : 2 ≤ P := by
    have : ((t10Graph D B Φ).vertices + 2) ^ 1 ≤ P := Nat.pow_le_pow_right (by omega) (by omega)
    simp at this
    omega
  omega

/-- **Every fixed power of the printed header length fits in `expLen N`.** -/
theorem hw_fit (cs K : ℕ) :
    ∃ N₀ : ℕ, ∀ Φ : ValidFormula, Φ.val.clauses.length ≤ cs * Φ.val.variables →
      N₀ ≤ Φ.val.variables → 1 ≤ kOf Φ.val.variables ∧
      ∀ t' : (Sel D B Φ).Tape, ((hwOf D B Φ t').length + 1) ^ K ≤
        Paper2.AEth.expLen Φ.val.variables := by
  obtain ⟨N₁, hN₁⟩ := Paper2.AEth3.bits_fit (167 * K) (D.sizeExponent + 2)
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
  have hl := hw_length_le D B Φ hk1 t'
  have h8 : 8 ≤ (n + 2) ^ (3 * (k + 1)) := by
    have : (2 : ℕ) ^ 3 ≤ (n + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have h' : (n + 2) ^ 3 ≤ (n + 2) ^ (3 * (k + 1)) := Nat.pow_le_pow_right (by omega) (by nlinarith)
    norm_num at this
    omega
  have hbase : (hwOf D B Φ t').length + 1 ≤ (n + 2) ^ (167 * (k + 1)) := by
    calc (hwOf D B Φ t').length + 1 ≤ 8 * (n + 2) ^ (164 * (k + 1)) := hl
      _ ≤ (n + 2) ^ (3 * (k + 1)) * (n + 2) ^ (164 * (k + 1)) := Nat.mul_le_mul_right _ h8
      _ = (n + 2) ^ (167 * (k + 1)) := by
        rw [← pow_add, show 3 * (k + 1) + 164 * (k + 1) = 167 * (k + 1) by ring]
  calc ((hwOf D B Φ t').length + 1) ^ K ≤ ((n + 2) ^ (167 * (k + 1))) ^ K :=
        Nat.pow_le_pow_left hbase K
    _ = (n + 2) ^ (167 * K * (k + 1)) := by
        rw [← pow_mul, show 167 * (k + 1) * K = 167 * K * (k + 1) by ring]
    _ ≤ Paper2.AEth.expLen Φ.val.variables := hfit

/-- **The classifier fits.** For every selected-carrier algorithm `C` and density `cs`, eventually its
tape on every printed header word has at most `C.cR · expLen N` bits and its clock is at most
`C.cT · expLen N`. -/
theorem classifier_fit (cs : ℕ) (C : Paper2.SelectedTape.Algorithm) :
    ∃ N₀ : ℕ, ∀ Φ : ValidFormula, Φ.val.clauses.length ≤ cs * Φ.val.variables →
      N₀ ≤ Φ.val.variables → ∀ t' : (Sel D B Φ).Tape,
        C.tapeLength (hwOf D B Φ t') ≤ C.cR * Paper2.AEth.expLen Φ.val.variables ∧
        C.cT * ((hwOf D B Φ t').length + 1) ^ C.dT ≤ C.cT * Paper2.AEth.expLen Φ.val.variables := by
  obtain ⟨N₁, hN₁⟩ := hw_fit D B cs C.dR
  obtain ⟨N₂, hN₂⟩ := hw_fit D B cs C.dT
  refine ⟨max N₁ N₂, fun Φ hsp hN t' => ?_⟩
  have hR := (hN₁ Φ hsp (le_trans (le_max_left _ _) hN)).2 t'
  have hT := (hN₂ Φ hsp (le_trans (le_max_right _ _) hN)).2 t'
  exact ⟨Nat.mul_le_mul_left _ hR, Nat.mul_le_mul_left _ hT⟩

end Paper2.AEth4

end

#print axioms Paper2.AEth4.hw_length_le
#print axioms Paper2.AEth4.hw_fit
#print axioms Paper2.AEth4.classifier_fit
