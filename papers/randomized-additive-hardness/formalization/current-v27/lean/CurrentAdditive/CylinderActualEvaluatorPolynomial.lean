import CurrentAdditive.CylinderActualMatrixEvaluator
import CurrentAdditive.CylinderEvalMapPolynomial
import CurrentAdditive.CylinderEvalOutputBounds
import CurrentAdditive.CylinderEvalPolynomialArithmetic

set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

/-! The physical tester, conjunction, routing and two ordered map loops
have one polynomial clock in the original prepared packet. The constants
are selected before q, alphabets, source arrays and feature descriptors. -/

namespace CurrentAdditive.CylinderActualEvaluatorPolynomial

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineBankCodec
open CurrentAdditive.CylinderFeatureCodec CurrentAdditive.CylinderEvalTypedBytes
open CurrentAdditive.CylinderEvalByteBounds CurrentAdditive.CylinderEvalOutputBounds
open CurrentAdditive.CylinderEvalPolynomialArithmetic CurrentAdditive.FeatureMapPairLoader

theorem feature_polynomial : ∃ C d : ℕ,1≤d ∧
    ∀ {q : ℕ} (v : Fin q → ℕ) (feature : List (ℕ × ℕ))
      (valid : ∀p∈feature,p.1<q),
      CylinderActualFeatureEvaluator.clock v feature ≤
        C*((CylinderActualFeatureEvaluator.input v feature).length+1)^d := by
  obtain ⟨K,E,hK⟩ := CylinderEvalMapPolynomial.uniform_from_callback
    CylinderEvalPairMachine.machine false 128 3
  refine ⟨K+4,max 1 E,by omega,?_⟩
  intro q v feature valid
  have hm := hK (CylinderEvalPairMachine.context v)
    (CylinderActualFeatureEvaluator.pairItems feature)
    (CylinderActualFeatureEvaluator.pairResult v) (CylinderActualFeatureEvaluator.pairClock v)
    (CylinderActualFeatureEvaluator.pair_runs v feature valid) (by intro w _;rfl)
  rw [CylinderActualFeatureEvaluator.raw_input] at hm
  have hlen : (CylinderGeneralFeatureSemanticBare.comparisonBits v feature).length≤
      (CylinderActualFeatureEvaluator.input v feature).length := by
    have hc := feature_count_le feature
    have hf := word_length_le_encode
      (![CylinderEvalPairMachine.context v,encodeFeature feature]) (1 : Fin 2)
    simpa only [CylinderGeneralFeatureSemanticBare.comparisonBits,List.length_map] using hc.trans hf
  have hlift := Nat.mul_le_mul_left K (Nat.pow_le_pow_right
    (by omega : 0<(CylinderActualFeatureEvaluator.input v feature).length+1)
    (show E ≤ max 1 E by omega))
  have hlin : (CylinderActualFeatureEvaluator.input v feature).length+1≤
      ((CylinderActualFeatureEvaluator.input v feature).length+1)^(max 1 E) := by
    simpa using Nat.pow_le_pow_right
      (by omega : 0<(CylinderActualFeatureEvaluator.input v feature).length+1)
      (show 1 ≤ max 1 E by omega)
  change CylinderActualFeatureEvaluator.mapClock v feature≤_ at hm
  unfold CylinderActualFeatureEvaluator.clock
  nlinarith

theorem cell_polynomial : ∃ C d : ℕ,1≤d ∧
    ∀ {q : ℕ} (v : Fin q → ℕ) (feature : List (ℕ × ℕ))
      (valid : ∀p∈feature,p.1<q),
      CylinderActualCellEvaluator.clock v feature ≤
        C*((CylinderActualCellEvaluator.input v feature).length+1)^d := by
  obtain ⟨C,d,hd,hC⟩ := feature_polynomial
  refine ⟨C*2^d+40,d,hd,?_⟩
  intro q v feature valid
  have hf := hC v feature valid
  have hr : (CylinderActualFeatureEvaluator.input v feature).length≤
      2*(CylinderActualCellEvaluator.input v feature).length :=
    reassociated_length_le (List.replicate q true) (encodeFeature feature)
      (CylinderEvalPairMachine.tupleWord v)
  have hp := Nat.mul_le_mul_left C (Nat.pow_le_pow_left
    (show (CylinderActualFeatureEvaluator.input v feature).length+1≤
      2*(CylinderActualCellEvaluator.input v feature).length+1 by omega) d)
  have hm := routed_envelope (CylinderActualCellEvaluator.input v feature).length C d
  have hlin := linear_plus (CylinderActualCellEvaluator.input v feature).length (C*2^d) 40 d hd
  unfold CylinderActualCellEvaluator.clock
  nlinarith

theorem row_polynomial : ∃ C d : ℕ,1≤d ∧
    ∀ {q : ℕ} (feature : List (ℕ × ℕ)) (source : Array ((Fin q → ℕ) × ℚ))
      (valid : ∀p∈feature,p.1<q),
      CylinderActualRowEvaluator.clock feature source ≤
        C*((CylinderActualRowEvaluator.input feature source).length+1)^d := by
  obtain ⟨C,d,hd,hC⟩ := cell_polynomial
  obtain ⟨K,E,hK⟩ := CylinderEvalMapPolynomial.uniform_from_callback
    CylinderActualCellEvaluator.machine true C d
  refine ⟨K*2^E+40,max 1 E,by omega,?_⟩
  intro q feature source valid
  have hb : ∀w∈CylinderProductionProjection.tupleWords source,
      CylinderActualRowEvaluator.cellClock q feature w≤
        C*((packet (CylinderActualRowEvaluator.context q feature) w).length+1)^d := by
    intro w hw
    obtain ⟨v,rfl⟩ := tuple_mem source w hw
    simpa only [CylinderActualRowEvaluator.cellClock,tupleValue_tupleWord,
      CylinderActualRowEvaluator.context,packet,CylinderActualCellEvaluator.input] using
      hC v feature valid
  have hm := hK (CylinderActualRowEvaluator.context q feature)
    (CylinderProductionProjection.tupleWords source)
    (CylinderActualRowEvaluator.cellResult q feature) (CylinderActualRowEvaluator.cellClock q feature)
    (CylinderActualRowEvaluator.cell_runs feature source valid) hb
  change CylinderActualRowEvaluator.mapClock feature source≤
    K*((CylinderActualRowEvaluator.routedInput feature source).length+1)^E at hm
  have hr : (CylinderActualRowEvaluator.routedInput feature source).length≤
      2*(CylinderActualRowEvaluator.input feature source).length :=
    reassociated_length_le (List.replicate q true)
      (SourceListEncoding.encode (CylinderProductionProjection.tupleWords source)) (encodeFeature feature)
  exact routed_power _ _ _ K E hr hm

theorem matrix_polynomial : ∃ C d : ℕ,1≤d ∧
    ∀ (q D : ℕ) (alphabet : Array ℕ) (source : Array ((Fin q → ℕ) × ℚ)),
      CylinderActualMatrixEvaluator.clock q D alphabet source ≤
        C*((CylinderActualMatrixEvaluator.input q D alphabet source).length+1)^d := by
  obtain ⟨C,d,hd,hC⟩ := row_polynomial
  obtain ⟨K,E,hK⟩ := CylinderEvalMapPolynomial.uniform_from_callback
    CylinderActualRowEvaluator.machine true C d
  refine ⟨K*2^E+40,max 1 E,by omega,?_⟩
  intro q D alphabet source
  have hb : ∀w∈CylinderActualMatrixEvaluator.featureItems q D alphabet,
      CylinderActualMatrixEvaluator.rowClock source w≤
        C*((packet (CylinderActualMatrixEvaluator.context source) w).length+1)^d := by
    intro w hw
    obtain ⟨feature,hf,rfl⟩ := List.mem_map.mp hw
    have hv := generated_features_valid q D alphabet feature hf
    simpa only [CylinderActualMatrixEvaluator.rowClock,featureValue_encodeFeature,
      CylinderActualMatrixEvaluator.context,packet,CylinderActualRowEvaluator.input] using
      hC feature source hv
  have hm := hK (CylinderActualMatrixEvaluator.context source)
    (CylinderActualMatrixEvaluator.featureItems q D alphabet)
    (CylinderActualMatrixEvaluator.rowResult source) (CylinderActualMatrixEvaluator.rowClock source)
    (CylinderActualMatrixEvaluator.row_runs q D alphabet source) hb
  change CylinderActualMatrixEvaluator.mapClock q D alphabet source≤
    K*((CylinderActualMatrixEvaluator.routedInput q D alphabet source).length+1)^E at hm
  have hr : (CylinderActualMatrixEvaluator.routedInput q D alphabet source).length≤
      2*(CylinderActualMatrixEvaluator.input q D alphabet source).length :=
    prepared_length_le (List.replicate q true) (generatedFeatureBits q D alphabet)
      (SourceListEncoding.encode (CylinderProductionProjection.tupleWords source))
  exact routed_power _ _ _ K E hr hm

end CurrentAdditive.CylinderActualEvaluatorPolynomial

namespace CurrentAdditive.CylinderActualMatrixEvaluator

open EthInapproximability.CurrentPaper

noncomputable def coefficient : ℕ :=
  Classical.choose CylinderActualEvaluatorPolynomial.matrix_polynomial

noncomputable def exponent : ℕ :=
  Classical.choose (Classical.choose_spec CylinderActualEvaluatorPolynomial.matrix_polynomial)

theorem clock_polynomial (q D : ℕ) (alphabet : Array ℕ)
    (source : Array ((Fin q → ℕ) × ℚ)) :
    clock q D alphabet source≤coefficient*((input q D alphabet source).length+1)^exponent :=
  (Classical.choose_spec (Classical.choose_spec
    CylinderActualEvaluatorPolynomial.matrix_polynomial)).2 q D alphabet source

theorem outputs_polynomial (q D : ℕ) (alphabet : Array ℕ)
    (source : Array ((Fin q → ℕ) × ℚ)) :
    machine.OutputsWithin (input q D alphabet source)
      (CylinderFeatureCodec.cylinderMatrixBits q D alphabet source)
      (coefficient*((input q D alphabet source).length+1)^exponent) :=
  BitMachine.outputsWithin_mono machine (outputs q D alphabet source)
    (clock_polynomial q D alphabet source)

theorem prepared_outputs_polynomial (q : ℕ) (alphabet : Array (ℕ × ℚ))
    (source : Array ((Fin q → ℕ) × ℚ)) :
    machine.OutputsWithin
      (BitMachineBankCodec.encode ![List.replicate q true,
        CylinderFeatureCodec.generatedFeatureBits q 8192 (alphabet.map Prod.fst),
        SourceListEncoding.encode (CylinderProductionProjection.tupleWords source)])
      (CylinderFeatureCodec.cylinderMatrixBits q 8192 (alphabet.map Prod.fst) source)
      (coefficient*((input q 8192 (alphabet.map Prod.fst) source).length+1)^exponent) :=
  outputs_polynomial q 8192 (alphabet.map Prod.fst) source

end CurrentAdditive.CylinderActualMatrixEvaluator

#print axioms CurrentAdditive.CylinderActualEvaluatorPolynomial.feature_polynomial
#print axioms CurrentAdditive.CylinderActualEvaluatorPolynomial.cell_polynomial
#print axioms CurrentAdditive.CylinderActualEvaluatorPolynomial.row_polynomial
#print axioms CurrentAdditive.CylinderActualEvaluatorPolynomial.matrix_polynomial
#print axioms CurrentAdditive.CylinderActualMatrixEvaluator.prepared_outputs_polynomial
