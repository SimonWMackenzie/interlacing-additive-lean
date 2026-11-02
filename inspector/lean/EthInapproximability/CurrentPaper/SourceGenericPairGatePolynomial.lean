import EthInapproximability.CurrentPaper.SourceGenericPairUnitPolynomial

/-! Polynomial charge for the physical generic pair-gate preparation and
row writer, before the shared cleanup phase. -/

namespace EthInapproximability.CurrentPaper.SourceGenericPairEnumeration

open SourceGenericPrefixMachine SourceBooleanPrefix
open SourceBooleanEncoding
set_option maxHeartbeats 2000000

theorem gate_pre_le_poly {n a : Nat} (v : Fin n) (bit : Fin a)
    (ell : Fin 2) (ordinal w : Nat) (sign : Bool) :
    GateOperands.cost a bit.val w (List.replicate v.val true) +
      (v.val + bit.val + 4) + (2*ordinal+2) +
      (PairGatePatch.offsetSize ell 0+2)+3+
      SourceClauseRowGate.cost v.val a bit.val n ell.val ordinal w sign+1 ≤
      100000*(UnaryBinaryEncoding.coefficient+1)*
        (n+a+v.val+ordinal+w+ell.val+5)^4 := by
  let M := n+a+v.val+ordinal+w+ell.val+5
  have hm : 5 ≤ M := by dsimp [M]; omega
  have hn : n ≤ M := by dsimp [M]; omega
  have ha : a ≤ M := by dsimp [M]; omega
  have hv : v.val ≤ M := by dsimp [M]; omega
  have hbit : bit.val ≤ M := by dsimp [M]; omega
  have hslot : ordinal ≤ M := by dsimp [M]; omega
  have hw : w ≤ M := by dsimp [M]; omega
  have hell : ell.val ≤ M := by dsimp [M]; omega
  have hsize (i : Fin 5) : GateOperands.constantSize a bit.val w i ≤ M := by
    fin_cases i <;> simp [GateOperands.constantSize] <;> omega
  have hbatch := SourceClauseCallbackPrimitivePolynomial.costPrefix_le
    (GateOperands.constantSize a bit.val w) M hsize 5
  have hva : v.val*a ≤ M^2 := by
    have h := Nat.mul_le_mul hv ha
    simpa [pow_two] using h
  have hna : n*a ≤ M^2 := by
    have h := Nat.mul_le_mul hn ha
    simpa [pow_two] using h
  have how : ordinal*w ≤ M^2 := by
    have h := Nat.mul_le_mul hslot hw
    simpa [pow_two] using h
  have hp1 : v.val*a+bit.val+1 ≤ 2*M^2 := by
    have hm2 : M ≤ M^2 := by nlinarith
    omega
  have hp2 : ordinal*w+(n*a+ell.val)+1 ≤ 3*M^2 := by
    have hm2 : M ≤ M^2 := by nlinarith
    omega
  have hsq1 : (v.val*a+bit.val+1)^2 ≤ 4*M^4 := by
    have h := Nat.mul_le_mul hp1 hp1
    nlinarith only [h]
  have hsq2 : (ordinal*w+(n*a+ell.val)+1)^2 ≤ 9*M^4 := by
    have h := Nat.mul_le_mul hp2 hp2
    nlinarith only [h]
  have hbits1 : (v.val*a+bit.val).bits.length ≤ 2*M^2 := by
    have h := ClockStepSemantics.bits_length_le (v.val*a+bit.val)
    omega
  have hbits2 : (ordinal*w+(n*a+ell.val)).bits.length ≤ 3*M^2 := by
    have h := ClockStepSemantics.bits_length_le
      (ordinal*w+(n*a+ell.val))
    omega
  have hbits3 : (ordinal*w+(n*a+ell.val)+1).bits.length ≤ 3*M^2 := by
    have h := ClockStepSemantics.bits_length_le
      (ordinal*w+(n*a+ell.val)+1)
    omega
  have hbits4 : (n*a+ell.val).bits.length ≤ 2*M^2 := by
    have h := ClockStepSemantics.bits_length_le (n*a+ell.val)
    have hm2 : M ≤ M^2 := by nlinarith
    omega
  have hm2 : M ≤ M^2 := by nlinarith
  have hm24 : M^2 ≤ M^4 := by
    calc
      M^2 = M*M := by ring
      _ ≤ M^2*M^2 := Nat.mul_le_mul hm2 hm2
      _ = M^4 := by ring
  have hm14 : M ≤ M^4 := hm2.trans hm24
  have hm04 : 1 ≤ M^4 := by omega
  have hcoeff1 := Nat.mul_le_mul_left UnaryBinaryEncoding.coefficient hsq1
  have hcoeff2 := Nat.mul_le_mul_left UnaryBinaryEncoding.coefficient hsq2
  change _ ≤ 100000*(UnaryBinaryEncoding.coefficient+1)*M^4
  simp only [GateOperands.cost, SourceClauseRowGate.cost,
    SourceClauseGateSlotAddress.cost, SourceLiteralWriter.emitTime,
    SourceLiteralWriter.words, SourceClauseGatePrepare.firstClause,
    SourceClauseGatePrepare.secondClause,
    SourceClauseGatePrepare.thirdClause,
    MatrixAddressMachine.exactTime,
    SourceClauseEncoding.positive, SourceClauseEncoding.negative,
    SourceClauseEncoding.negate, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
    Matrix.cons_val_succ, List.length_replicate,
    PairGatePatch.offsetSize]
  nlinarith only [hbatch, hsq1, hsq2, hbits1, hbits2, hbits3,
    hbits4, hna, hva, how, hn, ha, hv, hbit, hslot, hw, hell,
    hm14, hm24, hm04, hcoeff1, hcoeff2,
    Nat.zero_le (UnaryBinaryEncoding.coefficient*M^4)]

#print axioms gate_pre_le_poly

end EthInapproximability.CurrentPaper.SourceGenericPairEnumeration
