import EthInapproximability.CurrentPaper.SourceGenericPairWordBound
import EthInapproximability.CurrentPaper.SourceClausePrimitivePolynomial
import EthInapproximability.CurrentPaper.ClockStepSemantics
import EthInapproximability.CurrentPaper.SourceGenericUnitAddressCost

/-! A public-input bound for the first, non-cleanup part of the generic
ordered-pair unit phase. This charges the real fixed-bank writer, physical
address computation, and unary/binary work; it does not yet bound cleanup. -/

namespace EthInapproximability.CurrentPaper.SourceGenericPairEnumeration

open SourceGenericPrefixMachine SourceBooleanPrefix
set_option maxHeartbeats 2000000

theorem unit_pairCost_le_poly (n a ordinal w ell : Nat)
    (saved output count : List Bool) :
    UnitCycle.pairCost n a ordinal w ell saved output count ≤
      (16*UnaryBinaryEncoding.coefficient+100)*
        (n+a+ordinal+w+ell+1)^4 := by
  let M := n+a+ordinal+w+ell+1
  let p := ordinal*w+(n*a+ell)
  have hm : 1 ≤ M := by dsimp [M]; omega
  have hn : n ≤ M := by dsimp [M]; omega
  have ha : a ≤ M := by dsimp [M]; omega
  have ho : ordinal ≤ M := by dsimp [M]; omega
  have hw : w ≤ M := by dsimp [M]; omega
  have he : ell ≤ M := by dsimp [M]; omega
  have hna : n*a ≤ M^2 := by
    have h := Nat.mul_le_mul hn ha
    simpa [pow_two] using h
  have how : ordinal*w ≤ M^2 := by
    have h := Nat.mul_le_mul ho hw
    simpa [pow_two] using h
  have hp : p ≤ 3*M^2 := by
    dsimp [p]
    nlinarith
  have hbits : p.bits.length ≤ 3*M^2 :=
    (ClockStepSemantics.bits_length_le p).trans hp
  have hsizes (i : Fin 3) : UnitStage.constantSize a w ell i ≤ M := by
    fin_cases i <;> simp [UnitStage.constantSize] <;> omega
  have hbatch := SourceClauseCallbackPrimitivePolynomial.costPrefix_le
    (UnitStage.constantSize a w ell) M hsizes 3
  have haddress := SourceGenericUnitAddress.cost_polynomial
    n a ordinal w ell
  have hm2 : M ≤ M^2 := by nlinarith
  have hm24 : M^2 ≤ M^4 := by
    calc
      M^2 = M*M := by ring
      _ ≤ M^2*M^2 := Nat.mul_le_mul hm2 hm2
      _ = M^4 := by ring
  have hm14 : M ≤ M^4 := hm2.trans hm24
  have hm04 : 1 ≤ M^4 := by omega
  change UnitCycle.pairCost n a ordinal w ell saved output count ≤
    (16*UnaryBinaryEncoding.coefficient+100)*M^4
  dsimp only [UnitCycle.pairCost, UnitRun.cost]
  change p.bits.length ≤ 3*M^2 at hbits
  change SourceClauseFixedBatch.costPrefix
    (UnitStage.constantSize a w ell) 3 ≤ 3*(M+1) at hbatch
  change SourceGenericUnitAddress.cost n a ordinal w ell ≤
    (16*UnaryBinaryEncoding.coefficient+36)*M^4 at haddress
  change SourceClauseFixedBatch.costPrefix
      (UnitStage.constantSize a w ell) 3 + 1 +
      (SourceGenericUnitAddress.cost n a ordinal w ell +
        (2*p.bits.length+3)+1+(5*p.bits.length+13)+1)+1 ≤
      (16*UnaryBinaryEncoding.coefficient+100)*M^4
  nlinarith only [haddress, hbatch, hbits, hm14, hm24, hm04,
    Nat.zero_le (UnaryBinaryEncoding.coefficient*M^4)]

#print axioms unit_pairCost_le_poly

end EthInapproximability.CurrentPaper.SourceGenericPairEnumeration
