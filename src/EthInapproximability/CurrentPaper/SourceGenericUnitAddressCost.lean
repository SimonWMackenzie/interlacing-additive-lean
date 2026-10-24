import EthInapproximability.CurrentPaper.SourceGenericUnitAddress

/-! A deliberately coarse uniform clock bound for the unchanged generic
prefix-address controller. Fixed a,width,position can later be absorbed
into the whole prefix routine's coefficient. -/

namespace EthInapproximability.CurrentPaper.SourceGenericUnitAddress

theorem cost_polynomial (n a ordinal w ell : Nat) :
    cost n a ordinal w ell ≤
      (16 * UnaryBinaryEncoding.coefficient + 36) *
        (n + a + ordinal + w + ell + 1) ^ 4 := by
  let M := n + a + ordinal + w + ell + 1
  have hm : 1 ≤ M := by omega
  have hn : n ≤ M := by omega
  have ha : a ≤ M := by omega
  have ho : ordinal ≤ M := by omega
  have hw : w ≤ M := by omega
  have he : ell ≤ M := by omega
  have hna : n * a ≤ M ^ 2 := by
    have h := Nat.mul_le_mul hn ha
    simpa [pow_two] using h
  have how : ordinal * w ≤ M ^ 2 := by
    have h := Nat.mul_le_mul ho hw
    simpa [pow_two] using h
  have hm2 : M ≤ M ^ 2 := by nlinarith
  have hm24 : M ^ 2 ≤ M ^ 4 := by
    have h := Nat.mul_le_mul hm2 hm2
    nlinarith [h]
  have hp : ordinal * w + (n * a + ell) + 1 ≤ 4 * M ^ 2 := by
    nlinarith
  have hsq : (ordinal * w + (n * a + ell) + 1) ^ 2 ≤ 16 * M ^ 4 := by
    have h := Nat.mul_le_mul hp hp
    nlinarith [h]
  have hcoeff := Nat.mul_le_mul_left UnaryBinaryEncoding.coefficient hsq
  change cost n a ordinal w ell ≤
    (16 * UnaryBinaryEncoding.coefficient + 36) * M ^ 4
  simp only [cost, MatrixAddressMachine.exactTime]
  nlinarith

#print axioms cost_polynomial

end EthInapproximability.CurrentPaper.SourceGenericUnitAddress
