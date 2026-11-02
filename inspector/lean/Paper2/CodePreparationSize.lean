import Paper2.CodeSampleCompilerExponent
import Paper2.GeneratorSize

/-! Exact sample syntax size and charged copying overhead for preparation.
These estimates will be applied to the existing physical loader, not used
as substitutes for its bank or execution theorem. -/

set_option maxHeartbeats 1000000

namespace Paper2.CodePreparationSize

open Paper2.GeneratorCode Paper2.GeneratorSerialization

theorem sample_size (mX mY : Nat) (row col : Code) :
    codeSize (.append (copies mY col) (copies mX row)) =
      11 + mY*(codeSize col+3) + mX*(codeSize row+3) := by
  simp only [codeSize, GeneratorSize.copies_size]
  omega

theorem sample_size_le (mX mY A : Nat) (row col : Code)
    (hA : 1 ≤ A) (hx : mX ≤ A) (hy : mY ≤ A)
    (hr : codeSize row ≤ A) (hc : codeSize col ≤ A) :
    codeSize (.append (copies mY col) (copies mX row)) ≤ 19*A^2 := by
  have hx' := Nat.mul_le_mul hx (Nat.add_le_add_right hr 3)
  have hy' := Nat.mul_le_mul hy (Nat.add_le_add_right hc 3)
  rw [sample_size]
  have ha2 : A ≤ A^2 := by nlinarith
  nlinarith only [hx', hy', ha2, hA]

theorem preparation_overhead_le (mX mY A : Nat) (row col : Code)
    (hA : 1 ≤ A) (hx : mX ≤ A) (hy : mY ≤ A)
    (hr : codeSize row ≤ A) (hc : codeSize col ≤ A) :
    (2*(encodeCode (.append (copies mY col) (copies mX row))).length+2+1) +
      (2*mX+2)+(2*mY+2)+2+1 ≤ 4096*A^2 := by
  rw [encodeCode_length]
  have hsize := sample_size_le mX mY A row col hA hx hy hr hc
  have ha2 : A ≤ A^2 := by nlinarith
  nlinarith only [hsize, hx, hy, ha2, hA]

#print axioms sample_size
#print axioms sample_size_le
#print axioms preparation_overhead_le

end Paper2.CodePreparationSize
