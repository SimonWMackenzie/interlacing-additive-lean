import Paper2.CodeGeneratorExponentCore

set_option maxHeartbeats 2000000

namespace Paper2.CodeGeneratorExponentAlgebra

theorem round_algebra (S X F P B : Nat)
    (hS : S ≤ 1000000*B)
    (hInput : 8*X+1 ≤ 9*B)
    (hB : 1 ≤ B) :
    S + F*(8*X+1+P*S+1)+11 ≤
      1000000000*(F+1)*(P+1)*B := by
  have hcoef : 1000011 + F*(10+1000000*P) ≤
      1000000000*(F+1)*(P+1) := by
    nlinarith
  have hmul := Nat.mul_le_mul_left P hS
  have harg : 8*X+1+P*S+1 ≤ 9*B+P*(1000000*B)+B := by
    omega
  have hF := Nat.mul_le_mul_left F harg
  have hfirst : S+F*(8*X+1+P*S+1)+11 ≤
      1000000*B+F*(9*B+P*(1000000*B)+B)+11 := by omega
  have heq : 1000000*B+F*(9*B+P*(1000000*B)+B)+11 =
      (1000000+F*(10+1000000*P))*B+11 := by ring
  have hm := Nat.mul_le_mul_right B hcoef
  have heq2 : (1000011+F*(10+1000000*P))*B =
      (1000000+F*(10+1000000*P))*B+11*B := by ring
  rw [heq2] at hm
  have h11 : 11 ≤ 11*B := by nlinarith
  rw [heq] at hfirst
  omega

#print axioms round_algebra

end Paper2.CodeGeneratorExponentAlgebra
