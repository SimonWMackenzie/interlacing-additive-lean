import Paper2.CodeGeneratorExponentAlgebra

namespace Paper2.CodeGeneratorExponentInput

theorem input_self_bound (X : Nat) :
    8*X+1 ≤ 9*(X+1)^6 := by
  ring_nf
  omega

#print axioms input_self_bound

end Paper2.CodeGeneratorExponentInput
