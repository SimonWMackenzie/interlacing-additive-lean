import Paper2.CodeGeneratorExponent

/-! An absolute-power bound for the already checked public physical clock.
This algebra is disjoint from the frozen compiler packet. -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 32768

namespace Paper2.CodeGeneratorExponentPublic

open Paper2.CodeGeneratorClockSum
open Paper2.CodeGeneratorExponent

def coeff : Nat := coefficient*4096+100

theorem roundPoly_input_majorant (M A : Nat) :
    Paper2.CodeGeneratorStepGrowth.roundPoly M M M M M M A A ≤
      Paper2.CodeGeneratorStepGrowth.roundPoly
        (M+A+1) (M+A+1) (M+A+1) (M+A+1)
        (M+A+1) (M+A+1) (M+A+1) (M+A+1) := by
  dsimp [Paper2.CodeGeneratorStepGrowth.roundPoly,
    Paper2.CodeRecursiveStepClock.polynomialClock,
    Paper2.CodeRecursiveStepClock.graphCap,
    Paper2.CodeRecursiveStepClock.taggedCap,
    Paper2.TaggedCompiler.polynomialClock]
  gcongr <;> omega

theorem roundPoly_public_bound (M A : Nat)
    (hMA : M + 1 ≤ A) :
    Paper2.CodeGeneratorStepGrowth.roundPoly M M M M M M A A ≤
      coefficient*4096*A^6 := by
  let X := M+A+1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hM : X+1 ≤ 4*A := by dsimp [X]; omega
  have hpow := Nat.pow_le_pow_left hM 6
  have hp : (4*A)^6 = 4096*A^6 := by ring
  rw [hp] at hpow
  have hmul := Nat.mul_le_mul_left coefficient hpow
  calc
    Paper2.CodeGeneratorStepGrowth.roundPoly M M M M M M A A
      ≤ Paper2.CodeGeneratorStepGrowth.roundPoly X X X X X X X X := by
        simpa only [X] using roundPoly_input_majorant M A
    _ ≤ coefficient*(X+1)^6 := roundPoly_self_bound X hX
    _ ≤ coefficient*4096*A^6 := by nlinarith

#print axioms roundPoly_public_bound

theorem publicClock_scalar_bound (M A k : Nat)
    (hMA : M + 1 ≤ A) :
    6*M+19+k*(Paper2.CodeGeneratorStepGrowth.roundPoly
      M M M M M M A A + 1) ≤ coeff*(k+1)*A^6 := by
  let P := Paper2.CodeGeneratorStepGrowth.roundPoly M M M M M M A A
  let T := coefficient*4096
  have hP : P ≤ T*A^6 := roundPoly_public_bound M A hMA
  have hA6 : A ≤ A^6 := by
    calc
      A = A^1 := by simp
      _ ≤ A^6 := pow_le_pow_right₀ (by omega) (by omega)
  have hOne : 1 ≤ A^6 := by omega
  have hfront : 6*M+19 ≤ 25*A^6 := by omega
  have hper : P+1 ≤ (T+1)*A^6 := by
    have hh : 1 ≤ 1*A^6 := by simpa using hOne
    calc
      P+1 ≤ T*A^6+1*A^6 := by omega
      _ = (T+1)*A^6 := by ring
  have hk := Nat.mul_le_mul_left k hper
  have hcoeff : 25+k*(T+1) ≤ coeff*(k+1) := by
    dsimp [T, coeff]
    nlinarith
  have hm := Nat.mul_le_mul_right (A^6) hcoeff
  have heq : 25*A^6+k*((T+1)*A^6) =
      (25+k*(T+1))*A^6 := by ring
  dsimp [P] at *
  omega

#print axioms publicClock_scalar_bound

theorem publicClock_le_coeff (L k : Nat) :
    publicCompilerClock L k ≤
      coeff*(k+1)*((GeneratorPublicCap.publicCap L+1)^(18*(k+1)))^6 := by
  let M := GeneratorPublicCap.publicCap L
  let A := (M+1)^(18*(k+1))
  have hMA : M+1 ≤ A := by
    have hp : (M+1)^1 ≤ (M+1)^(18*(k+1)) :=
      pow_le_pow_right₀ (by omega) (by omega)
    simpa [A] using hp
  have h := publicClock_scalar_bound M A k hMA
  dsimp [publicCompilerClock]
  change 6*M+19+k*(Paper2.CodeGeneratorStepGrowth.roundPoly
      M M M M M M A A + 1) ≤ coeff*(k+1)*A^6
  exact h

theorem nat_le_two_pow (j : Nat) : j ≤ 2^j := by
  induction j with
  | zero => norm_num
  | succ j ih =>
      rw [pow_succ]
      have hpos : 1 ≤ 2^j := Nat.one_le_two_pow
      omega

#print axioms publicClock_le_coeff
#print axioms nat_le_two_pow

theorem publicCap_plus_le (L : Nat) (hL : 1 ≤ L) :
    GeneratorPublicCap.publicCap L + 1 ≤ 2^(8*L) := by
  let M := GeneratorPublicCap.publicCap L
  have hM : 1 ≤ M := by
    dsimp [M, GeneratorPublicCap.publicCap]
    exact Nat.one_le_two_pow
  have hdouble : M+1 ≤ 2*M := by omega
  have heq : 2*M = 2^(7*L+1) := by
    dsimp [M, GeneratorPublicCap.publicCap]
    rw [pow_add]
    ring
  calc
    M+1 ≤ 2*M := hdouble
    _ = 2^(7*L+1) := heq
    _ ≤ 2^(8*L) := pow_le_pow_right₀ (by omega) (by omega)

theorem publicA_le_pow (L k : Nat) (hL : 1 ≤ L) :
    (GeneratorPublicCap.publicCap L+1)^(18*(k+1)) ≤
      2^(144*(k+1)*L) := by
  have hp := Nat.pow_le_pow_left (publicCap_plus_le L hL) (18*(k+1))
  calc
    (GeneratorPublicCap.publicCap L+1)^(18*(k+1))
      ≤ (2^(8*L))^(18*(k+1)) := hp
    _ = 2^(144*(k+1)*L) := by
      rw [← pow_mul]
      congr 1
      ring

def exponentConstant : Nat := coeff+865

theorem publicCompilerClock_le_two_pow (L k : Nat) (hL : 1 ≤ L) :
    publicCompilerClock L k ≤
      2^(exponentConstant*(k+1)*L) := by
  let T := (k+1)*L
  let A := (GeneratorPublicCap.publicCap L+1)^(18*(k+1))
  have hT : 1 ≤ T := by dsimp [T]; nlinarith
  have hA : A ≤ 2^(144*T) := by
    simpa only [A, T, Nat.mul_assoc] using publicA_le_pow L k hL
  have hA6 : A^6 ≤ 2^(864*T) := by
    have hp := Nat.pow_le_pow_left hA 6
    calc
      A^6 ≤ (2^(144*T))^6 := hp
      _ = 2^(864*T) := by
        rw [← pow_mul]
        congr 1
        ring
  have hcoeff : coeff ≤ 2^coeff := nat_le_two_pow coeff
  have hkT : k+1 ≤ T := by dsimp [T]; nlinarith
  have hk : k+1 ≤ 2^T :=
    (nat_le_two_pow (k+1)).trans
      (pow_le_pow_right₀ (by omega) hkT)
  have hexp : coeff+T+864*T ≤ exponentConstant*T := by
    have hm := Nat.mul_le_mul_left coeff hT
    dsimp [exponentConstant]
    nlinarith
  calc
    publicCompilerClock L k ≤ coeff*(k+1)*A^6 := by
      simpa only [A] using publicClock_le_coeff L k
    _ ≤ 2^coeff*2^T*2^(864*T) := by gcongr
    _ = 2^(coeff+T+864*T) := by rw [pow_add, pow_add]
    _ ≤ 2^(exponentConstant*T) :=
      pow_le_pow_right₀ (by omega) hexp
    _ = 2^(exponentConstant*(k+1)*L) := by
      simp only [T, Nat.mul_assoc]

#print axioms publicCompilerClock_le_two_pow

#print axioms roundPoly_input_majorant

end Paper2.CodeGeneratorExponentPublic
