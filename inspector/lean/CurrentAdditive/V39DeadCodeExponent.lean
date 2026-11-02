import CurrentAdditive.V39DeadCodeClockSum

/-! An absolute exponent bound for the actual fixed recursive constructor.
The coefficient is a closed natural depending only on its finite control. -/

set_option maxHeartbeats 12000000
set_option maxRecDepth 32768

namespace CurrentAdditive.V39DeadCodeExponent

open Paper2

theorem step_self_bound (X : Nat) :
    CurrentAdditive.V39DeadCodeStepClock.polynomialClock X X X X X X X X ≤
      1000000 * (X+1)^6 := by
  dsimp [CurrentAdditive.V39DeadCodeStepClock.polynomialClock,
    CurrentAdditive.V39DeadCodeStepClock.graphCap,
    CurrentAdditive.V39DeadCodeStepClock.taggedCap,
    Paper2.TaggedCompiler.polynomialClock]
  ring_nf
  omega


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


theorem input_self_bound (X : Nat) :
    8*X+1 ≤ 9*(X+1)^6 := by
  ring_nf
  omega


def coefficient : Nat :=
  1000000000 * (CurrentAdditive.V39DeadCodeReentryBound.factor + 1) *
    (CurrentAdditive.V39DeadCodeStepGrowth.stepPush + 1)

theorem roundPoly_self_bound (X : Nat) (hX : 1 ≤ X) :
    CurrentAdditive.V39DeadCodeStepGrowth.roundPoly X X X X X X X X ≤
      coefficient * (X+1)^6 := by
  have hB : 1 ≤ (X+1)^6 := by
    have hp : 0 < (X+1)^6 := pow_pos (by omega) _
    omega
  have h := round_algebra
    (CurrentAdditive.V39DeadCodeStepClock.polynomialClock X X X X X X X X)
    X CurrentAdditive.V39DeadCodeReentryBound.factor
    CurrentAdditive.V39DeadCodeStepGrowth.stepPush ((X+1)^6)
    (step_self_bound X) (input_self_bound X) hB
  unfold CurrentAdditive.V39DeadCodeStepGrowth.roundPoly coefficient
  dsimp only
  have heq : X+X+X+X+X+X+X+X+1 = 8*X+1 := by omega
  rw [heq]
  exact h


def coeff : Nat := coefficient*4096+100

theorem roundPoly_input_majorant (M A : Nat) :
    CurrentAdditive.V39DeadCodeStepGrowth.roundPoly M M M M M M A A ≤
      CurrentAdditive.V39DeadCodeStepGrowth.roundPoly
        (M+A+1) (M+A+1) (M+A+1) (M+A+1)
        (M+A+1) (M+A+1) (M+A+1) (M+A+1) := by
  dsimp [CurrentAdditive.V39DeadCodeStepGrowth.roundPoly,
    CurrentAdditive.V39DeadCodeStepClock.polynomialClock,
    CurrentAdditive.V39DeadCodeStepClock.graphCap,
    CurrentAdditive.V39DeadCodeStepClock.taggedCap,
    Paper2.TaggedCompiler.polynomialClock]
  gcongr <;> omega

theorem roundPoly_public_bound (M A : Nat)
    (hMA : M + 1 ≤ A) :
    CurrentAdditive.V39DeadCodeStepGrowth.roundPoly M M M M M M A A ≤
      coefficient*4096*A^6 := by
  let X := M+A+1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hM : X+1 ≤ 4*A := by dsimp [X]; omega
  have hpow := Nat.pow_le_pow_left hM 6
  have hp : (4*A)^6 = 4096*A^6 := by ring
  rw [hp] at hpow
  have hmul := Nat.mul_le_mul_left coefficient hpow
  calc
    CurrentAdditive.V39DeadCodeStepGrowth.roundPoly M M M M M M A A
      ≤ CurrentAdditive.V39DeadCodeStepGrowth.roundPoly X X X X X X X X := by
        simpa only [X] using roundPoly_input_majorant M A
    _ ≤ coefficient*(X+1)^6 := roundPoly_self_bound X hX
    _ ≤ coefficient*4096*A^6 := by nlinarith

#print axioms roundPoly_public_bound

theorem publicClock_scalar_bound (M A k : Nat)
    (hMA : M + 1 ≤ A) :
    6*M+19+k*(CurrentAdditive.V39DeadCodeStepGrowth.roundPoly
      M M M M M M A A + 1) ≤ coeff*(k+1)*A^6 := by
  let P := CurrentAdditive.V39DeadCodeStepGrowth.roundPoly M M M M M M A A
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


theorem nat_le_two_pow (j : Nat) : j ≤ 2^j := by
  induction j with
  | zero => norm_num
  | succ j ih =>
      rw [pow_succ]
      have hpos : 1 ≤ 2^j := Nat.one_le_two_pow
      omega

def exponentConstant : Nat := coeff+55

theorem publicCompilerClock_le_two_pow (E k : Nat) :
    V39DeadCodeClockSum.publicCompilerClock E k ≤
      2^(exponentConstant*(k+1)*(E+10)) := by
  let T := (k+1)*(E+10)
  let A := 2^(9*T)
  have hT : 1 ≤ T := by dsimp [T]; nlinarith
  have hMA : 2^E+1 ≤ A := by
    have hm : 2^E+1 ≤ 2^(E+1) := by
      rw [pow_succ]
      have := Nat.one_le_two_pow (n := E)
      omega
    exact hm.trans (pow_le_pow_right₀ (by decide) (by dsimp [T]; nlinarith))
  have hscalar := publicClock_scalar_bound (2^E) A k hMA
  have hA6 : A^6 = 2^(54*T) := by
    dsimp [A]
    rw [← pow_mul]
    congr 1
    ring
  rw [hA6] at hscalar
  have hcoeff : coeff ≤ 2^coeff := nat_le_two_pow coeff
  have hkT : k+1 ≤ T := by dsimp [T]; nlinarith
  have hk : k+1 ≤ 2^T :=
    (nat_le_two_pow (k+1)).trans (pow_le_pow_right₀ (by decide) hkT)
  have hexp : coeff+T+54*T ≤ exponentConstant*T := by
    have hm := Nat.mul_le_mul_left coeff hT
    dsimp [exponentConstant]
    nlinarith
  calc
    V39DeadCodeClockSum.publicCompilerClock E k ≤ coeff*(k+1)*2^(54*T) := by
      simpa only [V39DeadCodeClockSum.publicCompilerClock, A, T, Nat.mul_assoc] using hscalar
    _ ≤ 2^coeff*2^T*2^(54*T) := by gcongr
    _ = 2^(coeff+T+54*T) := by rw [pow_add, pow_add]
    _ ≤ 2^(exponentConstant*T) := pow_le_pow_right₀ (by decide) hexp
    _ = 2^(exponentConstant*(k+1)*(E+10)) := by simp only [T, Nat.mul_assoc]

theorem compilerClock_le_two_pow (n p q₁ q₂ s w Q E k : Nat)
    (hs : 3 ≤ s)
    (hn : n ≤ 2^E) (hp : p ≤ 2^E) (hq₁ : q₁ ≤ 2^E) (hq₂ : q₂ ≤ 2^E)
    (hsE : s ≤ 2^E) (hw : w ≤ 2^E) (hQ : Q ≤ 2^E) :
    V39DeadCodeComplete.clock n p s q₁ q₂ w Q k ≤
      2^(exponentConstant*(k+1)*(E+10)) :=
  (V39DeadCodeClockSum.compilerClock_le_public n p q₁ q₂ s w Q E k hs
    hn hp hq₁ hq₂ hsE hw hQ).trans (publicCompilerClock_le_two_pow E k)

#print axioms step_self_bound
#print axioms roundPoly_self_bound
#print axioms compilerClock_le_two_pow

end CurrentAdditive.V39DeadCodeExponent
