import Paper2.CodeFullRunConsumer
import Mathlib.Tactic

/-! Uniform polynomial cap for the admitted physical interpreter clock.
All coefficients are fixed properties of its finite instruction tables. -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 16384

namespace Paper2.CodeSamplerInterpreterPolynomial

open Paper2.GeneratorCode Paper2.GeneratorSerialization
open EthInapproximability.CurrentPaper

noncomputable section

def rawCoeff : Nat :=
  13 + (UnaryBinaryEncoding.coefficient+130) + 72 + 77

def actualClock (root : Code) (B R N : Nat) : Nat :=
  (codeSize root+1)*CodeFullRepeatPublic.repeatStepCap root B R +
    N*(R*B)+2

theorem raw_cap_le (root : Code) (B R A : Nat)
    (hS : codeSize root ≤ A) (hB : B ≤ A) (hR : R ≤ A)
    (hA : 1 ≤ A) :
    CodeRawStepPublicBound.rawStepCap root B R ≤
      rawCoeff*(3*A+3)^3 := by
  let X := 3*A+3
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hs : codeSize root+3 ≤ X := by dsimp [X]; omega
  have hsum : codeSize root+B+R+2 ≤ X := by dsimp [X]; omega
  have hs2 : (codeSize root+3)^2 ≤ X^3 := by
    have hpow := Nat.pow_le_pow_left hs 2
    have hmono : X^2 ≤ X^3 := pow_le_pow_right₀ hX (by omega)
    exact hpow.trans hmono
  have hsum3 := Nat.pow_le_pow_left hsum 3
  have hX3 : X ≤ X^3 := by
    have hp : X^1 ≤ X^3 := pow_le_pow_right₀ hX (by omega)
    simpa using hp
  have hOne : 1 ≤ X^3 := le_trans hX hX3
  have h1 := Nat.mul_le_mul_left 13 hs2
  have h2 := Nat.mul_le_mul_left (UnaryBinaryEncoding.coefficient+130) hsum3
  have h3 := Nat.mul_le_mul_left 72 (hS.trans (le_trans (by dsimp [X]; omega : A ≤ X) hX3))
  have h4 := Nat.mul_le_mul_left 77 hOne
  change 13*(codeSize root+3)^2+
      (UnaryBinaryEncoding.coefficient+130)*
        (codeSize root+B+R+2)^3+
      72*codeSize root+77 ≤ rawCoeff*X^3
  calc
    _ ≤ 13*X^3+(UnaryBinaryEncoding.coefficient+130)*X^3+
        72*X^3+77*X^3 := by omega
    _ = rawCoeff*X^3 := by unfold rawCoeff; ring
    _ = _ := rfl

private theorem repeat_abstract (t C D P X : Nat)
    (ht : t ≤ C*X^3) (hX : 1 ≤ X^3) :
    t+(D*(P*t)+D+2)+1 ≤ ((1+D*P)*C+D+3)*X^3 := by
  have hmul := Nat.mul_le_mul_left (1+D*P) ht
  have hconst : D+3 ≤ (D+3)*X^3 := by
    simpa using Nat.mul_le_mul_left (D+3) hX
  calc
    _ = (1+D*P)*t+D+3 := by ring
    _ ≤ (1+D*P)*(C*X^3)+D+3 := by omega
    _ ≤ ((1+D*P)*C+D+3)*X^3 := by
      have heq : ((1+D*P)*C+D+3)*X^3 =
          (1+D*P)*(C*X^3)+(D+3)*X^3 := by ring
      rw [heq]
      omega

theorem repeat_cap_exists :
    ∃ C : Nat, ∀ (root : Code) (B R A : Nat),
      codeSize root ≤ A → B ≤ A → R ≤ A → 1 ≤ A →
      CodeFullRepeatPublic.repeatStepCap root B R ≤
        C*(3*A+3)^3 := by
  refine ⟨(1+CodeInterpreterReset.clearCount*
      CodeUniformResetBound.rawPushBound)*rawCoeff+
      CodeInterpreterReset.clearCount+3, ?_⟩
  intro root B R A hS hB hR hA
  let X := 3*A+3
  have hraw := raw_cap_le root B R A hS hB hR hA
  have hX3 : 1 ≤ X^3 := by
    have hX : 1 ≤ X := by dsimp [X]; omega
    have hp : X ≤ X^3 := by
      have hh : X^1 ≤ X^3 := pow_le_pow_right₀ hX (by omega)
      simpa using hh
    exact hX.trans hp
  have hrawX : CodeRawStepPublicBound.rawStepCap root B R ≤
      rawCoeff*X^3 := by simpa [X] using hraw
  have h := repeat_abstract
    (CodeRawStepPublicBound.rawStepCap root B R)
    rawCoeff CodeInterpreterReset.clearCount
    CodeUniformResetBound.rawPushBound X hrawX hX3
  change CodeRawStepPublicBound.rawStepCap root B R+
      (CodeInterpreterReset.clearCount*
        (CodeUniformResetBound.rawPushBound*
          CodeRawStepPublicBound.rawStepCap root B R)+
        CodeInterpreterReset.clearCount+2)+1 ≤
      ((1+CodeInterpreterReset.clearCount*
          CodeUniformResetBound.rawPushBound)*rawCoeff+
        CodeInterpreterReset.clearCount+3)*X^3
  exact h

def repeatCoeff : Nat := Classical.choose repeat_cap_exists

theorem repeat_cap_le (root : Code) (B R A : Nat)
    (hS : codeSize root ≤ A) (hB : B ≤ A) (hR : R ≤ A)
    (hA : 1 ≤ A) :
    CodeFullRepeatPublic.repeatStepCap root B R ≤
      repeatCoeff*(3*A+3)^3 :=
  Classical.choose_spec repeat_cap_exists root B R A hS hB hR hA

def interpreterCoeff : Nat := repeatCoeff+3

theorem actualClock_le (root : Code) (B R N A : Nat)
    (hS : codeSize root ≤ A) (hB : B ≤ A)
    (hR : R ≤ A) (hN : N ≤ A) (hA : 1 ≤ A) :
    actualClock root B R N ≤ interpreterCoeff*(3*A+3)^4 := by
  let X := 3*A+3
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hSx : codeSize root+1 ≤ X := by dsimp [X]; omega
  have hBx : B ≤ X := by dsimp [X]; omega
  have hRx : R ≤ X := by dsimp [X]; omega
  have hNx : N ≤ X := by dsimp [X]; omega
  have hrep := repeat_cap_le root B R A hS hB hR hA
  have hfirst : (codeSize root+1)*CodeFullRepeatPublic.repeatStepCap root B R ≤
      repeatCoeff*X^4 := by
    calc
      _ ≤ X*(repeatCoeff*X^3) := Nat.mul_le_mul hSx hrep
      _ = repeatCoeff*X^4 := by ring
  have hdraw : N*(R*B) ≤ X^4 := by
    have hprod := Nat.mul_le_mul hRx hBx
    have hprod2 := Nat.mul_le_mul hNx hprod
    have hp : X^3 ≤ X^4 := pow_le_pow_right₀ hX (by omega)
    calc
      N*(R*B) ≤ X*(X*X) := hprod2
      _ = X^3 := by ring
      _ ≤ X^4 := hp
  have htwo : 2 ≤ 2*X^4 := by
    have hp : X ≤ X^4 := by
      have hh : X^1 ≤ X^4 := pow_le_pow_right₀ hX (by omega)
      simpa using hh
    omega
  dsimp [actualClock, interpreterCoeff]
  have hsum : (codeSize root+1)*
      CodeFullRepeatPublic.repeatStepCap root B R+
        N*(R*B)+2 ≤ (repeatCoeff+3)*X^4 := by
    calc
      _ ≤ repeatCoeff*X^4+X^4+2*X^4 := by omega
      _ = (repeatCoeff+3)*X^4 := by ring
  simpa [X] using hsum

#print axioms raw_cap_le
#print axioms repeat_cap_le
#print axioms actualClock_le

end
end Paper2.CodeSamplerInterpreterPolynomial
