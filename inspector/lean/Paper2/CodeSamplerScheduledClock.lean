import Paper2.CodeSamplerScheduledBounds
import Mathlib.Tactic

/-! Exponential bound on the *actual* scheduled physical interpreter clock. -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

namespace Paper2.CodeSamplerScheduledClock

open GeneratorCode GeneratorSerialization
open RecursiveSamplingExecution
open SourceProfileParameters SourceRecursiveNoSampling
open ParameterizedCanonicalSource

noncomputable def exponentConstant : Nat :=
  CodeSamplerInterpreterPolynomial.interpreterCoeff+732

private theorem polynomial_to_pow (C T : Nat) (hT : 1 ≤ T) :
    C*(3*2^(180*T)+3)^4 ≤ 2^((C+732)*T) := by
  let A := 2^(180*T)
  have hA : 1 ≤ A := by
    have hp : 0 < A := by
      dsimp [A]
      exact pow_pos (by decide : 0 < (2:Nat)) _
    omega
  have hX : 3*A+3 ≤ 8*A := by omega
  have hpow := Nat.pow_le_pow_left hX 4
  have hC := WidthDomination.nat_le_two_pow C
  have hCT : C ≤ C*T := by
    simpa using Nat.mul_le_mul_left C hT
  have hA4 : A^4 = 2^(720*T) := by
    dsimp [A]
    rw [← pow_mul]
    congr 1
    omega
  have hnum : 4096*A^4 = 2^(720*T+12) := by
    rw [hA4, pow_add]
    norm_num
    ring
  have hexp : C+720*T+12 ≤ (C+732)*T := by
    nlinarith [hCT]
  calc
    C*(3*2^(180*T)+3)^4 = C*(3*A+3)^4 := rfl
    _ ≤ C*(8*A)^4 :=
      Nat.mul_le_mul_left C hpow
    _ = C*(4096*A^4) := by ring
    _ = C*2^(720*T+12) := by rw [hnum]
    _ ≤ 2^C*2^(720*T+12) :=
      Nat.mul_le_mul_right _ hC
    _ = 2^(C+720*T+12) := by simp only [pow_add]; ring
    _ ≤ 2^((C+732)*T) :=
      pow_le_pow_right₀ (by decide : 1 ≤ (2:Nat)) hexp

theorem scheduled_clock_le_two_pow {n m : Nat} [NeZero n]
    (L Δ : Nat) (γ : Rat) (k : Nat)
    (hc : CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) L Δ γ) :
    let mX := sourceRows L (restorationDepth L)
      (coverDepth n m L Δ γ) k
    let mY := sourceCols L (restorationDepth L)
      (coverDepth n m L Δ γ) k
    let root := GeneratorFullSample.scheduledSampleCode
      n m L Δ γ k mX mY
    let B := Nat.clog 2 (CodeFullRunConsumer.scheduledM n m L Δ γ)
    let N := CodeFullRunConsumer.scheduledN n m L Δ γ k mX mY
    let R := Paper2.rejectionAttemptCap N
    CodeSamplerInterpreterPolynomial.actualClock root B R N ≤
      2^(exponentConstant*(k+1)*L) := by
  let mX := sourceRows L (restorationDepth L)
    (coverDepth n m L Δ γ) k
  let mY := sourceCols L (restorationDepth L)
    (coverDepth n m L Δ γ) k
  let root := GeneratorFullSample.scheduledSampleCode
    n m L Δ γ k mX mY
  let B := Nat.clog 2 (CodeFullRunConsumer.scheduledM n m L Δ γ)
  let N := CodeFullRunConsumer.scheduledN n m L Δ γ k mX mY
  let R := Paper2.rejectionAttemptCap N
  let T := (k+1)*L
  let A := 2^(180*T)
  have hL : 16 ≤ L := by
    rcases hc with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hL, _⟩
    exact hL
  have hT : 1 ≤ T := by
    have hp : 0 < (k+1)*L :=
      Nat.mul_pos (by omega) (by omega)
    dsimp [T]
    omega
  have hA : 1 ≤ A := by
    have hp : 0 < A := by
      dsimp [A]
      exact pow_pos (by decide : 0 < (2:Nat)) _
    omega
  obtain ⟨hS,hB,hR,hN⟩ :=
    CodeSamplerScheduledBounds.scheduled_parameters_le L Δ γ k hc
  have hS' : codeSize root ≤ A := by
    simpa [root,mX,mY,A,T,Nat.mul_assoc] using hS
  have hB' : B ≤ A := by
    simpa [B,A,T,Nat.mul_assoc] using hB
  have hR' : R ≤ A := by
    simpa [R,N,mX,mY,A,T,Nat.mul_assoc] using hR
  have hN' : N ≤ A := by
    simpa [N,mX,mY,A,T,Nat.mul_assoc] using hN
  have hpoly := CodeSamplerInterpreterPolynomial.actualClock_le
    root B R N A hS' hB' hR' hN' hA
  have hexp := polynomial_to_pow
    CodeSamplerInterpreterPolynomial.interpreterCoeff T hT
  dsimp only
  exact hpoly.trans (by
    simpa [A,T,exponentConstant,Nat.mul_assoc] using hexp)

#print axioms scheduled_clock_le_two_pow

end Paper2.CodeSamplerScheduledClock
