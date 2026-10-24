import CurrentAdditive.QuarticParameters
import Paper2.CodeSamplerScheduledClock

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

namespace Paper2.CurrentAdditive.QuarticInterpreterClock

open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.RecursiveSamplingExecution
open Paper2.SourceProfileParameters Paper2.SourceRecursiveNoSampling
open Paper2.ParameterizedCanonicalSource Paper2.CodeSamplerScheduledClock
open CurrentAdditive.RandomizedSchedule

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

theorem interpreter_clock27 {n m : Nat} [NeZero n]
    (L Δ : Nat) (γ : Rat) (k : Nat)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) L Δ γ) :
    let mX := sourceRows L (4 * RestorationWidthScheduleScratch.ell L)
      (q27 (V := Fin n) (E := Fin m) L γ Δ) k
    let mY := sourceCols L (4 * RestorationWidthScheduleScratch.ell L)
      (q27 (V := Fin n) (E := Fin m) L γ Δ) k
    let root := CodeFallbackSourceResult.sampleRoot n (LookupSeed.width L)
      (width L) (width L - 2) (outerWidth L) (width27 L)
      (Q27 (V := Fin n) (E := Fin m) L γ Δ) k mX mY
    let B := Nat.clog 2 (alphabetCap (width L) (width L - 2) (outerWidth L)
      (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ) n (LookupSeed.width L))
    let N := drawCap (width L) (width L - 2) (outerWidth L)
      (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ)
      (LookupSeed.width L) k mX mY
    let R := Paper2.rejectionAttemptCap N
    CodeSamplerInterpreterPolynomial.actualClock root B R N ≤
      2^(exponentConstant*(k+1)*L) := by
  let mX := sourceRows L (4 * RestorationWidthScheduleScratch.ell L)
    (q27 (V := Fin n) (E := Fin m) L γ Δ) k
  let mY := sourceCols L (4 * RestorationWidthScheduleScratch.ell L)
    (q27 (V := Fin n) (E := Fin m) L γ Δ) k
  let root := CodeFallbackSourceResult.sampleRoot n (LookupSeed.width L)
    (width L) (width L - 2) (outerWidth L) (width27 L)
    (Q27 (V := Fin n) (E := Fin m) L γ Δ) k mX mY
  let B := Nat.clog 2 (alphabetCap (width L) (width L - 2) (outerWidth L)
      (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ) n (LookupSeed.width L))
  let N := drawCap (width L) (width L - 2) (outerWidth L)
      (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ)
      (LookupSeed.width L) k mX mY
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
    QuarticParameters.parameters27 L Δ γ k hc
  rw [show 180 * (k + 1) * L = 180 * T by dsimp [T]; ring] at hS hB hR hN
  have hS' : codeSize root ≤ A := by
    exact hS
  have hB' : B ≤ A := by
    exact hB
  have hR' : R ≤ A := by
    exact hR
  have hN' : N ≤ A := by
    exact hN
  have hpoly := CodeSamplerInterpreterPolynomial.actualClock_le
    root B R N A hS' hB' hR' hN' hA
  have hexp := polynomial_to_pow
    CodeSamplerInterpreterPolynomial.interpreterCoeff T hT
  dsimp only
  exact hpoly.trans (by
    simpa [A,T,exponentConstant,Nat.mul_assoc] using hexp)


end Paper2.CurrentAdditive.QuarticInterpreterClock

#print axioms Paper2.CurrentAdditive.QuarticInterpreterClock.interpreter_clock27
