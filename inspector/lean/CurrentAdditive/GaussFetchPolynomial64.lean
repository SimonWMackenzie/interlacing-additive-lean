import CurrentAdditive.GaussFourFetchEnvelope64

namespace CurrentAdditive.GaussFetchPolynomial64

noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

open GaussFourFetchEnvelope64

attribute [local irreducible] GaussFourFetchEnvelope64.pushes
  GaussFourFetchEnvelope64.stagePush GaussFourFetchEnvelope64.rawPushBound

def mass (B n : Nat) : Nat := B + (n+1)^3 + 1
@[irreducible] def growth : Nat := 1+300*pushes

theorem stageTime_le (B n : Nat) : stageTime B n ≤ 300*mass B n := by
  have hn : n ≤ (n+1)^3 := by
    nlinarith [Nat.zero_le (n*n*n),Nat.zero_le (n*n)]
  have hp : 1 ≤ (n+1)^3 := by
    nlinarith [Nat.zero_le (n*n*n),Nat.zero_le (n*n)]
  unfold stageTime mass
  nlinarith

theorem mass_next_le (B n : Nat) :
    mass (nextBankBound B n) n ≤ growth * mass B n := by
  have h := Nat.mul_le_mul_right pushes (stageTime_le B n)
  dsimp only [mass] at h
  unfold mass nextBankBound growth
  nlinarith

theorem mass_iterates (B n : Nat) :
    mass (nextBankBound B n) n ≤ growth * mass B n ∧
    mass (nextBankBound (nextBankBound B n) n) n ≤ growth^2 * mass B n ∧
    mass (nextBankBound (nextBankBound (nextBankBound B n) n) n) n ≤
      growth^3 * mass B n := by
  have h1 := mass_next_le B n
  have h2 := (mass_next_le (nextBankBound B n) n).trans
    (Nat.mul_le_mul_left growth h1)
  have h3 := (mass_next_le (nextBankBound (nextBankBound B n) n) n).trans
    (Nat.mul_le_mul_left growth h2)
  refine ⟨h1,?_,?_⟩
  · convert h2 using 1 <;> ring
  · convert h3 using 1 <;> ring

theorem mass_le_cube (B n : Nat) : mass B n ≤ 3*(B+n+1)^3 := by
  let N := B+n+1
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hB : B ≤ N := by dsimp [N]; omega
  have hpow := Nat.pow_le_pow_left (show n+1 ≤ N by dsimp [N]; omega) 3
  have hsq : N ≤ N^2 := by nlinarith
  have hcube : N ≤ N^3 := by
    have h := Nat.mul_le_mul_left N hsq
    nlinarith
  unfold mass
  change B+(n+1)^3+1 ≤ 3*N^3
  omega

def coefficient : Nat := 900*(1+growth+growth^2+growth^3)+9

/-- A cubic bound for the actual four-fetch recurrence. Its coefficient
depends only on the four fixed finite programs, never on a matrix or caller. -/
theorem fourBound_polynomial (B n : Nat) :
    fourBound B n ≤ coefficient * (B+n+1)^3 := by
  have h0 := stageTime_le B n
  obtain ⟨h1,h2,h3⟩ := mass_iterates B n
  have ht1 := (stageTime_le (nextBankBound B n) n).trans
    (Nat.mul_le_mul_left 300 h1)
  have ht2 := (stageTime_le (nextBankBound (nextBankBound B n) n) n).trans
    (Nat.mul_le_mul_left 300 h2)
  have ht3 := (stageTime_le
    (nextBankBound (nextBankBound (nextBankBound B n) n) n) n).trans
      (Nat.mul_le_mul_left 300 h3)
  have hm := mass_le_cube B n
  have hmass : 1 ≤ mass B n := by unfold mass; omega
  have hsum : fourBound B n ≤
      (300*(1+growth+growth^2+growth^3)+3)*mass B n := by
    unfold fourBound
    nlinarith
  have h := hsum.trans (Nat.mul_le_mul_left
    (300*(1+growth+growth^2+growth^3)+3) hm)
  calc
    fourBound B n ≤
        (300*(1+growth+growth^2+growth^3)+3) * (3*(B+n+1)^3) := h
    _ = coefficient*(B+n+1)^3 := by unfold coefficient; ring

#print axioms fourBound_polynomial

end
end CurrentAdditive.GaussFetchPolynomial64
