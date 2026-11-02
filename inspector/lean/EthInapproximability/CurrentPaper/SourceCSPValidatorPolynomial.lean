import EthInapproximability.CurrentPaper.SourceCSPGlobalTotalValidation

/-! A fixed-parameter cubic majorant for the actual total raw CSP validator clock. -/

namespace EthInapproximability.CurrentPaper.SourceCSPValidatorPolynomial

open SourceCSPGlobalTotalValidation

private def inputCoeff (a q : Nat) : Nat :=
  41 + a.bits.length + q.bits.length

private def dispatchCoeff (a q : Nat) : Nat :=
  let A := inputCoeff a q
  let G := SourceCSPInputGrowth.growthConstant a q
  A + 6 * G * A + 22

private def capCoeff (q : Nat) : Nat := 16 * q + 26

private def rowCoeff (a q : Nat) : Nat :=
  dispatchCoeff a q + capCoeff q + 4 * q + 26 +
    SourceCSPRowLoopTotalPolynomial.loopCoefficient q (a ^ q)

/-- A fixed-`a,q` coefficient constructed from the real instruction tables
and their actual displayed clock formulas. It is not an executable compiler. -/
noncomputable def majorantCoefficient (a q : Nat) : Nat :=
  let p := BitMachineStackGrowth.perStep
    (SourceCSPGlobalDecisionProgram.program a q)
  let p₀ := BitMachineStackGrowth.perStep
    (SourceCSPGuardOutputCombined.program a q)
  let D := dispatchCoeff a q
  let P := (1 + p₀) * D + 5
  let C := (1 + p) * (D + 2 + capCoeff q) + 4
  let R := (1 + p) * rowCoeff a q + 4
  1 + P + C + R

private theorem input_bound (a q L : Nat) :
    SourceCSPInputGuarded.inputBound a q L ≤
      inputCoeff a q * (L + 1) := by
  unfold SourceCSPInputGuarded.inputBound inputCoeff
  nlinarith

private theorem dispatch_bound (a q L : Nat) :
    SourceCSPGuardDispatchSequence.bound a q L ≤
      dispatchCoeff a q * (L + 1) ^ 2 := by
  let X := L + 1
  let A := inputCoeff a q
  let G := SourceCSPInputGrowth.growthConstant a q
  let I := SourceCSPInputGuarded.inputBound a q L
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hI : I ≤ A * X := input_bound a q L
  have hW : G * I ≤ G * (A * X) := Nat.mul_le_mul_left G hI
  have hmul := Nat.mul_le_mul_left (4 * X + 2) hW
  have hX2 : X ≤ X ^ 2 := by nlinarith
  have hA : A * X ≤ A * X ^ 2 := Nat.mul_le_mul_left A hX2
  have hGA := Nat.mul_le_mul_left (2 * G * A) hX2
  have hmulBound : (4 * X + 2) * (G * (A * X)) ≤
      6 * G * A * X ^ 2 := by
    nlinarith only [hGA]
  have hsmall : 2 * L + 5 * X + 15 ≤ 22 * X ^ 2 := by
    dsimp [X]
    nlinarith
  have heq : SourceCSPGuardDispatchSequence.bound a q L =
      I + (4 * X + 2) * (G * I) + 2 * L + 5 * X + 15 := by
    dsimp [SourceCSPGuardDispatchSequence.bound,
      SourceCSPGuardStatusSequence.bound,
      SourceCSPInputGuardedPoly.polyBound,
      SourceCSPInputGuarded.guardBound, X, I, G]
    ring
  rw [heq]
  calc
    _ ≤ A * X + (4 * X + 2) * (G * (A * X)) +
        2 * L + 5 * X + 15 := by omega
    _ ≤ A * X ^ 2 + 6 * G * A * X ^ 2 + 22 * X ^ 2 := by omega
    _ = dispatchCoeff a q * (L + 1) ^ 2 := by
      dsimp [dispatchCoeff, A, G, X]
      ring

private theorem prefix_bound (a q L : Nat) :
    SourceCSPGuardOutputCombined.polyBound a q L + 1 ≤
      ((1 + BitMachineStackGrowth.perStep
        (SourceCSPGuardOutputCombined.program a q)) *
        dispatchCoeff a q + 5) * (L + 1) ^ 2 := by
  have hD := dispatch_bound a q L
  have hmul := Nat.mul_le_mul_left
    (1 + BitMachineStackGrowth.perStep
      (SourceCSPGuardOutputCombined.program a q)) hD
  have hX : 1 ≤ (L + 1) ^ 2 := by
    have hp : 0 < (L + 1) ^ 2 := pow_pos (by omega) _
    omega
  dsimp [SourceCSPGuardOutputCombined.polyBound]
  nlinarith only [hmul, hX]

private theorem cap_bound (q L : Nat) :
    SourceCSPGlobalCapFromLiteral.capBound q L L ≤
      capCoeff q * (L + 1) ^ 2 := by
  let X := L + 1
  have heq : SourceCSPGlobalCapFromLiteral.capBound q L L =
      4 * q * L ^ 2 + (9 * q + 6) * L + 3 * q + 20 := by
    dsimp [SourceCSPGlobalCapFromLiteral.capBound]
    ring
  have hL2 : L ^ 2 ≤ X ^ 2 := by dsimp [X]; nlinarith
  have hL : L ≤ X ^ 2 := by dsimp [X]; nlinarith
  have h1 : 1 ≤ X ^ 2 := by dsimp [X]; nlinarith
  have hA := Nat.mul_le_mul_left (4 * q) hL2
  have hB := Nat.mul_le_mul_left (9 * q + 6) hL
  have hC := Nat.mul_le_mul_left (3 * q + 20) h1
  rw [heq]
  dsimp [capCoeff, X]
  nlinarith only [hA, hB, hC]

private theorem row_bound (a q L : Nat) :
    SourceCSPGlobalPositiveRows.physicalRowBound a q L ≤
      rowCoeff a q * (L + 1) ^ 3 := by
  have hD := dispatch_bound a q L
  have hC := cap_bound q L
  let X := L + 1
  have hX1 : 1 ≤ X := by dsimp [X]; omega
  have hX2 : X ^ 2 ≤ X ^ 3 := by
    calc
      X ^ 2 = X ^ 2 * 1 := by omega
      _ ≤ X ^ 2 * X := Nat.mul_le_mul_left _ hX1
      _ = X ^ 3 := by ring
  have hDX : SourceCSPGuardDispatchSequence.bound a q L ≤
      dispatchCoeff a q * X ^ 3 := hD.trans (Nat.mul_le_mul_left _ hX2)
  have hCX : SourceCSPGlobalCapFromLiteral.capBound q L L ≤
      capCoeff q * X ^ 3 := hC.trans (Nat.mul_le_mul_left _ hX2)
  have hX : L ≤ X ^ 3 := by dsimp [X]; nlinarith
  have h1 : 1 ≤ X ^ 3 := by dsimp [X]; nlinarith
  have hsmall : 6 * L + 4 * (q * L) + 20 ≤ (4 * q + 26) * X ^ 3 := by
    have hA := Nat.mul_le_mul_left (4 * q + 6) hX
    have hB := Nat.mul_le_mul_left 20 h1
    nlinarith only [hA, hB]
  have hformula : SourceCSPGlobalPositiveRows.physicalRowBound a q L =
      SourceCSPGuardDispatchSequence.bound a q L + 2 +
        SourceCSPGlobalCapFromLiteral.capBound q L L +
        (1 + 2 * L + 4 * (q * L) + 2 * L + 13) +
        (2 * L + 4) +
        SourceCSPRowLoopTotalPolynomial.loopCoefficient q (a ^ q) * X ^ 3 := rfl
  rw [hformula]
  have htarget : rowCoeff a q * X ^ 3 =
      dispatchCoeff a q * X ^ 3 + capCoeff q * X ^ 3 +
      (4 * q + 26) * X ^ 3 +
      SourceCSPRowLoopTotalPolynomial.loopCoefficient q (a ^ q) * X ^ 3 := by
    dsimp [rowCoeff]
    ring
  rw [htarget]
  omega

/-- The actual global validator halts within this explicit fixed-parameter
cubic majorant, for every raw length including zero. -/
theorem totalBound_le_cubic (a q L : Nat) :
    SourceCSPGlobalTotalValidation.totalBound a q L + 1 ≤
      majorantCoefficient a q * (L + 1) ^ 3 := by
  let X := L + 1
  let p := BitMachineStackGrowth.perStep
    (SourceCSPGlobalDecisionProgram.program a q)
  let p₀ := BitMachineStackGrowth.perStep
    (SourceCSPGuardOutputCombined.program a q)
  let D := dispatchCoeff a q
  let P := (1 + p₀) * D + 5
  let C := (1 + p) * (D + 2 + capCoeff q) + 4
  let R := (1 + p) * rowCoeff a q + 4
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hX2 : X ^ 2 ≤ X ^ 3 := by
    calc
      X ^ 2 = X ^ 2 * 1 := by omega
      _ ≤ X ^ 2 * X := Nat.mul_le_mul_left _ hX
      _ = X ^ 3 := by ring
  have hX3 : 1 ≤ X ^ 3 := by
    have hp : 0 < X ^ 3 := pow_pos (by omega) _
    omega
  have hD := dispatch_bound a q L
  have hP := prefix_bound a q L
  have hCap := cap_bound q L
  have hRow := row_bound a q L
  have hCapClock : (1 + p) *
      (SourceCSPGuardDispatchSequence.bound a q L + 2 +
        SourceCSPGlobalCapFromLiteral.capBound q L L) + 4 ≤ C * X ^ 3 := by
    have hD' : SourceCSPGuardDispatchSequence.bound a q L ≤ D * X ^ 3 :=
      hD.trans (Nat.mul_le_mul_left D hX2)
    have hC' : SourceCSPGlobalCapFromLiteral.capBound q L L ≤
        capCoeff q * X ^ 3 := hCap.trans (Nat.mul_le_mul_left _ hX2)
    have hsum : SourceCSPGuardDispatchSequence.bound a q L + 2 +
        SourceCSPGlobalCapFromLiteral.capBound q L L ≤
        (D + 2 + capCoeff q) * X ^ 3 := by
      nlinarith
    have hm := Nat.mul_le_mul_left (1 + p) hsum
    dsimp [C]
    nlinarith
  have hRowClock : (1 + p) *
      SourceCSPGlobalPositiveRows.physicalRowBound a q L + 4 ≤
      R * X ^ 3 := by
    have hm := Nat.mul_le_mul_left (1 + p) hRow
    change (1 + p) * SourceCSPGlobalPositiveRows.physicalRowBound a q L ≤
      (1 + p) * (rowCoeff a q * X ^ 3) at hm
    have heq : R * X ^ 3 =
        (1 + p) * (rowCoeff a q * X ^ 3) + 4 * X ^ 3 := by
      dsimp [R]
      ring
    rw [heq]
    omega
  have hPrefixClock : SourceCSPGuardOutputCombined.polyBound a q L + 1 ≤
      P * X ^ 3 := hP.trans (Nat.mul_le_mul_left P hX2)
  have htot : SourceCSPGlobalTotalValidation.totalBound a q L ≤
      max (P * X ^ 3) (max (C * X ^ 3) (R * X ^ 3)) := by
    unfold SourceCSPGlobalTotalValidation.totalBound
    exact max_le_max hPrefixClock (max_le_max hCapClock hRowClock)
  have hmax : max (P * X ^ 3) (max (C * X ^ 3) (R * X ^ 3)) ≤
      (P + C + R) * X ^ 3 := by
    apply max_le
    · nlinarith
    · apply max_le <;> nlinarith
  have hcoef : majorantCoefficient a q = 1 + P + C + R := rfl
  rw [hcoef]
  calc
    SourceCSPGlobalTotalValidation.totalBound a q L + 1 ≤
        (P + C + R) * X ^ 3 + 1 := Nat.add_le_add_right (htot.trans hmax) 1
    _ ≤ (P + C + R) * X ^ 3 + X ^ 3 :=
      Nat.add_le_add_left hX3 _
    _ = (1 + P + C + R) * (L + 1) ^ 3 := by
      dsimp [X]
      ring

end EthInapproximability.CurrentPaper.SourceCSPValidatorPolynomial
