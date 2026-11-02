import EthInapproximability.CurrentPaper.ActualCountClock

/-! Source identification for the large actual-count atoms. The hypotheses are
the *literal raw Stage-4 carrier naming bounds*; these terms are factors of
those carriers, not independent bounds or clock assumptions. -/

namespace EthInapproximability.CurrentPaper.ActualCarrierBounds

open EntryClockPoly3

theorem iteration_raw_carrier_sizes (i : LI) :
    (Iteration.rawRowNumbering i.G i.c i.b i.y i.lv i.M).size =
      MatrixStage4Codes.rows (sI i) (LI' i)
        (GraphVectors.vertexCount i.V (sI i))
        (GraphVectors.auxiliaryCount (sI i)) (rxI i) ∧
    (Iteration.rawColumnNumbering i.G i.c i.b i.y i.lv i.M).size =
      MatrixStage4Codes.cols (aI i) (sI i) (qI i) (cyI i) := by
  constructor
  · change sI i * LI' i +
        (GraphVectors.vertexCount i.V (sI i) * rxI i +
          GraphVectors.auxiliaryCount (sI i) * rxI i) = _
    unfold MatrixStage4Codes.rows
    ring
  · rfl

theorem raw_factor_bounds (a s q L nv nb rx cy p : ℕ)
    (hs : 1 ≤ s) (hq : 1 ≤ q) (hcy : 1 ≤ cy)
    (hrow : Nat.clog 2 (MatrixStage4Codes.rows s L nv nb rx) ≤ p)
    (hcol : Nat.clog 2 (MatrixStage4Codes.cols a s q cy) ≤ p) :
    L ≤ 2 ^ p ∧
    MatrixStage4Digits.wordBase a s cy ≤ 2 ^ p ∧
    MatrixStage4Digits.binBase a s q cy ≤ 2 ^ p ∧
    MatrixStage4Digits.binBase a s q cy ^ s ≤ 2 ^ p ∧
    cy ^ (s + 1) ≤ 2 ^ p := by
  have hrows : MatrixStage4Codes.rows s L nv nb rx ≤ 2 ^ p :=
    (Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) _).trans
      (Nat.pow_le_pow_right (by decide) hrow)
  have hcols : MatrixStage4Codes.cols a s q cy ≤ 2 ^ p :=
    (Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) _).trans
      (Nat.pow_le_pow_right (by decide) hcol)
  let W := MatrixStage4Digits.wordBase a s cy
  let B := MatrixStage4Digits.binBase a s q cy
  have hW : 1 ≤ W := by
    dsimp [W, MatrixStage4Digits.wordBase]
    exact Nat.one_le_pow _ _ hcy
  have hB : B = q * W := by rfl
  have hB1 : 1 ≤ B := by
    rw [hB]
    exact Nat.mul_pos hq hW
  have hBs : 1 ≤ B ^ s := Nat.one_le_pow _ _ hB1
  have hCys : 1 ≤ cy ^ (s + 1) := Nat.one_le_pow _ _ hcy
  have hcol_eq : MatrixStage4Codes.cols a s q cy = cy ^ (s + 1) * B ^ s := rfl
  have hL : L ≤ MatrixStage4Codes.rows s L nv nb rx := by
    unfold MatrixStage4Codes.rows
    nlinarith
  have hBs_col : B ^ s ≤ MatrixStage4Codes.cols a s q cy := by
    rw [hcol_eq]
    nlinarith
  have hB_col : B ≤ MatrixStage4Codes.cols a s q cy := by
    have hBpow : B ≤ B ^ s := by
      calc B = B ^ 1 := (pow_one B).symm
        _ ≤ B ^ s := Nat.pow_le_pow_right hB1 hs
    exact hBpow.trans hBs_col
  have hW_col : W ≤ MatrixStage4Codes.cols a s q cy := by
    have hWB : W ≤ B := by rw [hB]; nlinarith
    exact hWB.trans hB_col
  have hCy_col : cy ^ (s + 1) ≤ MatrixStage4Codes.cols a s q cy := by
    rw [hcol_eq]
    nlinarith
  exact ⟨hL.trans hrows, hW_col.trans hcols, hB_col.trans hcols,
    hBs_col.trans hcols, hCy_col.trans hcols⟩

/-- At the literal `Iteration` step, the five large machine-count atoms are
bounded by the raw matrix's **actual** row/column naming lengths. The family
prime is bounded by its family size, using the positive order. -/
theorem level_large_counts_of_raw_carriers (i : LI) (p : ℕ)
    (hrow : Nat.clog 2
      (Iteration.rawRowNumbering i.G i.c i.b i.y i.lv i.M).size ≤ p)
    (hcol : Nat.clog 2
      (Iteration.rawColumnNumbering i.G i.c i.b i.y i.lv i.M).size ≤ p) :
    LI' i ≤ 2 ^ p ∧ pI i ≤ 2 ^ p ∧
    MatrixStage4Digits.wordBase (aI i) (sI i) (cyI i) ≤ 2 ^ p ∧
    MatrixStage4Digits.binBase (aI i) (sI i) (qI i) (cyI i) ≤ 2 ^ p ∧
    MatrixStage4Digits.binBase (aI i) (sI i) (qI i) (cyI i) ^ sI i ≤ 2 ^ p ∧
    cyI i ^ (sI i + 1) ≤ 2 ^ p := by
  have hs : 1 ≤ sI i := Parameters.bins_pos (PL i)
  have hq : 1 ≤ qI i := EthInapproximability.ParameterizedNP.GuardedSourceSlab.q2_pos i.G (sI i)
  have hcy : 1 ≤ cyI i := i.M.columns_pos
  have hrow' : Nat.clog 2
      (MatrixStage4Codes.rows (sI i) (LI' i)
        (GraphVectors.vertexCount i.V (sI i))
        (GraphVectors.auxiliaryCount (sI i)) (rxI i)) ≤ p := by
    rw [← (iteration_raw_carrier_sizes i).1]
    exact hrow
  have hcol' : Nat.clog 2
      (MatrixStage4Codes.cols (aI i) (sI i) (qI i) (cyI i)) ≤ p := by
    rw [← (iteration_raw_carrier_sizes i).2]
    exact hcol
  obtain ⟨hL, hW, hB, hBs, hCy⟩ := raw_factor_bounds
    (aI i) (sI i) (qI i) (LI' i)
    (GraphVectors.vertexCount i.V (sI i))
    (GraphVectors.auxiliaryCount (sI i)) (rxI i) (cyI i) p
    hs hq hcy hrow' hcol'
  have ht : 1 ≤ tI i := by
    have h := (EffectiveIteration.parameter_size_bounds (PL i)).1
    change 128 ≤ tI i at h
    omega
  have hp2 : 2 ≤ pI i :=
    EthInapproximability.ParameterizedNP.BalancedFamilyBuilder.two_le_balPrime _ _ _
  have hpL : pI i ≤ LI' i := by
    change pI i ≤ pI i ^ tI i
    calc
      pI i = pI i ^ 1 := (pow_one _).symm
      _ ≤ pI i ^ tI i := Nat.pow_le_pow_right (by omega : 1 ≤ pI i) ht
  exact ⟨hL, hpL.trans hL, hW, hB, hBs, hCy⟩

#print axioms iteration_raw_carrier_sizes
#print axioms raw_factor_bounds
#print axioms level_large_counts_of_raw_carriers

end EthInapproximability.CurrentPaper.ActualCarrierBounds
