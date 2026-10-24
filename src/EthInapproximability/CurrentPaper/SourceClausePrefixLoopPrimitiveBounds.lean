import EthInapproximability.CurrentPaper.SourceClausePrefixLoopCost
import EthInapproximability.CurrentPaper.ClockStepSemantics
import EthInapproximability.CurrentPaper.SourceClausePrimitivePolynomial

namespace EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixLoopPolyProbe

open PrefixLoopCost
open scoped Classical

theorem unitPre_le_poly (n v w ell : ℕ) :
    unitPre n v w ell ≤
      100 * (UnaryBinaryEncoding.coefficient + 1) *
        (n + v + w + ell + 2) ^ 4 := by
  have hb (x : ℕ) : x.bits.length ≤ x :=
    ClockStepSemantics.bits_length_le x
  let M := n + v + w + ell + 2
  have hm : 2 ≤ M := by omega
  have hn : n ≤ M := by omega
  have hv : v ≤ M := by omega
  have hw : w ≤ M := by omega
  have he : ell ≤ M := by omega
  have hsize (i : Fin 3) : PrefixUnitClean.constantSize w ell i ≤ M := by
    fin_cases i <;> simp [PrefixUnitClean.constantSize] <;> omega
  have hc := SourceClauseCallbackPrimitivePolynomial.costPrefix_le
    (PrefixUnitClean.constantSize w ell) M hsize 3
  have hvw : v * w ≤ M ^ 2 := by
    have h := Nat.mul_le_mul hv hw
    simpa [pow_two] using h
  have hp : v * w + (2 * n + ell) + 1 ≤ 5 * M ^ 2 := by
    nlinarith [sq_nonneg (M : ℤ)]
  have hbits : (v * w + (2 * n + ell)).bits.length ≤ 5 * M ^ 2 := by
    have h := hb (v * w + (2 * n + ell))
    omega
  have hsq : (v * w + (2 * n + ell) + 1) ^ 2 ≤ 25 * M ^ 4 := by
    have h := Nat.mul_le_mul hp hp
    nlinarith [h]
  have hcoeff := Nat.mul_le_mul_left UnaryBinaryEncoding.coefficient hsq
  have hm2 : M ≤ M ^ 2 := by nlinarith
  have hm24 : M ^ 2 ≤ M ^ 4 := by
    have h := Nat.mul_le_mul hm2 hm2
    nlinarith [h]
  have hm14 : M ≤ M ^ 4 := hm2.trans hm24
  have hM4 : 1 ≤ M ^ 4 := by omega
  change unitPre n v w ell ≤
    100 * (UnaryBinaryEncoding.coefficient + 1) * M ^ 4
  simp only [unitPre, PrefixUnitRun.cost,
    PrefixUnitAddress.cost, MatrixAddressMachine.exactTime]
  nlinarith [Nat.zero_le (UnaryBinaryEncoding.coefficient * M ^ 4)]

theorem gatePre_le_poly {n : ℕ} (v : Fin n) (s : Fin 2) (w : ℕ) :
    PrefixGateOperands.preparationCost s.val w (List.replicate v.val true) +
      SourceClauseRowGate.cost v.val 2 s.val n s.val v.val w true + 1 ≤
      10000 * (UnaryBinaryEncoding.coefficient + 1) *
        (n + v.val + w + 3) ^ 4 := by
  let M := n + v.val + w + 3
  have hm : 3 ≤ M := by omega
  have hn : n ≤ M := by omega
  have hv : v.val ≤ M := by omega
  have hw : w ≤ M := by omega
  have hs : s.val ≤ 1 := by omega
  have hsize (i : Fin 5) : PrefixGateOperands.constantSize s.val w i ≤ M := by
    fin_cases i <;> simp [PrefixGateOperands.constantSize] <;> omega
  have hc := SourceClauseCallbackPrimitivePolynomial.costPrefix_le
    (PrefixGateOperands.constantSize s.val w) M hsize 5
  have hvw : v.val * w ≤ M ^ 2 := by
    have h := Nat.mul_le_mul hv hw
    simpa [pow_two] using h
  have hp1 : v.val * 2 + s.val + 1 ≤ 3 * M := by omega
  have hp2 : v.val * w + (n * 2 + s.val) + 1 ≤ 4 * M ^ 2 := by
    nlinarith
  have hsq1 : (v.val * 2 + s.val + 1) ^ 2 ≤ 9 * M ^ 2 := by
    have h := Nat.mul_le_mul hp1 hp1
    nlinarith [h]
  have hsq2 : (v.val * w + (n * 2 + s.val) + 1) ^ 2 ≤ 16 * M ^ 4 := by
    have h := Nat.mul_le_mul hp2 hp2
    nlinarith [h]
  have hcoeff1 := Nat.mul_le_mul_left UnaryBinaryEncoding.coefficient hsq1
  have hcoeff2 := Nat.mul_le_mul_left UnaryBinaryEncoding.coefficient hsq2
  have hbits1 : (v.val * 2 + s.val).bits.length ≤ 3 * M := by
    have h := ClockStepSemantics.bits_length_le (v.val * 2 + s.val)
    omega
  have hbits2 : (v.val * w + (n * 2 + s.val)).bits.length ≤ 4 * M ^ 2 := by
    have h := ClockStepSemantics.bits_length_le (v.val * w + (n * 2 + s.val))
    omega
  have hbits3 : (v.val * w + (n * 2 + s.val) + 1).bits.length ≤
      4 * M ^ 2 := by
    have h := ClockStepSemantics.bits_length_le
      (v.val * w + (n * 2 + s.val) + 1)
    omega
  have hm2 : M ≤ M ^ 2 := by nlinarith
  have hm24 : M ^ 2 ≤ M ^ 4 := by
    have h := Nat.mul_le_mul hm2 hm2
    nlinarith [h]
  have hm14 : M ≤ M ^ 4 := hm2.trans hm24
  have hM4 : 1 ≤ M ^ 4 := by omega
  change _ ≤ 10000 * (UnaryBinaryEncoding.coefficient + 1) * M ^ 4
  simp only [PrefixGateOperands.preparationCost,
    SourceClauseRowGate.cost, SourceClauseGateSlotAddress.cost,
    SourceLiteralWriter.emitTime, SourceLiteralWriter.words,
    SourceClauseGatePrepare.firstClause,
    SourceClauseGatePrepare.secondClause,
    SourceClauseGatePrepare.thirdClause,
    MatrixAddressMachine.exactTime,
    SourceClauseEncoding.positive, SourceClauseEncoding.negative,
    SourceClauseEncoding.negate, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
    Matrix.cons_val_zero, Matrix.cons_val_succ,
    List.length_replicate]
  nlinarith [Nat.zero_le (UnaryBinaryEncoding.coefficient * M ^ 4)]

noncomputable def preBound (n v q : ℕ) : ℕ :=
  10000 * (UnaryBinaryEncoding.coefficient + 1) *
    (n + v + SourceBooleanEncoding.width 2 q + 5) ^ 4

noncomputable def stepBound (q : ℕ) : ℕ :=
  let w := SourceBooleanEncoding.width 2 q + 1
  BitMachineStackGrowth.perStep (PrefixSharedUnitPair.program w 0 false) +
  BitMachineStackGrowth.perStep (PrefixSharedUnitPair.program w 2 true) +
  BitMachineStackGrowth.perStep (PrefixGateCycle.pairProgram 0 w) +
  BitMachineStackGrowth.perStep (PrefixGateCycle.pairProgram 1 w)

def wordBound (n q : ℕ) : ℕ :=
  8 * (6 * variableBound n q + 6)

def bankBound (n v q : ℕ) (saved output count : List Bool) : ℕ :=
  n + v + saved.length + output.length + count.length + wordBound n q + 8

noncomputable def phaseBound (n v q : ℕ)
    (saved output count : List Bool) : ℕ :=
  preBound n v q +
    workCount * (bankBound n v q saved output count +
      stepBound q * preBound n v q) + workCount + 3

theorem unitPre_le_preBound (n v q ell : ℕ) (hell : ell ≤ 2) :
    unitPre n v (SourceBooleanEncoding.width 2 q + 1) ell ≤
      preBound n v q := by
  let w := SourceBooleanEncoding.width 2 q + 1
  let C := UnaryBinaryEncoding.coefficient + 1
  have h := unitPre_le_poly n v w ell
  have hp : (n + v + w + ell + 2) ^ 4 ≤ (n + v + w + 4) ^ 4 :=
    pow_le_pow_left₀ (by omega) (by omega) 4
  have hm := Nat.mul_le_mul_left (100 * C) hp
  change unitPre n v w ell ≤ 100 * C * (n + v + w + ell + 2) ^ 4 at h
  have hscale : 100 * C * (n + v + w + 4) ^ 4 ≤
      10000 * C * (n + v + w + 4) ^ 4 := by
    nlinarith [Nat.zero_le (C * (n + v + w + 4) ^ 4)]
  change unitPre n v w ell ≤ 10000 * C * (n + v + w + 4) ^ 4
  exact h.trans (hm.trans hscale)

theorem gatePre_le_preBound {n q : ℕ} (v : Fin n) (s : Fin 2) :
    gatePre (q := q) v s ≤ preBound n v.val q := by
  let w := SourceBooleanEncoding.width 2 q + 1
  have h := gatePre_le_poly v s w
  have hp : (n + v.val + w + 3) ^ 4 ≤ (n + v.val + w + 4) ^ 4 :=
    pow_le_pow_left₀ (by omega) (by omega) 4
  have hm := Nat.mul_le_mul_left
    (10000 * (UnaryBinaryEncoding.coefficient + 1)) hp
  simpa only [gatePre, preBound, w] using le_trans h hm

theorem phase_majorize (n v q : ℕ)
    (saved output count : List Bool)
    (pre time H : ℕ) (hpre : pre ≤ preBound n v q)
    (htime : time ≤ stepBound q)
    (hH : H ≤ bankBound n v q saved output count) :
    pre + workCount * (H + time * pre) + workCount + 3 ≤
      phaseBound n v q saved output count := by
  have hp := Nat.mul_le_mul htime hpre
  have hs : H + time * pre ≤
      bankBound n v q saved output count + stepBound q * preBound n v q := by
    omega
  have hm := Nat.mul_le_mul_left workCount hs
  unfold phaseBound
  omega

theorem callback_cost_le_phase {n q : ℕ} (v : Fin n)
    (saved output count : List Bool) :
    PrefixFullCallback.cost (q := q) v saved output count ≤
      4 * phaseBound n v.val q saved output count + 3 := by
  let w := SourceBooleanEncoding.width 2 q + 1
  let S₁ := PrefixFirstTwoCycles.firstSaved n v.val w saved
  let S₂ := PrefixFirstTwoCycles.secondSaved (q := q) v saved
  let S₃ := PrefixThreeCycles.thirdSaved (q := q) v saved
  let C₁ := true :: count
  let C₄ := List.replicate 4 true ++ count
  let C₇ := List.replicate 7 true ++ count
  let B := phaseBound n v.val q saved output count
  obtain ⟨hs₁, hs₂, hs₃⟩ := partialSaved_length_le (q := q) v saved
  have hH₀ : n + v.val + saved.length + output.length + count.length ≤
      bankBound n v.val q saved output count := by
    unfold bankBound
    omega
  have hH₁ : n + v.val + S₁.length + output.length + C₁.length ≤
      bankBound n v.val q saved output count := by
    dsimp only [S₁, C₁, w]
    simp only [List.length_cons]
    unfold bankBound wordBound
    omega
  have hH₄ : n + v.val + S₂.length + output.length + C₄.length ≤
      bankBound n v.val q saved output count := by
    dsimp only [S₂, C₄]
    simp only [List.length_append, List.length_replicate]
    unfold bankBound wordBound
    omega
  have hH₇ : n + v.val + S₃.length + output.length + C₇.length ≤
      bankBound n v.val q saved output count := by
    dsimp only [S₃, C₇]
    simp only [List.length_append, List.length_replicate]
    unfold bankBound wordBound
    omega
  have hstepU₀ : BitMachineStackGrowth.perStep
      (PrefixSharedUnitPair.program w 0 false) ≤ stepBound q := by
    dsimp only [stepBound, w]
    omega
  have hstepU₂ : BitMachineStackGrowth.perStep
      (PrefixSharedUnitPair.program w 2 true) ≤ stepBound q := by
    dsimp only [stepBound, w]
    omega
  have hstepG₀ : BitMachineStackGrowth.perStep
      (PrefixGateCycle.pairProgram 0 w) ≤ stepBound q := by
    dsimp only [stepBound, w]
    omega
  have hstepG₁ : BitMachineStackGrowth.perStep
      (PrefixGateCycle.pairProgram 1 w) ≤ stepBound q := by
    dsimp only [stepBound, w]
    omega
  have hu₀ : PrefixFirstTwoCycles.unitCost n v.val w saved output count ≤ B := by
    have h := unitCost_le n v.val w saved output count
    have hpre := unitPre_le_preBound n v.val q 0 (by omega)
    have hm := phase_majorize n v.val q saved output count
      (unitPre n v.val w 0)
      (BitMachineStackGrowth.perStep (PrefixSharedUnitPair.program w 0 false))
      (n + v.val + saved.length + output.length + count.length)
      hpre hstepU₀ hH₀
    exact h.trans hm
  have hg₀ : PrefixFirstTwoCycles.gateCost (q := q) v (0 : Fin 2)
      S₁ output C₁ ≤ B := by
    have h := gateCost_le (q := q) v (0 : Fin 2) S₁ output C₁
    have hpre := gatePre_le_preBound (q := q) v (0 : Fin 2)
    have hm := phase_majorize n v.val q saved output count
      (gatePre (q := q) v (0 : Fin 2))
      (BitMachineStackGrowth.perStep (PrefixGateCycle.pairProgram 0 w))
      (n + v.val + S₁.length + output.length + C₁.length)
      hpre hstepG₀ hH₁
    exact h.trans hm
  have hg₁ : PrefixFirstTwoCycles.gateCost (q := q) v (1 : Fin 2)
      S₂ output C₄ ≤ B := by
    have h := gateCost_le (q := q) v (1 : Fin 2) S₂ output C₄
    have hpre := gatePre_le_preBound (q := q) v (1 : Fin 2)
    have hm := phase_majorize n v.val q saved output count
      (gatePre (q := q) v (1 : Fin 2))
      (BitMachineStackGrowth.perStep (PrefixGateCycle.pairProgram 1 w))
      (n + v.val + S₂.length + output.length + C₄.length)
      hpre hstepG₁ hH₄
    exact h.trans hm
  have hu₂ : PrefixFullCallback.terminalCost n v.val w S₃ output C₇ ≤ B := by
    have h := terminalCost_le n v.val w S₃ output C₇
    have hpre := unitPre_le_preBound n v.val q 2 (by omega)
    have hm := phase_majorize n v.val q saved output count
      (unitPre n v.val w 2)
      (BitMachineStackGrowth.perStep (PrefixSharedUnitPair.program w 2 true))
      (n + v.val + S₃.length + output.length + C₇.length)
      hpre hstepU₂ hH₇
    exact h.trans hm
  unfold PrefixFullCallback.cost PrefixThreeCycles.cost
  dsimp only [w, S₁, S₂, S₃, C₁, C₄, C₇, B] at hu₀ hg₀ hg₁ hu₂ ⊢
  omega

end EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixLoopPolyProbe
