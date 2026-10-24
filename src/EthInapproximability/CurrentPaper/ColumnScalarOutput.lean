import EthInapproximability.CurrentPaper.ColumnScalarJoin
import EthInapproximability.CurrentPaper.MatrixWeightedEntrySemantic

/-! Exact output bank and fixed polynomial bound for the physical scalar program. -/

namespace EthInapproximability.CurrentPaper.ColumnScalarOutput

open Turing
open BitMachineEncoding
open ColumnScalarPrefix

def finalBank (a s q L rx cy : ℕ) : Stack → List Bool :=
  ColumnScalarWidth.outputBank
    (ColumnScalarWidth.sourceBank a s q L rx cy) a s q cy

theorem six_inputs_preserved (a s q L rx cy : ℕ) :
    finalBank a s q L rx cy 0 = List.replicate a true ∧
    finalBank a s q L rx cy 1 = List.replicate s true ∧
    finalBank a s q L rx cy 2 = List.replicate q true ∧
    finalBank a s q L rx cy 3 = List.replicate L true ∧
    finalBank a s q L rx cy 4 = List.replicate rx true ∧
    finalBank a s q L rx cy 5 = List.replicate cy true := by
  simp [finalBank, ColumnScalarWidth.outputBank, ColumnScalarWidth.sourceBank,
    ColumnScalarBinPower.outputBank, ColumnScalarBinPower.sourceBank,
    ColumnScalarTailPower.outputBank, ColumnScalarTailPower.sourceBank,
    ColumnScalarBinBase.outputBank, ColumnScalarBinBase.sourceBank,
    ColumnScalarWordBase.outputBank, ColumnScalarWordBase.sourceBank,
    ColumnScalarPrefix.lengthBank, ColumnScalarPrefix.qoneBank,
    ColumnScalarPrefix.inputBank]

theorem exact_outputs (a s q L rx cy : ℕ) :
    finalBank a s q L rx cy 8 =
      List.replicate (MatrixStage4Digits.wordBase a s cy) true ∧
    finalBank a s q L rx cy 9 =
      List.replicate (MatrixStage4Digits.binBase a s q cy) true ∧
    finalBank a s q L rx cy 12 =
      List.replicate (MatrixStage4Codes.cols a s q cy) true := by
  simp [finalBank, ColumnScalarWidth.outputBank, ColumnScalarWidth.sourceBank,
    ColumnScalarBinPower.outputBank, ColumnScalarBinPower.sourceBank,
    ColumnScalarTailPower.outputBank, ColumnScalarTailPower.sourceBank,
    ColumnScalarBinBase.outputBank, ColumnScalarBinBase.sourceBank,
    ColumnScalarWordBase.outputBank]

theorem scratch_cleared (a s q L rx cy : ℕ) (j : Stack)
    (hj : 13 ≤ j.val) : finalBank a s q L rx cy j = [] := by
  fin_cases j <;> simp_all [finalBank, ColumnScalarWidth.outputBank, ColumnScalarWidth.sourceBank,
    ColumnScalarBinPower.outputBank, ColumnScalarBinPower.sourceBank,
    ColumnScalarTailPower.outputBank, ColumnScalarTailPower.sourceBank,
    ColumnScalarBinBase.outputBank, ColumnScalarBinBase.sourceBank,
    ColumnScalarWordBase.outputBank, ColumnScalarWordBase.sourceBank,
    ColumnScalarPrefix.lengthBank, ColumnScalarPrefix.qoneBank,
    ColumnScalarPrefix.inputBank]

/-- Fixed multivariate polynomial in the unary input lengths and the
physically produced intermediate/output word lengths. No recursive machine
clock is left in this expression. -/
def polynomialCost (a s q cy : ℕ) : ℕ :=
  let f := Construction.firstLength a s
  let w := MatrixStage4Digits.wordBase a s cy
  let b := MatrixStage4Digits.binBase a s q cy
  let v := cy^(s+1)
  let z := b^s
  (4*2^a+5*a+10) + (2*Construction.qOne a+2*s+7) +
  (2*f+5+(f+1)*(3*(w+1)*cy+5*(w+1)+7)) +
  (2*q*w+4*q+4) +
  (2*s+6+(s+2)*(3*(v+1)*cy+5*(v+1)+7)) +
  (2*s+5+(s+1)*(3*(z+1)*b+5*(z+1)+7)) +
  (2*v*z+4*v+4) + 6

theorem cost_le_polynomial (a s q cy : ℕ) :
    ColumnScalarJoin.cost a s q cy ≤ polynomialCost a s q cy := by
  have h₁ := MatrixWeightedPower.powerBound_polynomial cy
    (Construction.firstLength a s)
  have h₂ := MatrixWeightedPower.powerBound_polynomial cy (s+1)
  rw [show s + 1 + 1 = s + 2 by omega] at h₂
  have h₃ := MatrixWeightedPower.powerBound_polynomial
    (MatrixStage4Digits.binBase a s q cy) s
  dsimp [ColumnScalarJoin.cost, ColumnScalarJoin.cost₅,
    ColumnScalarJoin.cost₄, ColumnScalarJoin.cost₃,
    ColumnScalarJoin.cost₂, ColumnScalarJoin.cost₁,
    ColumnScalarJoin.c₀, ColumnScalarJoin.c₁,
    ColumnScalarJoin.c₂, ColumnScalarJoin.c₃,
    ColumnScalarJoin.c₄, ColumnScalarJoin.c₅,
    ColumnScalarJoin.c₆, polynomialCost,
    MatrixAddressMachine.exactTime] at *
  unfold MatrixStage4Digits.wordBase at *
  omega

theorem physical_run_polynomial (a s q L rx cy : ℕ) :
    ∃ t ≤ polynomialCost a s q cy,
      ((advance ColumnScalarJoin.program)^[t])
        ⟨some ColumnScalarJoin.start, ColumnScalarJoin.control,
          inputBank a s q L rx cy⟩ =
        ⟨none, ColumnScalarJoin.control, finalBank a s q L rx cy⟩ := by
  obtain ⟨t,ht,hr⟩ := ColumnScalarJoin.run a s q L rx cy
  exact ⟨t, ht.trans (cost_le_polynomial a s q cy),
    by simpa only [finalBank] using hr⟩

theorem exact_input_projection {rx cy : ℕ}
    (R : Fin rx → Fin cy → Bool) (a s q L nv nb : ℕ)
    (hs : 0 < s) (family : Construction.SecondFamily a q L (Fin rx))
    (order : Construction.ItemOrder nv nb)
    (vectors : Fin (nv+nb) → Fin q → Bool)
    (cap : ∀ α, (Construction.activeItems vectors α).card ≤ s) :
    let d := MatrixWeightedEntrySemantic.actualInput
      R a s q L nv nb hs family order vectors cap
    finalBank a s q L rx cy 8 = List.replicate d.wordBase true ∧
    finalBank a s q L rx cy 9 = List.replicate d.binBase true ∧
    finalBank a s q L rx cy 12 = List.replicate d.rawWidth true := by
  simpa [MatrixWeightedEntrySemantic.actualInput] using
    exact_outputs a s q L rx cy

#print axioms six_inputs_preserved
#print axioms exact_outputs
#print axioms scratch_cleared
#print axioms cost_le_polynomial
#print axioms physical_run_polynomial
#print axioms exact_input_projection

end EthInapproximability.CurrentPaper.ColumnScalarOutput
