import CurrentAdditive.CanonicalDimensionsMultiply

/-! A fixed physical unary program computes the number of ordered field
seed pairs `(2^d)^2` directly as `4^d`, preserving the public degree word. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalFieldSquare

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

def copyPlace : Fin 3 ↪ Fin 9 := ⟨![0, 1, 4], by decide⟩
def powerPlace : MatrixWeightedPower.Stack ↪ Fin 9 :=
  ⟨Sum.elim (![3, 2, 5, 6, 7, 8] : Fin 6 → Fin 9)
    (![1] : Fin 1 → Fin 9), by decide⟩

def powerProgram := MatrixStage4ScalarPreparationOps.weightedPowerProgram powerPlace
def accPower := BitMachineRawSequence.program
  (SourceClauseFixedUnary.program (3 : Fin 9) 1) powerProgram
  (Sum.inr MatrixWeightedPower.Admin.test) () (false, false)
def baseAccPower := BitMachineRawSequence.program
  (SourceClauseFixedUnary.program (2 : Fin 9) 4) accPower
  (BitMachineRawSequence.leftLabel (0 : SourceClauseFixedUnary.Label 1))
  () ((), (false, false))
def program := BitMachineRawSequence.program
  (MatrixStage4ScalarPreparationOps.copyProgram copyPlace) baseAccPower
  (BitMachineRawSequence.leftLabel (0 : SourceClauseFixedUnary.Label 4))
  (none : Option Bool) ((), ((), (false, false)))

def initial (d : ℕ) : Fin 9 → List Bool :=
  fun k => if k = 0 then List.replicate d true else []

theorem four_pow_eq_field_square (d : ℕ) : 4 ^ d = (2 ^ d) ^ 2 := by
  calc
    4 ^ d = (2 * 2) ^ d := by norm_num
    _ = 2 ^ d * 2 ^ d := by rw [mul_pow]
    _ = (2 ^ d) ^ 2 := by ring

theorem physical_field_square (d : ℕ) :
    ∃ steps ≤ (2*d+2) + 5 + 2 +
        MatrixWeightedPower.powerBound 4 d + 3,
      ((advance program)^[steps])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
          (none, ((), ((), (false, false)))), initial d⟩ :
          TM2.Cfg (fun _ : Fin 9 => Bool) _ _) =
        ⟨none, (none, ((), ((), (false, false)))),
          Function.update (Function.update (initial d) 2
            (List.replicate 4 true)) 3
            (List.replicate ((2 ^ d) ^ 2) true)⟩ := by
  let S := initial d
  let S1 := Function.update S 1 (List.replicate d true)
  let S2 := Function.update S1 2 (List.replicate 4 true)
  let S3 := Function.update S2 3 [true]
  let S4 := Function.update (Function.update S3 3 (List.replicate (4^d) true)) 1 []
  have hcopy := MatrixStage4ScalarPreparationOps.copy_run copyPlace S (by rfl)
  have hcopy' : ((advance (MatrixStage4ScalarPreparationOps.copyProgram copyPlace))^[2*d+2])
      (⟨some BitMachineCopy.Label.scan, none, S⟩ :
        TM2.Cfg (fun _ : Fin 9 => Bool) _ _) = ⟨none, none, S1⟩ := by
    simpa [copyPlace, S1, S, initial] using hcopy
  have hbase := SourceClauseFixedUnary.run (2 : Fin 9) S1 4
    (by simp [S1, S, initial])
  have hbase' : ((advance (SourceClauseFixedUnary.program (2 : Fin 9) 4))^[5])
      (⟨some (0 : SourceClauseFixedUnary.Label 4), (), S1⟩ :
        TM2.Cfg (fun _ : Fin 9 => Bool) _ _) = ⟨none, (), S2⟩ := by
    simpa [S2] using hbase
  have hacc := SourceClauseFixedUnary.run (3 : Fin 9) S2 1
    (by simp [S2, S1, S, initial])
  have hacc' : ((advance (SourceClauseFixedUnary.program (3 : Fin 9) 1))^[2])
      (⟨some (0 : SourceClauseFixedUnary.Label 1), (), S2⟩ :
        TM2.Cfg (fun _ : Fin 9 => Bool) _ _) = ⟨none, (), S3⟩ := by
    simpa [S3] using hacc
  obtain ⟨u, hu, hpower⟩ := MatrixStage4ScalarPreparationOps.weighted_power_run
    powerPlace S3 4 d
    (by simp [powerPlace, S3, S2, S1, S, initial])
    (by simp [powerPlace, S3, S2, S1, S, initial])
    (by simp [powerPlace, S3, S2, S1, S, initial])
    (by simp [powerPlace, S3, S2, S1, S, initial])
    (by simp [powerPlace, S3, S2, S1, S, initial])
    (by simp [powerPlace, S3, S2, S1, S, initial])
    (by simp [powerPlace, S3, S2, S1, S, initial])
  have hpower' : ((advance powerProgram)^[u])
      (⟨some (.inr .test), (false, false), S3⟩ :
        TM2.Cfg (fun _ : Fin 9 => Bool) _ _) =
      ⟨none, (false, false), S4⟩ := by
    simpa [powerProgram, powerPlace, S4] using hpower
  obtain ⟨u3, hu3, hr3⟩ := BitMachineRawSequence.runs
    (SourceClauseFixedUnary.program (3 : Fin 9) 1) powerProgram
    (0 : SourceClauseFixedUnary.Label 1) (Sum.inr MatrixWeightedPower.Admin.test)
    () () (false, false) (false, false) S2 S3 S4 2 u hacc' hpower'
  obtain ⟨u2, hu2, hr2⟩ := BitMachineRawSequence.runs
    (SourceClauseFixedUnary.program (2 : Fin 9) 4) accPower
    (0 : SourceClauseFixedUnary.Label 4)
    (BitMachineRawSequence.leftLabel (0 : SourceClauseFixedUnary.Label 1))
    () () ((), (false, false)) ((), (false, false)) S1 S2 S4 5 u3 hbase' hr3
  obtain ⟨steps, hsteps, hrun⟩ := BitMachineRawSequence.runs
    (MatrixStage4ScalarPreparationOps.copyProgram copyPlace) baseAccPower
    BitMachineCopy.Label.scan
    (BitMachineRawSequence.leftLabel (0 : SourceClauseFixedUnary.Label 4))
    none none ((), ((), (false, false))) ((), ((), (false, false)))
    S S1 S4 (2*d+2) u2 hcopy' hr2
  refine ⟨steps, by omega, ?_⟩
  have hbank : S4 = Function.update (Function.update S 2
      (List.replicate 4 true)) 3
      (List.replicate ((2^d)^2) true) := by
    funext k
    fin_cases k <;> simp [S4, S3, S2, S1, S, initial, four_pow_eq_field_square]
  rw [hbank] at hrun
  simpa [program, S] using hrun

#print axioms physical_field_square

end CurrentAdditive.FiniteFieldConstructor.CanonicalFieldSquare
