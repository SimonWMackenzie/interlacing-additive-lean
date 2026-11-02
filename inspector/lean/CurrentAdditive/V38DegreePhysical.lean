import CurrentAdditive.CanonicalWidthMultiply

/-! Literal unary public-degree preparation.  The varying input is only b.
Two fixed pushes install 5 and 14t, then the inherited six-stack preserving
multiply-add writes b*5+14t. No source promise or field witness is inspected. -/

noncomputable section
namespace CurrentAdditive.V38DegreePhysical

open Turing EthInapproximability.CurrentPaper
open BitMachineEncoding MatrixStage4ScalarPreparationOps

def mulPlace : Fin 6 ↪ Fin 6 := ⟨![0, 1, 2, 4, 5, 3], by decide⟩
def mulProgram := multiplyProgram mulPlace
def tail (t : ℕ) := BitMachineRawSequence.program
  (SourceClauseFixedUnary.program (3 : Fin 6) (14*t)) mulProgram
  MatrixAddressMachine.Label.outer () false
def program (t : ℕ) := BitMachineRawSequence.program
  (SourceClauseFixedUnary.program (1 : Fin 6) 5) (tail t)
  (BitMachineRawSequence.leftLabel (0 : SourceClauseFixedUnary.Label (14*t)))
  () ((), false)

def initial (b : ℕ) : Fin 6 → List Bool :=
  ![List.replicate b true, [], [], [], [], []]

def final (b t : ℕ) : Fin 6 → List Bool :=
  ![List.replicate b true, List.replicate 5 true,
    [], List.replicate (5*b+14*t) true, [], []]

def clock (b t : ℕ) : ℕ :=
  6 + (14*t+1) + MatrixAddressMachine.exactTime b 5 0 + 2

theorem run (b t : ℕ) :
    ∃ steps ≤ clock b t,
      ((advance (program t))^[steps])
        (⟨some (BitMachineRawSequence.leftLabel
            (0 : SourceClauseFixedUnary.Label 5)),
          ((), ((), false)), initial b⟩ :
          TM2.Cfg (fun _ : Fin 6 => Bool) _ _) =
        ⟨none, ((), ((), false)), final b t⟩ := by
  let S := initial b
  let S1 := Function.update S (1 : Fin 6) (List.replicate 5 true)
  let S2 := Function.update S1 (3 : Fin 6) (List.replicate (14*t) true)
  have h1 := SourceClauseFixedUnary.run (1 : Fin 6) S 5 (by rfl)
  have h1' : ((advance (SourceClauseFixedUnary.program (1 : Fin 6) 5))^[6])
      (⟨some (0 : SourceClauseFixedUnary.Label 5), (), S⟩ :
        TM2.Cfg (fun _ : Fin 6 => Bool) _ _) = ⟨none, (), S1⟩ := by
    simpa only [S1] using h1
  have h2 := SourceClauseFixedUnary.run (3 : Fin 6) S1 (14*t) (by rfl)
  have h2' : ((advance (SourceClauseFixedUnary.program (3 : Fin 6) (14*t)))^[14*t+1])
      (⟨some (0 : SourceClauseFixedUnary.Label (14*t)), (), S1⟩ :
        TM2.Cfg (fun _ : Fin 6 => Bool) _ _) = ⟨none, (), S2⟩ := by
    simpa only [S2] using h2
  have hm := MatrixStage4ScalarPreparationOps.multiply_run mulPlace S2 b 5
    (by simp [S2, S1, S, initial, mulPlace])
    (by simp [S2, S1, S, initial, mulPlace])
    (by simp [S2, S1, S, initial, mulPlace])
    (by simp [S2, S1, S, initial, mulPlace])
    (by simp [S2, S1, S, initial, mulPlace])
  have hf : Function.update S2 (3 : Fin 6)
      (List.replicate (b*5) true ++ S2 3) = final b t := by
    funext i
    fin_cases i <;> simp [S2, S1, S, initial, final, Nat.mul_comm, ← List.replicate_add]
  have hm' : ((advance mulProgram)^[MatrixAddressMachine.exactTime b 5 0])
      (⟨some MatrixAddressMachine.Label.outer, false, S2⟩ :
        TM2.Cfg (fun _ : Fin 6 => Bool) _ _) =
      ⟨none, false, final b t⟩ := by
    simpa [mulProgram, mulPlace, hf] using hm
  obtain ⟨u, hu, hr⟩ := BitMachineRawSequence.runs
    (SourceClauseFixedUnary.program (3 : Fin 6) (14*t)) mulProgram
    (0 : SourceClauseFixedUnary.Label (14*t)) MatrixAddressMachine.Label.outer
    () () false false S1 S2 (final b t) (14*t+1)
    (MatrixAddressMachine.exactTime b 5 0) h2' hm'
  obtain ⟨v, hv, hrun⟩ := BitMachineRawSequence.runs
    (SourceClauseFixedUnary.program (1 : Fin 6) 5) (tail t)
    (0 : SourceClauseFixedUnary.Label 5)
    (BitMachineRawSequence.leftLabel (0 : SourceClauseFixedUnary.Label (14*t)))
    () () ((), false) ((), false) S S1 (final b t) 6 u h1' hr
  exact ⟨v, by unfold clock; omega, by simpa [program, tail, S] using hrun⟩

theorem clock_linear (b t : ℕ) : clock b t ≤ 40 * (b + t + 1) := by
  simp [clock, MatrixAddressMachine.exactTime]
  omega

#print axioms run
#print axioms clock_linear
end CurrentAdditive.V38DegreePhysical
