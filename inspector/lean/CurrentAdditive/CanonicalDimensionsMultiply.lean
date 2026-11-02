import CurrentAdditive.CanonicalSelectorBankPower

/-! Three physical unary multiplications produce the canonical row and
column counts from prepared unary factors. The multiplication program
preserves factors and clears its scratch cells at each handoff. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalDimensionsMultiply

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

def rowPlace : Fin 6 ↪ Fin 11 := ⟨![0, 1, 8, 9, 10, 5], by decide⟩
def firstColPlace : Fin 6 ↪ Fin 11 := ⟨![4, 2, 8, 9, 10, 6], by decide⟩
def lastColPlace : Fin 6 ↪ Fin 11 := ⟨![6, 3, 8, 9, 10, 7], by decide⟩

def lastTwo := BitMachineRawSequence.program
  (MatrixStage4ScalarPreparationOps.multiplyProgram firstColPlace)
  (MatrixStage4ScalarPreparationOps.multiplyProgram lastColPlace)
  MatrixAddressMachine.Label.outer false false
def program := BitMachineRawSequence.program
  (MatrixStage4ScalarPreparationOps.multiplyProgram rowPlace)
  lastTwo (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)
  false (false, false)

def initial (v cap H R2 q : ℕ) : Fin 11 → List Bool :=
  (![List.replicate v true, List.replicate cap true,
      List.replicate H true, List.replicate R2 true,
      List.replicate q true, [], [], [], [], [], []] : Fin 11 → List Bool)

theorem physical_dimensions (v cap H R2 q : ℕ) :
    ∃ steps ≤ MatrixAddressMachine.exactTime v cap 0 +
        MatrixAddressMachine.exactTime q H 0 +
        MatrixAddressMachine.exactTime (q * H) R2 0 + 2,
      ((advance program)^[steps])
        (⟨some (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer),
          (false, (false, false)), initial v cap H R2 q⟩ :
          TM2.Cfg (fun _ : Fin 11 => Bool) _ _) =
        ⟨none, (false, (false, false)),
          Function.update
            (Function.update
              (Function.update (initial v cap H R2 q) 5
                (List.replicate (v * cap) true)) 6
              (List.replicate (q * H) true)) 7
            (List.replicate (q * H * R2) true)⟩ := by
  let S := initial v cap H R2 q
  let S1 := Function.update S 5 (List.replicate (v*cap) true)
  let S2 := Function.update S1 6 (List.replicate (q*H) true)
  let S3 := Function.update S2 7 (List.replicate (q*H*R2) true)
  have h1 := MatrixStage4ScalarPreparationOps.multiply_run rowPlace S v cap
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  have h1' : ((advance (MatrixStage4ScalarPreparationOps.multiplyProgram rowPlace))^[
      MatrixAddressMachine.exactTime v cap 0])
      (⟨some MatrixAddressMachine.Label.outer, false, S⟩ :
        TM2.Cfg (fun _ : Fin 11 => Bool) _ _) = ⟨none, false, S1⟩ := by
    simpa [rowPlace, S, S1, initial] using h1
  have h2 := MatrixStage4ScalarPreparationOps.multiply_run firstColPlace S1 q H
    (by simp [S1, S, initial, firstColPlace])
    (by simp [S1, S, initial, firstColPlace])
    (by simp [S1, S, initial, firstColPlace])
    (by simp [S1, S, initial, firstColPlace])
    (by simp [S1, S, initial, firstColPlace])
  have h2' : ((advance (MatrixStage4ScalarPreparationOps.multiplyProgram firstColPlace))^[
      MatrixAddressMachine.exactTime q H 0])
      (⟨some MatrixAddressMachine.Label.outer, false, S1⟩ :
        TM2.Cfg (fun _ : Fin 11 => Bool) _ _) = ⟨none, false, S2⟩ := by
    simpa [firstColPlace, S2, S1, S, initial] using h2
  have h3 := MatrixStage4ScalarPreparationOps.multiply_run lastColPlace S2 (q*H) R2
    (by simp [S2, S1, S, initial, lastColPlace])
    (by simp [S2, S1, S, initial, lastColPlace])
    (by simp [S2, S1, S, initial, lastColPlace])
    (by simp [S2, S1, S, initial, lastColPlace])
    (by simp [S2, S1, S, initial, lastColPlace])
  have h3' : ((advance (MatrixStage4ScalarPreparationOps.multiplyProgram lastColPlace))^[
      MatrixAddressMachine.exactTime (q*H) R2 0])
      (⟨some MatrixAddressMachine.Label.outer, false, S2⟩ :
        TM2.Cfg (fun _ : Fin 11 => Bool) _ _) = ⟨none, false, S3⟩ := by
    simpa [lastColPlace, S3, S2, S1, S, initial] using h3
  obtain ⟨u, hu, hlast⟩ := BitMachineRawSequence.runs
    (MatrixStage4ScalarPreparationOps.multiplyProgram firstColPlace)
    (MatrixStage4ScalarPreparationOps.multiplyProgram lastColPlace)
    MatrixAddressMachine.Label.outer MatrixAddressMachine.Label.outer
    false false false false S1 S2 S3
    (MatrixAddressMachine.exactTime q H 0)
    (MatrixAddressMachine.exactTime (q*H) R2 0) h2' h3'
  obtain ⟨steps, hsteps, hrun⟩ := BitMachineRawSequence.runs
    (MatrixStage4ScalarPreparationOps.multiplyProgram rowPlace) lastTwo
    MatrixAddressMachine.Label.outer
    (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)
    false false (false, false) (false, false) S S1 S3
    (MatrixAddressMachine.exactTime v cap 0) u h1' hlast
  exact ⟨steps, by omega, by simpa [program, S3, S2, S1, S] using hrun⟩

#print axioms physical_dimensions

end CurrentAdditive.FiniteFieldConstructor.CanonicalDimensionsMultiply
