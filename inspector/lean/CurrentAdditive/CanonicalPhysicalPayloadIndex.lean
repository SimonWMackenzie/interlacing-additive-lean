import CurrentAdditive.CanonicalPhysicalSelectorDigit
import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalTable

open Turing Paper2.YaoPositionFull
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

def payloadMulCells : Fin 4 ↪ Fin 6 := ⟨![0, 1, 2, 3], by decide⟩
def payloadAddCells : Fin 3 ↪ Fin 6 := ⟨![4, 2, 5], by decide⟩

/-- Fixed physical multiplication followed by a unary prepend-copy. -/
noncomputable def payloadIndexProgram :=
  BitMachineRawSequence.program (mulProgram payloadMulCells)
    (MatrixStage4ScalarPreparationOps.copyProgram payloadAddCells)
    BitMachineCopy.Label.scan false none

/-- From unary address `α`, slot `p`, and width `K+1`, produce their
row-major payload coordinate `α*(K+1)+p`. The width and address copies
are consumed; the slot is preserved. -/
theorem physical_payload_index (H K : ℕ)
    (α : Fin H) (p : Fin (K + 1)) (S : Fin 6 → List Bool)
    (hwidth : S 0 = List.replicate (K + 1) true)
    (haddr : S 1 = List.replicate α.val true)
    (hprod : S 2 = []) (hwork : S 3 = [])
    (hslot : S 4 = List.replicate p.val true)
    (hcopy : S 5 = []) :
    ∃ steps ≤ (α.val * (2 * (K + 1) + 3) + 1 + ((K + 1) + 1)) +
        (2 * p.val + 2) + 1,
      ((advance payloadIndexProgram)^[steps])
        (⟨some (BitMachineRawSequence.leftLabel MatrixUnaryArithmetic.Label.outer),
          (false, none), S⟩ : TM2.Cfg (fun _ : Fin 6 => Bool) _ _) =
      ⟨none, (false, none),
        Function.update
          (Function.update (Function.update S 0 []) 1 []) 2
          (List.replicate (α.val * (K + 1) + p.val) true)⟩ := by
  let S1 := Function.update (Function.update (Function.update S 0 []) 1 []) 2
    (List.replicate (α.val * (K + 1)) true)
  obtain ⟨t1, ht1, hr1⟩ := mul_run payloadMulCells S α.val (K + 1)
    (by simpa [payloadMulCells] using hwidth)
    (by simpa [payloadMulCells] using haddr)
    (by simpa [payloadMulCells] using hprod)
    (by simpa [payloadMulCells] using hwork)
  have hr1' : ((advance (mulProgram payloadMulCells))^[t1])
      (⟨some MatrixUnaryArithmetic.Label.outer, false, S⟩ :
        TM2.Cfg (fun _ : Fin 6 => Bool) _ _) =
      ⟨none, false, S1⟩ := by simpa only [S1, payloadMulCells] using hr1
  have hcopy1 : S1 (payloadAddCells 2) = [] := by
    simp [S1, payloadAddCells, hcopy]
  have hsource1 : S1 (payloadAddCells 0) = List.replicate p.val true := by
    simp [S1, payloadAddCells, hslot]
  have htarget1 : S1 (payloadAddCells 1) =
      List.replicate (α.val * (K + 1)) true := by
    simp [S1, payloadAddCells]
  have hr2 := MatrixStage4ScalarPreparationOps.copy_run payloadAddCells S1 hcopy1
  obtain ⟨steps, hsteps, hrun⟩ := BitMachineRawSequence.runs
    (mulProgram payloadMulCells)
    (MatrixStage4ScalarPreparationOps.copyProgram payloadAddCells)
    MatrixUnaryArithmetic.Label.outer BitMachineCopy.Label.scan
    false false none none S S1
    (Function.update S1 (payloadAddCells 1)
      (S1 (payloadAddCells 0) ++ S1 (payloadAddCells 1)))
    t1 (2 * (S1 (payloadAddCells 0)).length + 2) hr1' hr2
  refine ⟨steps, ?_, ?_⟩
  · simp only [hsource1, List.length_replicate] at hsteps
    omega
  · have hbank : Function.update S1 (payloadAddCells 1)
        (S1 (payloadAddCells 0) ++ S1 (payloadAddCells 1)) =
        Function.update (Function.update (Function.update S 0 []) 1 []) 2
          (List.replicate (α.val * (K + 1) + p.val) true) := by
      funext k
      fin_cases k <;>
        simp [S1, payloadAddCells, hslot,
          List.replicate_append_replicate, Nat.add_comm]
    simpa only [payloadIndexProgram, hbank] using hrun

#print axioms physical_payload_index

end CurrentAdditive.FiniteFieldConstructor.CanonicalTable
