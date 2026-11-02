import CurrentAdditive.CanonicalPhysicalPosition

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalTable

open Turing Paper2.YaoIndexDecoder
open CurrentAdditive.SmallBias
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

def strideCells : Fin 6 ↪ Fin 11 := ⟨![0, 1, 2, 3, 4, 5], by decide⟩
def digitCells : Fin 6 ↪ Fin 11 := ⟨![4, 6, 7, 8, 9, 10], by decide⟩

/-- A fixed two-division TM2 program. Its first divisor is the supplied
unary stride `H^g`; its second divisor is the supplied unary base `H`. -/
noncomputable def selectorDigitProgram :=
  BitMachineRawSequence.program (divProgram strideCells)
    (divProgram digitCells) MatrixUnaryDivision.Label.start false false

/-- A physical base-`H` selector digit, provided its unary stride and base
have been prepared. The original row label is consumed; the selected digit
is left in cell 8. Preparing `H^g` and restoring the bank remain separate. -/
theorem physical_selector_digit (q H : ℕ)
    (z : Fin (H ^ q)) (g : Fin q) (S : Fin 11 → List Bool)
    (h0 : S 0 = List.replicate z.val true)
    (h1 : S 1 = List.replicate (H ^ g.val) true)
    (h6 : S 6 = List.replicate H true)
    (hempty : ∀ k : Fin 11, k ≠ 0 → k ≠ 1 → k ≠ 6 → S k = []) :
    ∃ steps ≤ (8 * z.val + 3 * (H ^ g.val) + 4) +
        (8 * (z.val / H ^ g.val) + 3 * H + 4) + 1,
      ((advance selectorDigitProgram)^[steps])
        (⟨some (BitMachineRawSequence.leftLabel MatrixUnaryDivision.Label.start),
          (false, false), S⟩ : TM2.Cfg (fun _ : Fin 11 => Bool) _ _) =
      ⟨none, (false, false),
        Function.update (Function.update (Function.update
          (Function.update (Function.update (Function.update S 0 [])
            3 (List.replicate (z.val % H ^ g.val) true))
            4 (List.replicate (z.val / H ^ g.val) true))
            4 [])
            8 (List.replicate (selector q H z g).val true))
            9 (List.replicate ((z.val / H ^ g.val) / H) true)⟩ := by
  let S1 := Function.update (Function.update (Function.update S 0 [])
    3 (List.replicate (z.val % H ^ g.val) true))
    4 (List.replicate (z.val / H ^ g.val) true)
  obtain ⟨t1, ht1, hr1⟩ := div_run strideCells S z.val (H ^ g.val)
    (by simpa [strideCells] using h0)
    (by simpa [strideCells] using h1)
    (by simp [strideCells, hempty 2 (by decide) (by decide) (by decide)])
    (by simp [strideCells, hempty 3 (by decide) (by decide) (by decide)])
    (by simp [strideCells, hempty 4 (by decide) (by decide) (by decide)])
    (by simp [strideCells, hempty 5 (by decide) (by decide) (by decide)])
  have hr1' : ((advance (divProgram strideCells))^[t1])
      (⟨some MatrixUnaryDivision.Label.start, false, S⟩ :
        TM2.Cfg (fun _ : Fin 11 => Bool) _ _) =
      ⟨none, false, S1⟩ := by simpa only [S1, strideCells] using hr1
  obtain ⟨t2, ht2, hr2⟩ := div_run digitCells S1
    (z.val / H ^ g.val) H
    (by simp [S1, digitCells])
    (by simpa [S1, digitCells] using h6)
    (by simp [S1, digitCells, hempty 7 (by decide) (by decide) (by decide)])
    (by simp [S1, digitCells, hempty 8 (by decide) (by decide) (by decide)])
    (by simp [S1, digitCells, hempty 9 (by decide) (by decide) (by decide)])
    (by simp [S1, digitCells, hempty 10 (by decide) (by decide) (by decide)])
  obtain ⟨steps, hsteps, hrun⟩ := BitMachineRawSequence.runs
    (divProgram strideCells) (divProgram digitCells)
    MatrixUnaryDivision.Label.start MatrixUnaryDivision.Label.start
    false false false false S S1
    (Function.update (Function.update (Function.update S1 (digitCells 0) [])
      (digitCells 3) (List.replicate ((z.val / H ^ g.val) % H) true))
      (digitCells 4) (List.replicate ((z.val / H ^ g.val) / H) true))
    t1 t2 hr1' hr2
  refine ⟨steps, by omega, ?_⟩
  simpa only [selectorDigitProgram, S1, strideCells, digitCells,
    selector_digit_numeric] using hrun

#print axioms physical_selector_digit

end CurrentAdditive.FiniteFieldConstructor.CanonicalTable
